"""
ktuple_sieve_v1.py -- targeted k-tuple ("constellation") candidate sieve, complementary
to constellation_finder_v1.py.

WHY THIS EXISTS: constellation_finder_v1.py finds k-tuples by pattern-matching against
windows that prime_sieve_v1/prime_sieve_primesieve.py have ALREADY fully sieved (every
prime in the window, via primesieve). That's the right tool when you already want every
prime in a range for other reasons, but it's the wrong tool for hunting a single sparse
pattern deep in a wide floor: a k=15 pattern's singular-series density at floor ~25 is on
the order of 1e-21..1e-22 per integer, so fully sieving a range wide enough to have a
realistic chance of a hit (~1e20-1e21 wide) would take a FULL prime sieve engine
centuries even at this app's own measured floor-25 throughput -- the bottleneck isn't the
per-window sieve cost (that's genuinely cheap, ~0.18s/1e7-window even at floor 25), it's
that there are simply too many windows to visit at all.

This module instead builds a small explicit residue WHEEL (via CRT over a handful of
small primes) for the pattern's own offsets: for each wheel prime p, at least one of the
k members is FORCED divisible by p for most residues of the window's starting position n
mod p (since k=15's offsets already span most residues mod any small p -- see
build_wheel()'s own docstring), so the overwhelming majority of positions can be
DIRECTLY SKIPPED (via striding by the wheel modulus) rather than ever touched. What
survives the wheel is filtered further by incremental trial division (early-exit) against
deeper primes, and only the tiny remainder -- individual integers, not whole windows --
gets real primality-tested (Miller-Rabin; numbers in play here are a few dozen to ~100
bits, trivially cheap to test individually regardless of how many survive).

This is deterministic and exact at every stage before the final Miller-Rabin call: a
position is only ever ELIMINATED because one of its k members is PROVABLY divisible by a
small prime (hence composite, barring the trivial n+d==p edge case, guarded for
explicitly) -- so no true k-tuple is ever silently skipped by the wheel or trial-division
stages. Only the final Miller-Rabin step is probabilistic (standard rounds=40 default,
error probability < 4**-40), same trust level the rest of this app already uses
elsewhere (see primeatlas/primality.py's own miller_rabin_test, which this deliberately
mirrors in miniature -- duplicated rather than imported since this script runs standalone
inside WSL, same self-contained pattern as constellation_finder_v1.py/prime_sieve_v1.py,
with no dependency on the primeatlas/ Windows-side package).

Because this mode never needs a pre-existing PRIME_WINDOW_*.bin for the locations it
scans (it works directly off raw integer ranges), it's independent of prime_sieve's own
generation pipeline and CHECKPOINT.txt -- confirmed hits are written into the SAME
per-(k,variant) hit-file format constellation_finder_v1.py uses (via that module's own
hit_file_path()/_append_hits_deduped()), so the rest of the portal (browsing, search)
needs no changes at all to pick these up.
"""
import math
import random


# ------------------------------------------------------------------------------------------
# Miller-Rabin -- minimal standalone copy of primeatlas/primality.py's own
# miller_rabin_test(), trimmed to just the True/False verdict (no certainty label needed
# here). See this module's own docstring for why it's duplicated rather than imported.
# ------------------------------------------------------------------------------------------

_MR_DETERMINISTIC_WITNESSES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]
_MR_DETERMINISTIC_LIMIT = 3317044064679887385961981  # ~3.3e24 -- see primality.py


def _miller_rabin_round(n, a, d, r):
    x = pow(a, d, n)
    if x == 1 or x == n - 1:
        return True
    for _ in range(r - 1):
        x = pow(x, 2, n)
        if x == n - 1:
            return True
    return False


def is_probable_prime(n, rounds=40):
    if n < 2:
        return False
    for p in _MR_DETERMINISTIC_WITNESSES:
        if n == p:
            return True
        if n % p == 0:
            return False
    d = n - 1
    r = 0
    while d % 2 == 0:
        d //= 2
        r += 1
    if n < _MR_DETERMINISTIC_LIMIT:
        for a in _MR_DETERMINISTIC_WITNESSES:
            if a >= n:
                continue
            if not _miller_rabin_round(n, a, d, r):
                return False
        return True
    for _ in range(rounds):
        a = random.randrange(2, n - 1)
        if not _miller_rabin_round(n, a, d, r):
            return False
    return True


# ------------------------------------------------------------------------------------------
# Small prime generation (pure Python sieve -- deep_prime_limit is at most a few million,
# instant either way, no external dependency needed).
# ------------------------------------------------------------------------------------------

def primes_upto(limit):
    """Simple sieve of Eratosthenes, ascending list of primes <= limit."""
    if limit < 2:
        return []
    sieve = bytearray([1]) * (limit + 1)
    sieve[0] = sieve[1] = 0
    for p in range(2, math.isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p::p] = bytearray(len(sieve[p * p::p]))
    return [i for i, is_p in enumerate(sieve) if is_p]


# ------------------------------------------------------------------------------------------
# Wheel construction (CRT over a handful of small primes).
# ------------------------------------------------------------------------------------------

def _crt_pair(r1, m1, r2, m2):
    """x == r1 (mod m1), x == r2 (mod m2), 0 <= x < m1*m2 -- m1, m2 coprime."""
    m1_inv = pow(m1, -1, m2)
    return (r1 + m1 * ((r2 - r1) * m1_inv % m2)) % (m1 * m2)


def build_wheel(offsets, wheel_primes):
    """For each wheel prime p, a residue r (mod p) is BAD if some offset d makes
    (r + d) % p == 0 -- i.e. starting at n === r (mod p) forces member n+d divisible by
    p. Since k=15-style patterns already span most residues mod small p (their offsets
    are spread across [0, 56] -- for p > 56 every offset is automatically distinct mod
    p, and even for p <= 56 most are), only a small fraction of residues mod p survive.
    Combining survivors across several small primes via CRT compounds this fast (e.g.
    for k15 variant 4: mod 2 alone already halves the space, mod 2*3*5*7*11*13=30030
    leaves ~1 in 30030). Returns (M, sorted_surviving_residues)."""
    M = 1
    residues = [0]
    for p in wheel_primes:
        bad = set((-d) % p for d in offsets)
        good_mod_p = [r for r in range(p) if r not in bad]
        new_residues = [_crt_pair(r, M, gp, p) for r in residues for gp in good_mod_p]
        residues = new_residues
        M *= p
    residues.sort()
    return M, residues


def default_wheel_primes(offsets, max_M=100_000):
    """Greedily picks small primes (2, 3, 5, 7, ...) to include in the explicit wheel,
    stopping just before the combined modulus M would exceed max_M -- keeps the
    surviving-residue table (len(residues), used to stride every window) small enough
    to build/iterate cheaply, while still capturing most of the wheel's benefit (see
    build_wheel()'s own docstring -- returns diminish fast past the first several
    primes, per Mertens' theorem)."""
    chosen = []
    M = 1
    for p in primes_upto(97):
        if M * p > max_M:
            break
        chosen.append(p)
        M *= p
    return chosen


# ------------------------------------------------------------------------------------------
# Per-window candidate extraction.
# ------------------------------------------------------------------------------------------

def _survives_trial_division(n, offsets, deep_primes):
    for p in deep_primes:
        r = n % p
        for d in offsets:
            if (r + d) % p == 0 and n + d != p:  # n+d==p guard: trivial, never hit at the
                return False                      # magnitudes this module targets, kept
                                                    # for correctness at any scale anyway
    return True


def scan_window_for_candidates(base, window_m, offsets, wheel_M, wheel_residues, deep_primes):
    """Scans [base, base+window_m) for positions n surviving both the wheel and the
    deep-prime trial-division filter. Returns a list of surviving n (still need real
    primality verification of all k members -- see verify_candidates())."""
    candidates = []
    for r in wheel_residues:
        n = base + ((r - base) % wheel_M)
        while n < base + window_m:
            if _survives_trial_division(n, offsets, deep_primes):
                candidates.append(n)
            n += wheel_M
    candidates.sort()
    return candidates


def verify_candidates(candidates, offsets, rounds=40):
    """Real primality verification of survivors -- returns the sorted subset of
    `candidates` for which EVERY member (n+d for d in offsets) is prime."""
    hits = []
    for n in candidates:
        if all(is_probable_prime(n + d, rounds=rounds) for d in offsets):
            hits.append(n)
    return hits


# ------------------------------------------------------------------------------------------
# Hardy-Littlewood density -- used only to size a SUGGESTED fragment for the
# "concentrated" location strategy (select_locations() below); never affects
# correctness of the sieve itself, only how wide a slice is worth searching for a
# reasonable chance of a hit.
# ------------------------------------------------------------------------------------------

def singular_series_constant(offsets, k, limit=200_000):
    """C_k for this specific pattern: product over primes p of
    (1 - w(p)/p) / (1 - 1/p)**k, where w(p) = number of distinct residues the offsets
    occupy mod p. Converges quickly (grows/shrinks by ever-smaller factors past the
    first few hundred primes) -- limit=200_000 is already good to ~4-5 significant
    figures for k=15-sized patterns; raise it for more precision at real compute cost
    (primes_upto() is O(limit), one-off, cheap even at limit=2_000_000)."""
    log_c = 0.0
    for p in primes_upto(limit):
        w = len(set(o % p for o in offsets))
        if w >= p:
            return 0.0  # inadmissible pattern -- every residue mod p is bad
        log_c += math.log((1 - w / p) / (1 - 1 / p) ** k)
    return math.exp(log_c)


def recommended_fragment_width(offsets, k, floor_exponent, target_expected=1.0, limit=200_000):
    """Width W (as an int) such that the Hardy-Littlewood expected count of this
    pattern with its base in a W-wide slice near 10**floor_exponent is approximately
    target_expected. Uses ln(10**floor_exponent) as a single representative log(x) --
    good enough for sizing a search fragment (not a precision research estimate) since
    ln(x) barely moves across even a couple of orders of magnitude at these depths."""
    C_k = singular_series_constant(offsets, k, limit=limit)
    if C_k <= 0:
        raise ValueError("pattern is inadmissible (or C_k underflowed to 0) -- cannot size a fragment")
    ln_x = floor_exponent * math.log(10)
    density = C_k / ln_x ** k
    return max(1, round(target_expected / density))


# ------------------------------------------------------------------------------------------
# Location selection -- WHERE to put the (up to) window_m-wide windows this run will
# scan, as offsets from the floor's own start (10**base_exponent). Always returns
# ABSOLUTE base positions (10**base_exponent + offset), sorted ascending.
# ------------------------------------------------------------------------------------------

def select_locations(base_exponent, n_locations, window_m, strategy="even",
                      offsets=None, k=None, fragment_width=None, fragment_start=0,
                      manual_offsets=None, target_expected=1.0, hl_limit=200_000):
    """strategy:
      "even"        -- n_locations windows spread evenly across the WHOLE floor
                        (10**base_exponent .. 10**(base_exponent+1)) -- broad, sparse
                        coverage, appropriate for casting a wide net over a floor with
                        no fragment picked out yet.
      "concentrated" -- n_locations windows spread evenly across a single, narrower
                        fragment. `fragment_width` may be given explicitly, or left
                        None to auto-size it via recommended_fragment_width() (needs
                        `offsets` + `k`) so the fragment's own Hardy-Littlewood expected
                        hit count is ~target_expected. `fragment_start` is an offset
                        from the floor's own start (default 0 -- the floor's youngest
                        edge, closest to any already-known record for this pattern).
      "manual"      -- uses `manual_offsets` (ints, offsets from the floor's own start)
                        directly, one window per entry -- n_locations is ignored.
    Returns a sorted list of absolute base positions (Python big ints)."""
    floor_base = 10 ** base_exponent
    floor_width = 9 * floor_base

    if strategy == "manual":
        if not manual_offsets:
            raise ValueError("strategy='manual' requires a non-empty manual_offsets list")
        return sorted(floor_base + off for off in manual_offsets)

    if strategy == "even":
        if n_locations < 1:
            raise ValueError("n_locations must be >= 1")
        step = floor_width // n_locations
        if step < window_m:
            raise ValueError(
                f"n_locations={n_locations} windows of width {window_m:,} would overlap "
                f"across the floor's width ({floor_width:.3e}) -- reduce n_locations or "
                f"window_m, or switch to strategy='concentrated'")
        return [floor_base + i * step for i in range(n_locations)]

    if strategy == "concentrated":
        if fragment_width is None:
            if offsets is None or k is None:
                raise ValueError("strategy='concentrated' needs fragment_width, or both "
                                  "offsets and k to auto-size one")
            fragment_width = recommended_fragment_width(
                offsets, k, base_exponent, target_expected=target_expected, limit=hl_limit)
        if n_locations < 1:
            raise ValueError("n_locations must be >= 1")
        step = max(window_m, fragment_width // n_locations)
        return [floor_base + fragment_start + i * step for i in range(n_locations)]

    raise ValueError(f"unknown strategy {strategy!r} -- expected 'even', 'concentrated', or 'manual'")


# ------------------------------------------------------------------------------------------
# Top-level driver -- scans a list of locations for one catalog pattern, writing
# confirmed hits into the SAME per-(k,variant) hit-file format constellation_finder_v1.py
# uses, via that module's own storage functions (imported below, same sys.path pattern
# constellation_finder_v1.py itself uses for prime_sieve_v1).
# ------------------------------------------------------------------------------------------

import os  # noqa: E402
_SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))
import sys  # noqa: E402
sys.path.insert(0, _SCRIPT_DIR)  # constellation_finder_v1.py, pattern_catalog_v1.py (same folder)
from constellation_finder_v1 import _append_hits_deduped  # noqa: E402
from pattern_catalog_v1 import PATTERN_CATALOG  # noqa: E402


def scan_locations(base_exponent, pattern, locations, window_m,
                    wheel_primes=None, deep_prime_limit=2000, mr_rounds=40,
                    progress_cb=None, should_stop=None):
    """Scans each of `locations` (absolute base positions, each a window_m-wide range)
    for pattern's k-tuple, writing confirmed hits into the pattern's own cumulative hit
    file (constellation_finder_v1.hit_file_path/_append_hits_deduped -- same format and
    same dedup-safety the sequential finder uses, so this is safe to re-run over
    overlapping/previously-scanned locations without risk of duplicate or crashed
    writes).

    `pattern` -- one entry from PATTERN_CATALOG (dict with "k", "id", "offsets").
    `progress_cb(index, total, location, candidates_found, confirmed_count)` -- called
    after each location finishes.
    `should_stop()` -- checked before each location; returns
    {"locations_done": n, "cancelled": bool, "total_candidates": n, "total_confirmed": n}.

    Note: unlike constellation_finder_v1.process_floor(), this never touches
    CHECKPOINT.txt -- these locations aren't tied to pre-existing PRIME_WINDOW_*.bin
    files at all (see this module's own docstring), so there is no sequential
    "last processed window" concept here to track."""
    offsets = pattern["offsets"]
    k = pattern["k"]
    variant_id = pattern["id"]

    if wheel_primes is None:
        wheel_primes = default_wheel_primes(offsets)
    wheel_M, wheel_residues = build_wheel(offsets, wheel_primes)
    deep_primes = [p for p in primes_upto(deep_prime_limit) if p not in wheel_primes]

    total_candidates = 0
    total_confirmed = 0
    locations_done = 0
    cancelled = False

    for i, base in enumerate(locations):
        if should_stop is not None and should_stop():
            cancelled = True
            break
        candidates = scan_window_for_candidates(
            base, window_m, offsets, wheel_M, wheel_residues, deep_primes)
        confirmed = verify_candidates(candidates, offsets, rounds=mr_rounds)
        if confirmed:
            _append_hits_deduped(base_exponent, k, variant_id, sorted(confirmed))
        total_candidates += len(candidates)
        total_confirmed += len(confirmed)
        locations_done += 1
        if progress_cb is not None:
            progress_cb(i, len(locations), base, len(candidates), len(confirmed))

    return {"locations_done": locations_done, "cancelled": cancelled,
            "total_candidates": total_candidates, "total_confirmed": total_confirmed}


if __name__ == "__main__":
    import argparse
    parser = argparse.ArgumentParser(
        description="Targeted k-tuple candidate sieve (wheel + trial division + Miller-Rabin) "
                    "for a single catalog pattern over a set of scattered window locations.")
    parser.add_argument("base_exponent", type=int, help="floor N (searches near 10**N)")
    parser.add_argument("k", type=int, help="pattern k (e.g. 15)")
    parser.add_argument("variant_id", type=int, help="pattern variant id within k (see pattern_catalog_v1.py)")
    parser.add_argument("--n-locations", type=int, default=1000)
    parser.add_argument("--window-m", type=int, default=10_000_000)
    parser.add_argument("--strategy", choices=["even", "concentrated", "manual"], default="concentrated")
    parser.add_argument("--fragment-width", type=int, default=None)
    parser.add_argument("--fragment-start", type=int, default=0)
    parser.add_argument("--manual-offsets", type=int, nargs="*", default=None)
    parser.add_argument("--deep-prime-limit", type=int, default=2000)
    parser.add_argument("--mr-rounds", type=int, default=40)
    args = parser.parse_args()

    pattern = next((w for w in PATTERN_CATALOG if w["k"] == args.k and w["id"] == args.variant_id), None)
    if pattern is None:
        print(f"[!] No pattern k={args.k} id={args.variant_id} in PATTERN_CATALOG.")
        sys.exit(1)

    locations = select_locations(
        args.base_exponent, args.n_locations, args.window_m, strategy=args.strategy,
        offsets=pattern["offsets"], k=pattern["k"],
        fragment_width=args.fragment_width, fragment_start=args.fragment_start,
        manual_offsets=args.manual_offsets)

    print(f"[KTUPLE SIEVE v1] 10^{args.base_exponent} pattern k={args.k} v={args.variant_id} "
          f"({pattern['discoverer']}, {pattern['date']}) -- {len(locations)} location(s), "
          f"window_m={args.window_m:,}, strategy={args.strategy}")

    def progress(i, total, base, n_cand, n_conf):
        extra = f" -- {n_conf} CONFIRMED HIT(S)!" if n_conf else ""
        print(f"[KTUPLE SIEVE v1] {i+1}/{total}: base={base} candidates={n_cand}{extra}")

    result = scan_locations(args.base_exponent, pattern, locations, args.window_m,
                             deep_prime_limit=args.deep_prime_limit, mr_rounds=args.mr_rounds,
                             progress_cb=progress)
    print(f"\n[KTUPLE SIEVE v1] Done. locations_done={result['locations_done']} "
          f"total_candidates={result['total_candidates']} "
          f"total_confirmed={result['total_confirmed']}")
