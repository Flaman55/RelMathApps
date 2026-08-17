"""
goldbach_window.py -- structural window check for Goldbach's conjecture, for the
Badania -> Goldbach sub-tab. Pure Python, no external dependencies (same zero-install
promise as primality.py -- see that module's own header comment).

Mirrors, term for term, Artur's own formalization in
"A Structural Sieve for Goldbach's Conjecture" (LaTeX) and
Hipoteza Goldbacha/lean/StructuralGoldbach/{Basic,Structural}.lean:

  hasGoldbachRep(n)   := exists p q, p prime, q prime, p + q = n            (Basic.lean)
  repCount(n)         := #{p in [0, n] : p prime and (n - p) prime}        (Basic.lean)
  windowCovered(Pmax) := for every even n, 4 <= n <= 2*Pmax, hasGoldbachRep(n)
                                                                             (Structural.lean)
  windowCoveredDec(Pmax) := for every even n < 2*Pmax + 1, not(4<=n and repCount(n)=0)
                                                                             (Structural.lean)

repCount ranges its witness p over ALL of [0, n] (Lean's `range (n+1)`), so it counts
ORDERED witnesses -- both p=3,q=7 and p=7,q=3 add 1 each to repCount(10) (repCount(10)=3:
p in {3,5,7}). check_window()'s "all_combinations" mode reports that same number under
"rep_count" (exactly reproducing the Lean definition), and ALSO derives the deduplicated
UNORDERED pair list (p <= q) under "pairs", since that's the more natural thing for a
person to read -- the two are never in conflict, "pairs" is just "rep_count" grouped by
{p, q} instead of listed once per p.

Two selectable modes (the checkbox in the GUI), both checking exactly the same window
[4, 2*Pmax] and reporting exactly the same "covered" verdict on that window as a whole --
they differ only in how much they compute PER n, in line with the paper's own framing
(Constructive.lean's header comment): "windowCovered doesn't count how many primes are
in the window, it shows the window must geometrically deliver one" vs
"repCount/PositiveMargin are the counting-spirit road, which runs into the parity
problem".

  "touch_once"       -- for each n, stop at the FIRST witness found (smallest p).
                         This is windowCovered / hasGoldbachRep: existence, not count.
                         The paper's ACTIVE line of proof.
  "all_combinations" -- for each n, compute repCount(n) in full (every p in [0, n]).
                         This is the paper's repCount/PositiveMargin framing, explicitly
                         flagged there as kept "for comparison, not the active line of
                         proof" (it inherits the parity problem in full force).

Because every n checked here satisfies n <= 2*Pmax, any witness pair p <= q must have
p <= Pmax (p is the smaller summand, so 2p <= p+q = n <= 2*Pmax). This means
"touch_once"'s witness search never needs a candidate above Pmax -- it is simultaneously
a live check of buildableFromBase(Pmax, n) (Constructive.lean) for every n in the window,
not just of the unbounded hasGoldbachRep -- the two framings coincide exactly on this
window, which is itself a small confirmation that the translation below is faithful to
the source.

The GUI's number field is labeled "n" (an arbitrary integer), not "Pmax" -- Pmax is
DERIVED as the largest prime <= n (see largest_prime_le()), matching the paper's own
convention that Pmax must itself be a genuine prime, without requiring the person to
type a prime by hand.
"""
import time


def sieve_is_prime(limit):
    """Classic sieve of Eratosthenes. Returns a bytearray `is_prime` of length
    limit + 1, is_prime[i] truthy iff i is prime (0 and 1 are not). O(limit
    log log limit) time, O(limit) memory -- fine for the window sizes this tab is meant
    for (a GUI research tool, not the production floor-sieve -- see
    primeatlas_offset_optimization_ceiling.md in memory for why depth belongs to the
    primesieve-backed engine, not here)."""
    if limit < 2:
        return bytearray(max(limit + 1, 0))
    is_prime = bytearray([1]) * (limit + 1)
    is_prime[0] = 0
    is_prime[1] = 0
    p = 2
    while p * p <= limit:
        if is_prime[p]:
            span = len(range(p * p, limit + 1, p))
            is_prime[p * p:: p] = bytearray(span)
        p += 1
    return is_prime


def largest_prime_le(is_prime, n):
    """Largest prime <= n, or None if none exists (n < 2) -- how the GUI derives Pmax
    from the user-facing "n" field: Pmax := the largest prime <= n, matching the paper's
    own convention that Pmax must itself be a genuine prime, without requiring the
    person to type a prime by hand. Dual of next_anchor() below (that one searches
    upward for the next prime; this one searches downward for the one at-or-below n).
    `is_prime` must be long enough to index up to n."""
    for candidate in range(min(n, len(is_prime) - 1), 1, -1):
        if is_prime[candidate]:
            return candidate
    return None


def _smallest_witness(is_prime, n):
    """Smallest prime p with p <= n//2 and n-p also prime, or (None, None) if no such p
    exists. The single witness-search primitive shared by check_window()'s "touch_once"
    branch and window_rows() below, so both really do run "the exact same algorithm",
    not just similarly-shaped code."""
    for p in range(2, n // 2 + 1):
        if is_prime[p] and is_prime[n - p]:
            return p, n - p
    return None, None


def window_rows(is_prime, Pmax, row_cap=None, row_offset=0):
    """Computes windowCovered(Pmax) (Structural.lean) -- every even n in [4, 2*Pmax] --
    using an EXTERNALLY supplied is_prime array (e.g. sourced from on-disk storage, see
    prime_atlas_v1.read_is_prime_from_storage) instead of building a fresh sieve. Runs
    the exact same touch_once witness search as check_window()'s touch_once branch
    (_smallest_witness), just against a caller-supplied is_prime instead of one built
    internally -- this is the Goldbach tab's Wizualizacja feature, per Artur's
    instruction that "wizualizacja zawsze siedzi w oknie 4-2Pmax" (the visualization
    always lives inside the [4, 2*Pmax] window -- the SAME window "Sprawdz okno"
    checks, not a separate cascade step). `is_prime` must be long enough to index up to
    2*Pmax.

    `row_cap` limits how many per-n rows are returned (for GUI display); `row_offset`
    skips that many n's (in window order) before collection starts -- together these
    are a simple offset/limit page window, letting the GUI page through the full
    window's decomposition rows (Artur: chciał nawigacji jak gdzie indziej przy dużej
    ilości danych) without ever materializing more than one page's worth of row dicts
    at a time. The coverage verdict and counterexample list are ALWAYS computed over
    the FULL window regardless of row_cap/row_offset -- pagination only affects which
    slice of already-computed witnesses gets packaged into "rows".

    Returns {"pmax":, "window_max":, "old_base_primes": [...], "covered":,
    "counterexamples": [...], "segment_size": int, "row_offset": int,
    "rows": [{"n":,"p":,"q":,"q_is_new": bool}, ...], "rows_truncated": bool} --
    "old_base_primes" is every prime <= Pmax (the frozen base every p is drawn from,
    automatically -- see the module docstring's note on p <= Pmax); "q_is_new" flags
    q > Pmax (a prime that was NOT part of that base and so wasn't strictly needed to
    find p, mirroring the Wizualizacja diagram's "old base vs new" framing);
    "rows_truncated" means there are more rows AFTER this page (row_offset + len(rows)
    < segment_size), i.e. whether a "next page" would return anything."""
    if Pmax < 2:
        raise ValueError("Pmax must be >= 2")
    window_max = 2 * Pmax
    old_base_primes = [p for p in range(2, Pmax + 1) if is_prime[p]]
    rows = []
    counterexamples = []
    segment_size = 0
    for n in range(4, window_max + 1, 2):
        idx = segment_size  # 0-based position of n within the window, before increment
        segment_size += 1
        p_found, q_found = _smallest_witness(is_prime, n)
        if p_found is None:
            counterexamples.append(n)
        if idx >= row_offset and (row_cap is None or len(rows) < row_cap):
            rows.append({
                "n": n, "p": p_found, "q": q_found,
                "q_is_new": (q_found is not None and q_found > Pmax),
            })
    return {
        "pmax": Pmax, "window_max": window_max, "old_base_primes": old_base_primes,
        "covered": not counterexamples, "counterexamples": counterexamples,
        "segment_size": segment_size, "row_offset": row_offset, "rows": rows,
        "rows_truncated": (row_cap is not None and row_offset + len(rows) < segment_size),
    }


def check_window(Pmax, mode):
    """Checks windowCovered(Pmax): every even n with 4 <= n <= 2*Pmax must be a sum of
    two primes. `mode` is "touch_once" or "all_combinations" (see module docstring).

    Returns a dict:
      {"pmax": Pmax, "window_max": 2*Pmax, "mode": mode, "covered": bool,
       "n_checked": int, "counterexamples": [n, ...], "elapsed": float,
       "rows": [{"n": n, "p": p or None, "q": q or None, "rep_count": int or None,
                 "pairs": [(p, q), ...] or None}, ...]}

    rows is one entry per even n in [4, 2*Pmax], in ascending order. In "touch_once"
    mode, rep_count/pairs are left None (not computed -- that is the whole point of
    the mode) and p/q hold the first witness found (or None, None for a counterexample).
    In "all_combinations" mode, p/q hold the SMALLEST witness pair for convenience
    (same value "touch_once" would have found), rep_count holds the exact Lean
    repCount(n), and pairs holds the deduplicated (p <= q) witness list.

    Raises ValueError if Pmax < 2 (windowCovered's own window [4, 2*Pmax] is empty/
    degenerate below that -- mirrors anchor 0 = 2, the paper's own base case)."""
    if Pmax < 2:
        raise ValueError("Pmax must be >= 2")
    if mode not in ("touch_once", "all_combinations"):
        raise ValueError(f"unknown mode: {mode!r}")

    t0 = time.perf_counter()
    window_max = 2 * Pmax
    is_prime = sieve_is_prime(window_max)

    rows = []
    counterexamples = []
    for n in range(4, window_max + 1, 2):
        if mode == "touch_once":
            p_found, q_found = _smallest_witness(is_prime, n)
            if p_found is None:
                counterexamples.append(n)
            rows.append({"n": n, "p": p_found, "q": q_found,
                         "rep_count": None, "pairs": None})
        else:
            rep_count = 0
            pairs = []
            for p in range(0, n + 1):
                if is_prime[p] and is_prime[n - p]:
                    rep_count += 1
                    if p <= n - p:
                        pairs.append((p, n - p))
            if rep_count == 0:
                counterexamples.append(n)
            p0, q0 = (pairs[0] if pairs else (None, None))
            rows.append({"n": n, "p": p0, "q": q0,
                         "rep_count": rep_count, "pairs": pairs})

    elapsed = time.perf_counter() - t0
    return {
        "pmax": Pmax, "window_max": window_max, "mode": mode,
        "covered": not counterexamples,
        "n_checked": len(rows), "counterexamples": counterexamples,
        "elapsed": elapsed, "rows": rows,
    }


# ------------------------------------------------------------------------------------------
# Cascade step -- Constructive.lean's nextAnchor / anchor / top / CascadeOldBaseSufficiency.
# A separate, stronger claim from windowCovered above (base held fixed from the PREVIOUS
# cascade step, rather than re-derived as Pmax for the whole window) -- not currently wired
# into any GUI control (the Wizualizacja button uses window_rows() instead, to stay strictly
# inside [4, 2*Pmax] per Artur's instruction), but kept here since it's a distinct, verified,
# potentially useful piece of the formalization for a future dedicated cascade view.
# ------------------------------------------------------------------------------------------

def next_anchor(is_prime, Pmax):
    """Largest prime in (Pmax, 2*Pmax], or 2*Pmax if none -- mirrors Constructive.lean's
    nextAnchor exactly. `is_prime` must be long enough to index up to 2*Pmax (Bertrand's
    postulate guarantees a prime is always found in this range for Pmax >= 1, so the
    "none" fallback is a formality that should never actually trigger)."""
    hi = 2 * Pmax
    for candidate in range(hi, Pmax, -1):
        if is_prime[candidate]:
            return candidate
    return hi


def cascade_step(is_prime, anchor_k, row_cap=None):
    """One cascade step starting at anchor(k) = anchor_k: computes top(k) = 2*anchor_k,
    the next anchor (largest prime in (anchor_k, 2*anchor_k]), top(k+1) = 2*next_anchor,
    and -- for every new even n in the segment (top(k), top(k+1)] -- the smallest prime
    p <= top(k) (the OLD, frozen base) with n-p also prime (buildableFromBase(top(k), n),
    Constructive.lean). `is_prime` must be long enough to index up to top(k+1) -- since
    top(k+1) <= 4*anchor_k always (next_anchor <= 2*anchor_k), the caller should ensure
    `is_prime` covers at least that.

    `row_cap` limits how many per-n rows are returned (for GUI display) -- the coverage
    verdict and counterexample list are still computed over the FULL segment regardless,
    never just the truncated display slice.

    Returns {"anchor_k":, "top_k":, "next_anchor":, "top_k1":, "old_base_primes": [...],
    "segment_size": int, "rows": [{"n":,"p":,"q":,"q_is_new": bool}, ...],
    "rows_truncated": bool, "counterexamples": [...], "covered": bool}."""
    if anchor_k < 1:
        raise ValueError("anchor_k must be >= 1")
    top_k = 2 * anchor_k
    nxt = next_anchor(is_prime, anchor_k)
    top_k1 = 2 * nxt
    old_base_primes = [p for p in range(2, top_k + 1) if is_prime[p]]

    rows = []
    counterexamples = []
    segment_size = 0
    for n in range(top_k + 2, top_k1 + 1, 2):
        segment_size += 1
        p_found = q_found = None
        for p in old_base_primes:
            if p > n // 2:
                break
            if is_prime[n - p]:
                p_found, q_found = p, n - p
                break
        if p_found is None:
            counterexamples.append(n)
        if row_cap is None or len(rows) < row_cap:
            rows.append({
                "n": n, "p": p_found, "q": q_found,
                "q_is_new": (q_found is not None and q_found > top_k),
            })

    return {
        "anchor_k": anchor_k, "top_k": top_k, "next_anchor": nxt, "top_k1": top_k1,
        "old_base_primes": old_base_primes, "segment_size": segment_size,
        "rows": rows, "rows_truncated": (row_cap is not None and segment_size > row_cap),
        "counterexamples": counterexamples, "covered": not counterexamples,
    }
