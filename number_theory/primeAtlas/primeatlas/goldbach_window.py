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
            p_found = q_found = None
            for p in range(2, n // 2 + 1):
                if is_prime[p] and is_prime[n - p]:
                    p_found, q_found = p, n - p
                    break
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
# This is the "less fuel" framing (see the Wizualizacja diagram in the Goldbach tab): a
# FROZEN base of primes <= top(k) = 2*anchor(k) must supply the smaller summand p for
# every new even n in the segment (top(k), top(k+1)], with no credit for any prime that
# first appears inside that very segment. Separate from check_window() above -- windowCovered
# re-derives base=Pmax fresh for the WHOLE window [4, 2*Pmax] every time, while this checks
# ONE cascade step with the base held fixed from the step before, which is the stronger,
# harder-to-satisfy claim the paper's actual constructive proof line rests on.
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
