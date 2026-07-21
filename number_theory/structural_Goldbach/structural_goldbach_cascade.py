"""
Structural additive sieve for Goldbach's conjecture: windowed-cascade verification.

Companion numerical tool to the Lean 4 formalization `StructuralGoldbach` and the
accompanying paper "A Structural Sieve for Goldbach's Conjecture" (Flamandzki, 2026).

Analogy with the multiplicative sieve for Bertrand's postulate:

  * Bertrand (multiplicative): a VOID is a number that cannot be built from the base
    by a MULTIPLE -- equivalently, a prime.
  * Goldbach (additive):       a VOID is an even number that cannot be built from the
    base by a SUM of two primes -- a Goldbach counterexample, were one ever found.

Windowed-cascade theory (as formalized in `Constructive.lean` / `Structural.lean`):

  * Anchor Pmax. The deterministic window (Pmax, 2*Pmax] supplies NEW primes: inside
    it, every survivor of the base is provably prime (`void_isPrime`, since the
    generative decision reaches up to Pmax**2, and 2*Pmax < Pmax**2).
  * Coverage of sums lives on the interval of even numbers [2*Pmin, 2*Pmax]
    (Pmin = 2, so 2*Pmin = 4).
  * Additive self-containment: no additive void in the new window segment.
  * Existential margin r(n), the number of representations of n as p + q, must stay
    strictly positive for every even n.

Scope note. This script implements the classical COUNTING oracle: r(n) is computed
once via an FFT self-convolution of the prime indicator function, and the cascade
loop below reports, window by window, the new primes supplied, any additive voids,
and the minimal margin observed. This is the numerical evidence behind the
Hardy-Littlewood floor conjecture `HL_Floor` recorded in `Bridge.lean`. It is *not*
the active line of the Lean proof: the formalization moves from counting
representations to asking what is CONSTRUCTIBLE from an already-certified base
(`buildableFromBase`, `CascadeOldBaseSufficiency`), because counting inherits the
sieve-theoretic parity problem (see the paper, Section 8), while constructibility
does not. This script remains useful as an independent numerical check and as the
historical origin of that reframing.
"""
import math
import numpy as np


def sieve_of_eratosthenes(limit):
    """Boolean sieve: `is_prime[n]` is truthy iff `n` is prime, for `0 <= n <= limit`."""
    is_prime = bytearray([1]) * (limit + 1)
    is_prime[0] = is_prime[1] = 0
    for i in range(2, math.isqrt(limit) + 1):
        if is_prime[i]:
            is_prime[i * i: limit + 1: i] = bytearray(len(range(i * i, limit + 1, i)))
    return is_prime


def goldbach_representation_counts(limit, is_prime=None):
    """r[n] = number of ORDERED prime pairs (p, q) with p + q = n, for 0 <= n <= limit.

    Computed with a single FFT self-convolution of the prime indicator function --
    O(limit log limit), rather than an O(limit) trial-division count at every n.
    """
    if is_prime is None:
        is_prime = sieve_of_eratosthenes(limit)
    indicator = np.frombuffer(bytes(is_prime), dtype=np.uint8).astype(np.float64)
    length = 1
    while length < 2 * limit + 1:
        length *= 2
    spectrum = np.fft.rfft(indicator, n=length)
    return np.rint(np.fft.irfft(spectrum * spectrum, n=length)[:limit + 1]).astype(np.int64)


def windowed_cascade(limit, p_start=5):
    """
    Windowed cascade (structural framework). Iterates anchors `Pmax -> 2*Pmax`:

      * window `(Pmax, 2*Pmax]` -> new primes (deterministically prime, since
        `2*Pmax < Pmax**2`, matching `void_isPrime`);
      * segment of new even numbers `(prev_top, 2*Pmax]`, covered by a sum of two
        primes;
      * report: new primes supplied, additive voids, minimal margin `r(n)` in the
        segment.

    Returns a list with one dict per window.
    """
    is_prime = sieve_of_eratosthenes(limit)
    r = goldbach_representation_counts(limit, is_prime)

    p_min = 2
    p_max = p_start
    prev_top = 2                       # so the first segment starts at 2 * p_min = 4
    windows = []
    while 2 * p_max <= limit:
        top = 2 * p_max
        new_primes = [n for n in range(p_max + 1, top + 1) if is_prime[n]]

        segment_lo = prev_top + 2                     # first new even number
        if segment_lo % 2:
            segment_lo += 1
        voids = []
        min_margin, n_at_min = None, None
        for n in range(segment_lo, top + 1, 2):
            count = int(r[n])
            if count == 0:
                voids.append(n)
            if min_margin is None or count < min_margin:
                min_margin, n_at_min = count, n

        windows.append({
            "p_max": p_max, "top": top, "new_primes": len(new_primes),
            "segment": (segment_lo, top), "voids": voids,
            "min_margin": min_margin, "n_at_min": n_at_min,
        })
        prev_top = top
        p_max = new_primes[-1] if new_primes else top   # new anchor = largest prime in the window
    return windows


if __name__ == "__main__":
    N = 10 ** 6
    print("STRUCTURAL ADDITIVE SIEVE -- WINDOWED CASCADE (GOLDBACH)")
    print("=" * 96)
    print(f"{'anchor Pmax':>14} | {'window (Pmax,2Pmax]':>22} | {'new primes':>10} | "
          f"{'even segment':>22} | {'voids':>6} | {'min r(n)':>10}")
    print("-" * 96)
    windows = windowed_cascade(N)
    for w in windows[:6] + windows[-3:]:
        a, b = w["segment"]
        print(f"{w['p_max']:>14,} | {'(' + format(w['p_max'], ',') + ', ' + format(w['top'], ',') + ']':>22} | "
              f"{w['new_primes']:>10,} | {'[' + format(a, ',') + ', ' + format(b, ',') + ']':>22} | "
              f"{len(w['voids']):>6} | {w['min_margin']:>10,}")
    print("-" * 96)
    total_voids = sum(len(w["voids"]) for w in windows)
    global_min = min(w["min_margin"] for w in windows)
    print(f"Windows: {len(windows)}   |   total additive voids: {total_voids}   "
          f"(self-containment {'holds' if total_voids == 0 else 'FAILS'})")
    print(f"Smallest margin r(n) observed across all windows: {global_min}")
    print("=" * 96)
    print("Every window is covered without gaps -> additive self-containment on this finite range.")
    print("Conjectural target (classical, counting form): the margin r(n) never touches zero as")
    print("Pmax -> infinity -- see `PositiveMargin` / `HL_Floor` in `Bridge.lean`. The active line")
    print("of the Lean development replaces this with a constructibility question instead; see")
    print("`Constructive.lean` and the accompanying paper.")
