import StructuralBertrand.Defs
import StructuralBertrand.LPF
import StructuralBertrand.ZeroForce
import StructuralBertrand.Weight
import StructuralBertrand.GPS_StateMachine
import StructuralBertrand.Main
import StructuralBertrand.Truncated
import StructuralBertrand.SelfContained
import StructuralBertrand.Rings
import StructuralBertrand.Newton
import StructuralBertrand.Threshold
import StructuralBertrand.BinomialBound
import StructuralBertrand.BinomialCertificate
import StructuralBertrand.Certificate
/-!
# StructuralBertrand — Structural Reduction of Bertrand's Postulate

Formalization in Lean 4 / Mathlib4.
Author: Artur Flamandzki

Based on: "A Structural Reduction of Bertrand's Postulate"

## Status

**Fully verified — zero `sorry`.** The whole chain from Definition 2.1 to
`bertrand_chebyshev` is machine-checked. Mathlib's Bertrand
(`Nat.bertrand`/`exists_prime_lt_and_le_two_mul`) is **never used**, and the main
theorem's import closure does **not** contain `Mathlib.NumberTheory.Bertrand`: the
atom is closed by the self-contained `binomial_contradiction`. That Mathlib file is
imported only in `Erdos.lean` (instance A, off the main path — see README).

## Strategy

The structural scaffold is verified with no analytic machinery: divisibility/gcd
algebra, totient multiplicativity, induction over the prime base, linear/nonlinear
arithmetic (`omega`, `nlinarith`), and finite-set cardinality (union bound).
The starting observation is the **determinism boundary**: the reach of a complete
base `{2, …, P_max}` is deterministic exactly up to `2·P_max`
(`window_composite_smooth` / `window_self_contained`), and provably breaks above it
(`determinism_breaks_above`). The postulate collapses to a single quantitative atom
— *the sieve never covers its own window* — closed by the self-contained argument on
the central binomial coefficient (`binomial_contradiction`, `BinomialCertificate.lean`): the
prime content of `C(2n,n)` in the window is governed by the S1 purity law
(`window_primes_prod_dvd_centralBinom`), its growth by the Pascal row
(`four_pow_le_newton`), the empty-window upper bound reproved in-project
(`window_centralBinom_le`, from Legendre/Kummer + primorial), and a prime-free size
threshold (`threshold_inequality`); a computational oracle handles `n < 512`.

### Key constraint (Definition 2.1)
The prime base `𝒫` must be a *complete generative segment*: it contains every prime
between `P_min` and `P_max` without exception.  Omitting one prime breaks the identity
φ(M)/M = ∏(1−1/p) and invalidates the multiplicative structure.

### Chain
1. **LPF** (`LPF.lean`): every composite n ∈ (P_max, P_min·P_max] has n.minFac ≤ P_max,
   so uncovered elements must be prime.  [verified]

2. **Zero Effective Force** (`ZeroForce.lean`): P_k's only multiple in (P_k, 2·P_k] is
   2·P_k, already covered by 2 ∈ 𝒫'.  Composites in the window ↔ covered by 𝒫'.  [verified]

3. **Structural Weight** (`Weight.lean`): w(𝒫) = P_k·φ(M)/M ≥ 1, by induction; preceding
   base satisfies M' < P_k·φ(M').  This is the *average* survivor density — a necessary
   condition, **not** by itself a guarantee for a specific window.  [verified]

4. **Self-containment** (`SelfContained.lean`): the window width ≤ P_max (multiplier = the
   minimal prime) is the maximal self-contained width — the structural reason for the
   constant.  [verified]

5. **Ring collective** (`Rings.lean`): void ⟺ prime dichotomy, determinism boundary,
   small-anchor closures P_k ≤ 83 by a sufficient gap bound on the active-covering rings
   (not the object's own gap), the disjoint minFac telescope, the Legendre interference
   identity, and the S1 bridge to `C(2n,n)`. [verified]

6. **Central Positivity** (`BinomialBound.lean`, `Threshold.lean`,
   `BinomialCertificate.lean`, `Newton.lean`, `GPS_StateMachine.lean`):
   `binomial_contradiction` closed self-containedly — computational oracle for 2 < n < 512,
   the two bounds on `C(2n,n)` for n ≥ 512 (no Bertrand import); `dense_sieve_survivor` follows,
   since a prime in the window is automatically free. Modularity is a theorem
   (`Certificate.lean`), with `erdos_certificate` as a second, Mathlib-based instance. [verified]

7. **Reduction** (`Main.lean`): `structural_bertrand_chebyshev` and `bertrand_chebyshev`.
   [verified]

## File structure

| File | Content | Status |
|------|---------|--------|
| `Defs.lean`            | Complete generative base, sieve coverage, window (Def. 2.1) | verified |
| `LPF.lean`             | Least Prime Factor; uncovered ⇒ prime (Lemma 3.1) | verified |
| `ZeroForce.lean`       | Zero Effective Force; composites covered by 𝒫' (Lemma 4.1) | verified |
| `Weight.lean`          | Structural weight w ≥ 1; M' < P·φ(M') (Lemma 4.3) | verified |
| `SelfContained.lean`   | Self-containment fixes the window width (why the constant) | verified |
| `Truncated.lean`       | Sparse-regime positivity by union bound | verified |
| `Rings.lean`           | Ring collective, regimes, telescope, interference identity, S1 bridge | verified |
| `Newton.lean`          | Central binomial coefficient and the window's prime content | verified |
| `BinomialBound.lean`   | Upper bound `window_centralBinom_le` from primitives (no Bertrand import) | verified |
| `Threshold.lean`       | Prime-free size inequality `threshold_inequality` (convexity) | verified |
| `BinomialCertificate.lean` | Self-contained kernel `binomial_contradiction` | verified |
| `GPS_StateMachine.lean`| Generative window; regime dispatch; `prime_in_window` | verified |
| `Certificate.lean`     | Modular `WindowCertificate`; instances erdos_/binomial_certificate | verified |
| `Erdos.lean`           | Instance A (off main path): `erdos_contradiction` via Mathlib | verified |
| `Main.lean`            | Theorem 5.1 + `bertrand_chebyshev` | verified |
-/
