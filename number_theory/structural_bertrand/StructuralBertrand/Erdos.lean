import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-!
# Erdos.lean — instance A of the quantitative certificate (via Mathlib)

A closed proof of the quantitative kernel, using Mathlib's two inequalities on `C(2n,n)`. It
is retained as instance A for the modularity comparison in `Certificate.lean`; the main theorem
uses the self-contained `binomial_contradiction` instead. Outline:

  · large windows (`n ≥ 512`): the two bounds on `C(2n,n)` are combined — the lower bound
    `4^n < n · C(2n,n)` (`Nat.four_pow_lt_mul_centralBinom`) and the upper bound from the old
    sources (`centralBinom_le_of_no_bertrand_prime`, a consequence of the S1 purity law: a new
    source `q ∈ (n,2n]` divides `C(2n,n)` exactly once, so its absence leaves only factors
    `≤ 2n/3` and `≤ √(2n)`); the comparison `bertrand_main_inequality` then yields
    `4^n < 4^n`, a contradiction;
  · small windows (`2 < n < 512`): a computational oracle (`native_decide`), the deterministic
    sieve evaluated inside the proof.

**Non-circularity.** This file imports `Mathlib.NumberTheory.Bertrand` solely for the two
inequalities on `C(2n,n)` and powers. It does not use `Nat.bertrand` or
`Nat.exists_prime_lt_and_le_two_mul`; the non-circularity audit is a grep over *uses*, not
over imports:
`grep -n "Nat.bertrand[^_]\|exists_prime_lt" StructuralBertrand/*.lean`.

Context (Rings.lean/Newton.lean): the prime content of `C(2n,n)` in the window is governed by
the S1 purity law (`window_primes_prod_dvd_centralBinom`); the lower bound
`4^n ≤ (2n+1)·C(2n,n)` has a purely combinatorial proof (`four_pow_le_newton`).
-/

namespace StructuralBertrand

/-- **Small windows (`2 < n < 512`):** a prime in `(n, 2n]` by a computational oracle — the
    sieve evaluated inside the proof, with no external lemma. -/
lemma small_window_prime :
    ∀ n < 512, 2 < n → ∃ p < 1024, n < p ∧ p ≤ 2 * n ∧ Nat.Prime p := by
  native_decide

/--
**Quantitative kernel (instance A) — closed.** The absence of a prime in `(n, 2n]` leads to a
contradiction: the lower and upper bounds on `C(2n,n)` are then incompatible.
-/
theorem erdos_contradiction {n : ℕ} (hn3 : 2 < n)
    (h_no_prime : ∀ q, n < q → q ≤ 2 * n → ¬ Nat.Prime q) : False := by
  rcases Nat.lt_or_ge n 512 with hsmall | hbig
  · -- small windows: witness from the oracle
    obtain ⟨p, _, hlo, hhi, hp⟩ := small_window_prime n hsmall hn3
    exact h_no_prime p hlo hhi hp
  · -- large windows: combine the two bounds on C(2n,n)
    have no_prime : ¬∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
      rintro ⟨p, hp, h1, h2⟩
      exact h_no_prime p h1 h2 hp
    have hub := _root_.centralBinom_le_of_no_bertrand_prime n hn3 no_prime
    have hmain := _root_.bertrand_main_inequality hbig
    have hlb := Nat.four_pow_lt_mul_centralBinom n (by omega)
    have hchain : (4 : ℕ) ^ n < 4 ^ n :=
      calc (4 : ℕ) ^ n < n * Nat.centralBinom n := hlb
        _ ≤ n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) :=
            Nat.mul_le_mul_left n hub
        _ = n * (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by ring
        _ ≤ 4 ^ n := hmain
    exact absurd hchain (lt_irrefl _)

end StructuralBertrand
