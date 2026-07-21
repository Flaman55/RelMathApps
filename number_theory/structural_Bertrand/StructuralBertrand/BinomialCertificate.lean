import StructuralBertrand.BinomialBound
import StructuralBertrand.Threshold
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# BinomialCertificate.lean — the self-contained binomial contradiction

`binomial_contradiction` closes the quantitative atom entirely within our own development:
for `2 < n`, an empty window `(n, 2n]` is impossible. It imports only

* `BinomialBound` — the upper bound `window_centralBinom_le`, reproved from Legendre/Kummer +
  primorial primitives (the Erdős-specific content, ours);
* `Threshold` — the prime-free size inequality `threshold_inequality`;
* `Mathlib.Data.Nat.Choose.Central` — the lower bound `four_pow_lt_mul_centralBinom`
  (`4^n < n · C(2n,n)`) and the definition of `centralBinom`.

Crucially it does NOT import `Mathlib.NumberTheory.Bertrand`: the closure is assembled from
the two bounds on `C(2n,n)` plus a computational oracle for the small cases, none of which is
Mathlib's Bertrand theorem. Plugs into `WindowCertificate` as instance B.
-/

open Nat

namespace StructuralBertrand

/-- **Small windows (`2 < n < 512`).** A prime in `(n, 2n]` by a compiled sieve — a local
    oracle, no external lemma. (Same statement as `Erdos.small_window_prime`, redefined here so
    this file stays free of the Bertrand import.) -/
lemma small_window_oracle :
    ∀ n < 512, 2 < n → ∃ p < 1024, n < p ∧ p ≤ 2 * n ∧ Nat.Prime p := by
  native_decide

/-- **Self-contained quantitative kernel.** For `2 < n`, if `(n, 2n]` has no prime then a
    contradiction follows: the lower bound `4^n < n · C(2n,n)` and the empty-window upper bound
    `window_centralBinom_le` on the same integer `C(2n,n)` are incompatible. Built without
    Mathlib's Bertrand theorem. -/
theorem binomial_contradiction {n : ℕ} (hn3 : 2 < n)
    (h_no_prime : ∀ q, n < q → q ≤ 2 * n → ¬ Nat.Prime q) : False := by
  rcases Nat.lt_or_ge n 512 with hsmall | hbig
  · -- small windows: witness from the oracle
    obtain ⟨p, _, hlo, hhi, hp⟩ := small_window_oracle n hsmall hn3
    exact h_no_prime p hlo hhi hp
  · -- large windows: combine the two bounds on C(2n,n)
    have no_prime : ¬∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
      rintro ⟨p, hp, h1, h2⟩
      exact h_no_prime p h1 h2 hp
    have hub := window_centralBinom_le n hn3 no_prime
    have hmain := threshold_inequality hbig
    have hlb := Nat.four_pow_lt_mul_centralBinom n (by omega)
    have hchain : (4 : ℕ) ^ n < 4 ^ n :=
      calc (4 : ℕ) ^ n < n * Nat.centralBinom n := hlb
        _ ≤ n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) :=
            Nat.mul_le_mul_left n hub
        _ = n * (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by ring
        _ ≤ 4 ^ n := hmain
    exact absurd hchain (lt_irrefl _)

end StructuralBertrand
