import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-!
# BinomialBound.lean — the self-contained empty-window upper bound

This file reproves the Erdős-type upper bound on the central binomial coefficient *within our
own development*, importing only the Legendre/Kummer factorization primitives
(`Mathlib.Data.Nat.Choose.Factorization`) and the primorial bound
(`Mathlib.NumberTheory.Primorial`). It does NOT import `Mathlib.NumberTheory.Bertrand`; the
Erdős-specific content — the partition of the prime factors of `C(2n,n)` into ranges — is
carried here, not borrowed.

The five ranges of prime factors (`v_p` denotes the `p`-adic valuation of `C(2n,n)`):
1. `p ≤ √(2n)`: `v_p ≥ 1` possible, but `p^{v_p} ≤ 2n` (Legendre threshold);
2. `√(2n) < p ≤ 2n/3`: `v_p ≤ 1`, product `≤ ∏ p ≤ 4^{2n/3}` (primorial bound);
3. `2n/3 < p ≤ n`: `v_p = 0`;
4. `n < p ≤ 2n`: `v_p ≤ 1`, absent when the window contains no prime;
5. `p > 2n`: `v_p = 0`.

The proof structure follows Mathlib's `centralBinom_le_of_no_bertrand_prime`, but is placed in
our namespace and depends only on the primitives above, so the development remains free of
Mathlib's Bertrand theorem.
-/

open Finset Nat

namespace StructuralBertrand

/-- **Empty window ⇒ all prime factors are `≤ 2n/3`.** If `(n, 2n]` contains no prime, then
    every prime factor of `C(2n,n)` is `≤ 2n/3` (ranges 1–2 only): range 3 has valuation `0`,
    and ranges 4–5 are empty. -/
theorem window_centralBinom_factorization_small (n : ℕ) (n_large : 2 < n)
    (no_prime : ¬∃ p : ℕ, p.Prime ∧ n < p ∧ p ≤ 2 * n) :
    centralBinom n = ∏ p ∈ Finset.range (2 * n / 3 + 1), p ^ (centralBinom n).factorization p := by
  refine (Eq.trans ?_ n.prod_pow_factorization_centralBinom).symm
  apply Finset.prod_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  intro x hx h2x
  rw [Finset.mem_range, Nat.lt_succ_iff] at hx h2x
  rw [not_le, div_lt_iff_lt_mul three_pos, mul_comm x] at h2x
  replace no_prime := not_exists.mp no_prime x
  rw [← and_assoc, not_and', not_and_or, not_lt] at no_prime
  cases' no_prime hx with h h
  · rw [factorization_eq_zero_of_not_prime n.centralBinom h, Nat.pow_zero]
  · rw [factorization_centralBinom_of_two_mul_self_lt_three_mul n_large h h2x, Nat.pow_zero]

/-- **Empty-window upper bound (self-contained).** If `(n, 2n]` has no prime, then
    `C(2n,n) ≤ (2n)^{√(2n)} · 4^{2n/3}`. Range 1 contributes `≤ (2n)^{√(2n)}`, range 2
    contributes `≤ 4^{2n/3}` (primorial), ranges 3–5 contribute a factor `1`. Reproved from
    Legendre/Kummer + primorial primitives; independent of Mathlib's Bertrand. -/
theorem window_centralBinom_le (n : ℕ) (n_large : 2 < n)
    (no_prime : ¬∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n) :
    centralBinom n ≤ (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n_pos : 0 < n := (Nat.zero_le _).trans_lt n_large
  have n2_pos : 1 ≤ 2 * n := mul_pos (zero_lt_two' ℕ) n_pos
  let S := (Finset.range (2 * n / 3 + 1)).filter Nat.Prime
  let f x := x ^ n.centralBinom.factorization x
  have hS : ∏ x ∈ S, f x = ∏ x ∈ Finset.range (2 * n / 3 + 1), f x := by
    refine Finset.prod_filter_of_ne fun p _ h => ?_
    contrapose! h; dsimp only [f]
    rw [factorization_eq_zero_of_not_prime n.centralBinom h, _root_.pow_zero]
  rw [window_centralBinom_factorization_small n n_large no_prime, ← hS, ←
    Finset.prod_filter_mul_prod_filter_not S (· ≤ sqrt (2 * n))]
  apply mul_le_mul'
  · refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos n_pos)
    have hcard : (Finset.Icc 1 (sqrt (2 * n))).card = sqrt (2 * n) := by
      rw [card_Icc, Nat.add_sub_cancel]
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans hcard.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · refine le_trans ?_ (primorial_le_4_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

end StructuralBertrand
