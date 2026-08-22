import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Tactic
import Mathlib.Tactic.NormNum.Prime

/-!
# Threshold.lean — the generic size inequality (prime-free)

The large-`n` contradiction in the binomial certificate needs the inequality
`n · (2n)^√(2n) · 4^(2n/3) ≤ 4^n` for `n ≥ 512`. This is a *prime-free* analytic size bound —
it contains no primes and is not part of the Erdős argument; it merely says a certain function
is dominated by `4^n`. Its proof uses real convexity.

To keep the development free of `Mathlib.NumberTheory.Bertrand`, we place the proof here,
importing only `Mathlib.Analysis.Convex.SpecificFunctions.*`. The proof is adapted verbatim
from Mathlib's `Bertrand.real_main_inequality` / `bertrand_main_inequality`
(Apache-2.0, authors Patrick Stevens and Bolton Bailey); nothing prime-theoretic is used.
-/

namespace StructuralBertrand

section Real
open Real

/-- Real form of the threshold inequality (adapted from Mathlib's `Bertrand.real_main_inequality`,
    Apache-2.0, P. Stevens & B. Bailey). Prime-free. -/
theorem real_threshold_inequality {x : ℝ} (x_large : (512 : ℝ) ≤ x) :
    x * (2 * x) ^ √(2 * x) * 4 ^ (2 * x / 3) ≤ 4 ^ x := by
  let f : ℝ → ℝ := fun x => log x + √(2 * x) * log (2 * x) - log 4 / 3 * x
  have hf' : ∀ x, 0 < x → 0 < x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3) := fun x h =>
    div_pos (mul_pos h (rpow_pos_of_pos (mul_pos two_pos h) _)) (rpow_pos_of_pos four_pos _)
  have hf : ∀ x, 0 < x → f x = log (x * (2 * x) ^ √(2 * x) / 4 ^ (x / 3)) := by
    intro x h5
    have h6 := mul_pos (zero_lt_two' ℝ) h5
    have h7 := rpow_pos_of_pos h6 (√(2 * x))
    rw [log_div (mul_pos h5 h7).ne' (rpow_pos_of_pos four_pos _).ne', log_mul h5.ne' h7.ne',
      log_rpow h6, log_rpow zero_lt_four, ← mul_div_right_comm, ← mul_div, mul_comm x]
  have h5 : 0 < x := lt_of_lt_of_le (by norm_num1) x_large
  rw [← div_le_one (rpow_pos_of_pos four_pos x), ← div_div_eq_mul_div, ← rpow_sub four_pos, ←
    mul_div 2 x, mul_div_left_comm, ← mul_one_sub, (by norm_num1 : (1 : ℝ) - 2 / 3 = 1 / 3),
    mul_one_div, ← log_nonpos_iff (hf' x h5).le, ← hf x h5]
  have h : ConcaveOn ℝ (Set.Ioi 0.5) f := by
    apply ConcaveOn.sub
    · apply ConcaveOn.add
      · exact strictConcaveOn_log_Ioi.concaveOn.subset
          (Set.Ioi_subset_Ioi (by norm_num)) (convex_Ioi 0.5)
      convert ((strictConcaveOn_sqrt_mul_log_Ioi.concaveOn.comp_linearMap
        ((2 : ℝ) • LinearMap.id))) using 1
      ext x
      simp only [Set.mem_Ioi, Set.mem_preimage, LinearMap.smul_apply,
        LinearMap.id_coe, id_eq, smul_eq_mul]
      rw [← mul_lt_mul_iff_of_pos_left (two_pos)]
      norm_num1
      rfl
    apply ConvexOn.smul
    · refine div_nonneg (log_nonneg (by norm_num1)) (by norm_num1)
    · exact convexOn_id (convex_Ioi (0.5 : ℝ))
  suffices ∃ x1 x2, 0.5 < x1 ∧ x1 < x2 ∧ x2 ≤ x ∧ 0 ≤ f x1 ∧ f x2 ≤ 0 by
    obtain ⟨x1, x2, h1, h2, h0, h3, h4⟩ := this
    exact (h.right_le_of_le_left'' h1 ((h1.trans h2).trans_le h0) h2 h0 (h4.trans h3)).trans h4
  refine ⟨18, 512, by norm_num1, by norm_num1, x_large, ?_, ?_⟩
  · have : √(2 * 18 : ℝ) = 6 := (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonneg_iff (by positivity), this, one_le_div (by norm_num1)]
    norm_num1
  · have : √(2 * 512) = 32 :=
      (sqrt_eq_iff_mul_self_eq_of_pos (by norm_num1)).mpr (by norm_num1)
    rw [hf _ (by norm_num1), log_nonpos_iff (hf' _ (by norm_num1)).le, this,
        div_le_one (by positivity)]
    conv in 512 => equals 2 ^ 9 => norm_num1
    conv in 2 * 512 => equals 2 ^ 10 => norm_num1
    conv in 32 => rw [← Nat.cast_ofNat]
    rw [rpow_natCast, ← pow_mul, ← pow_add]
    conv in 4 => equals 2 ^ (2 : ℝ) => rw [rpow_two]; norm_num1
    rw [← rpow_mul, ← rpow_natCast]
    on_goal 1 => apply rpow_le_rpow_of_exponent_le
    all_goals norm_num1

end Real

section Nat
open Nat

/-- **The threshold inequality (prime-free), in ℕ.** For `n ≥ 512`,
    `n · (2n)^√(2n) · 4^(2n/3) ≤ 4^n`. Adapted from Mathlib's `bertrand_main_inequality`
    (Apache-2.0), placed here to avoid importing `Mathlib.NumberTheory.Bertrand`. -/
theorem threshold_inequality {n : ℕ} (n_large : 512 ≤ n) :
    n * (2 * n) ^ sqrt (2 * n) * 4 ^ (2 * n / 3) ≤ 4 ^ n := by
  -- Rebuilt (Mathlib bump to v4.28.0): the old `gcongr`-with-bullets proof relied on a goal
  -- order/count that changed upstream. This version proves the two exponent-cast bridges
  -- (`Nat`-pow vs `Real.rpow`) explicitly instead of leaning on `gcongr`'s auto-splitting.
  have hn1 : (1 : ℝ) ≤ (2 * n : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * n)
  have h4 : (1 : ℝ) ≤ (4 : ℝ) := by norm_num1
  have hexp1 : ((sqrt (2 * n) : ℕ) : ℝ) ≤ Real.sqrt (2 * n : ℝ) := by
    exact_mod_cast Real.nat_sqrt_le_real_sqrt
  have hexp2 : ((2 * n / 3 : ℕ) : ℝ) ≤ (2 * n : ℝ) / 3 := by
    exact_mod_cast Nat.cast_div_le
  have hpow1 : (2 * n : ℝ) ^ (sqrt (2 * n)) ≤ (2 * n : ℝ) ^ Real.sqrt (2 * n : ℝ) := by
    rw [← Real.rpow_natCast (2 * n : ℝ) (sqrt (2 * n))]
    exact Real.rpow_le_rpow_of_exponent_le hn1 hexp1
  have hpow2 : (4 : ℝ) ^ (2 * n / 3) ≤ (4 : ℝ) ^ ((2 * n : ℝ) / 3) := by
    rw [← Real.rpow_natCast (4 : ℝ) (2 * n / 3)]
    exact Real.rpow_le_rpow_of_exponent_le h4 hexp2
  rw [← @Nat.cast_le ℝ]
  push_cast
  calc (n : ℝ) * (2 * n : ℝ) ^ sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3)
      ≤ (n : ℝ) * (2 * n : ℝ) ^ Real.sqrt (2 * n : ℝ) * (4 : ℝ) ^ ((2 * n : ℝ) / 3) := by
        gcongr <;> first | exact hpow1 | exact hpow2
    _ ≤ (4 : ℝ) ^ (n : ℝ) := real_threshold_inequality (by exact_mod_cast n_large)
    _ = (4 : ℝ) ^ n := by rw [Real.rpow_natCast]

end Nat

end StructuralBertrand
