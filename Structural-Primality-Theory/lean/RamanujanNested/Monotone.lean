import RamanujanNested.Defs

/-!
# Monotone.lean — Section 4.1, monotonicity of the truncated sequence

"the truncated values R_1^(N) form a monotone increasing sequence in N"
(assuming `a_k ≥ 0` for all `k`, unlike `Bounds.lean` this direction genuinely
needs nonnegativity: a negative coefficient can make adding a layer decrease
the value). We prove the single-step inequality
`rollUp a 1 N ≤ rollUp a 1 (N+1)` and package it as `Monotone (truncRadical a)`.
-/

namespace RamanujanNested

/-- Single-step monotonicity: adding one more layer (with the canonical seed
`1`) never decreases the truncated radical, provided every coefficient is
nonnegative. Stated with `a` quantified inside the induction (same reason as
in `Bounds.lean`: the inductive step needs the claim for the *shifted*
coefficient sequence, not just the original `a`). -/
theorem rollUp_seed_one_step_mono :
    ∀ (N : ℕ) (a : ℕ → ℝ), (∀ k, 0 ≤ a k) → rollUp a 1 N ≤ rollUp a 1 (N + 1) := by
  intro N
  induction N with
  | zero =>
    intro a ha
    rw [rollUp_succ]
    have h1 : rollUp (fun k => a (k + 1)) 1 0 = (1 : ℝ) := rfl
    rw [h1]
    have ha1 : 0 ≤ a 1 := ha 1
    have hle : (1 : ℝ) ≤ 1 + a 1 * 1 := by nlinarith
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (1 + a 1 * 1) := Real.sqrt_le_sqrt hle
  | succ n ih =>
    intro a ha
    have ha_shift : ∀ k, 0 ≤ (fun k => a (k + 1)) k := fun k => ha (k + 1)
    have ih_shift := ih (fun k => a (k + 1)) ha_shift
    rw [rollUp_succ, rollUp_succ]
    have ha1 : 0 ≤ a 1 := ha 1
    have hstep : 1 + a 1 * rollUp (fun k => a (k + 1)) 1 n ≤
        1 + a 1 * rollUp (fun k => a (k + 1)) 1 (n + 1) := by
      have := mul_le_mul_of_nonneg_left ih_shift ha1
      linarith
    exact Real.sqrt_le_sqrt hstep

/-- `truncRadical a` is monotone in the truncation depth, for nonnegative
coefficients — the monotonicity half of Section 4.1's convergence argument. -/
theorem truncRadical_monotone (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k) :
    Monotone (truncRadical a) := by
  apply monotone_nat_of_le_succ
  intro N
  exact rollUp_seed_one_step_mono N a ha

end RamanujanNested
