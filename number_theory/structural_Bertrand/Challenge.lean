import Mathlib.Data.Nat.Prime.Basic

/-!
# Advertised statement

This is the small, trusted surface a mathematical reader should audit: Bertrand's
postulate in its Chebyshev-strengthened form. For every integer `N > 1` there is a
prime strictly greater than `N` and at most `2 * N`.

The statement below is discharged in `Solution.lean` by invoking the fully independent
structural proof `StructuralBertrand.bertrand_chebyshev`, developed in this repository's
`StructuralBertrand/Main.lean`. That development does **not** import
`Mathlib.NumberTheory.Bertrand`; the quantitative core is an original structural sieve
described in the accompanying paper (`LaTex/A Structural Sieve for Bertrands
Postulate.pdf`).
-/

/-- **Bertrand–Chebyshev bound.** For every `N > 1` there is a prime `p` with
`N < p ≤ 2 * N`. -/
theorem Submission.bertrand_chebyshev (N : ℕ) (hN : 1 < N) :
    ∃ p : ℕ, N < p ∧ p ≤ 2 * N ∧ p.Prime := by
  sorry
