import RamanujanNested.Bounds
import RamanujanNested.Monotone
import Mathlib

/-!
# Convergence.lean — Section 4.1's actual conclusion

"the sequence `(R_1^(N))` is bounded from above ... which implies convergence
of the truncated radicals to a finite real limit." `Bounds.lean` gives the
boundedness, `Monotone.lean` gives the monotonicity; this file combines them
via Mathlib's monotone-bounded-sequence convergence theorem
(`tendsto_atTop_ciSup`) to get the actual convergence statement the paper
claims — this is the piece that was missing after the first pass.

This file `import Mathlib` wholesale rather than a narrow path, because the
exact module housing `tendsto_atTop_ciSup` was not double-checked against a
running toolchain in this sandbox (no network access to fetch the Mathlib
cache — see the project root docstring); if that lemma name has moved or been
renamed, this is the one spot in the project most likely to need a fix, and a
wildcard import at least isolates "wrong lemma name" from "wrong import path"
as separate failure modes.
-/

namespace RamanujanNested

open Filter Topology

/-- **Section 4.1, convergence.** For coefficients bounded above by `A` and
nonnegative, the truncated radical `truncRadical a N` converges to a finite
real limit as `N → ∞`. This is the paper's actual stated conclusion for
Section 4.1's main sufficient condition. -/
theorem truncRadical_converges {A : ℝ} (hA : 0 ≤ A) (a : ℕ → ℝ)
    (ha_nonneg : ∀ k, 0 ≤ a k) (ha_le : ∀ k, a k ≤ A) :
    ∃ L : ℝ, Tendsto (truncRadical a) atTop (𝓝 L) := by
  have hmono : Monotone (truncRadical a) := truncRadical_monotone a ha_nonneg
  have hbdd : BddAbove (Set.range (truncRadical a)) := by
    refine ⟨rStar A, ?_⟩
    rintro x ⟨N, rfl⟩
    exact (truncRadical_bounded hA N a ha_le).2
  exact ⟨⨆ i, truncRadical a i, tendsto_atTop_ciSup hmono hbdd⟩

end RamanujanNested
