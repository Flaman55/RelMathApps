import StructuralLegendre.Basic

/-!
# StructuralLegendre.Jacobsthal — the structural floor

The Jacobsthal function `g(M)` of the ring product `M = ∏(active rings)` is the widest window
the rings dividing `M` can fully cover — the longest run of consecutive integers each sharing a
factor with `M`. It is the structural floor of the window width: a window wider than `g(M)`
must contain a position coprime to `M` (a void). Here `g` is computable, so the floors of small
active-ring sets are settled by evaluation; the values match `structural_bertrand`.
-/

namespace StructuralLegendre

/-- Product of the active rings up to `s`: `∏ (p prime ≤ s)`. Choosing the anchor `s` selects
    the active ring set — Bertrand's `Pmax = 7` takes all of `{2,3,5,7}`; the generalized
    reading takes smaller anchors `5, 3` as smaller ring sets. -/
def activePrimorial (s : ℕ) : ℕ := ((Finset.range (s + 1)).filter Nat.Prime).prod id

/-- The Jacobsthal function `g(M)`: the maximal gap between consecutive integers coprime to `M`,
    i.e. the longest fully-coverable run plus one. Computed over two periods `[0, 2M)`, which by
    periodicity contains the maximal gap. -/
def jacobsthal (M : ℕ) : ℕ :=
  let cs := (List.range (2 * M)).filter (fun n => Nat.gcd M n == 1)
  ((cs.zip cs.tail).map (fun p => p.2 - p.1)).foldr max 0

-- Small active-ring sets (the anchor experiment); values match `structural_bertrand`.
example : jacobsthal 6 = 4 := by native_decide       -- anchor 3: rings {2,3}
example : jacobsthal 30 = 6 := by native_decide       -- anchor 5: rings {2,3,5}
example : jacobsthal 210 = 10 := by native_decide      -- anchor 7: rings {2,3,5,7}
example : jacobsthal 2310 = 14 := by native_decide     -- anchor 11: rings {2,3,5,7,11}

example : activePrimorial 7 = 210 := by native_decide

end StructuralLegendre
