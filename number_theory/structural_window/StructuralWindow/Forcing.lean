import StructuralWindow.Basic

/-!
# StructuralWindow.Forcing — voids are coprimes to the ring product

A position is a void exactly when it is coprime to `M = ∏(active base)`. This is the bridge
between the window and the Jacobsthal floor `g(M)`: the window contains a void iff it contains
an integer coprime to `M`, and the maximal gap between such integers is `g(M)`. Hence a window
wider than `g(M)` is forced to contain a void — the structural forcing, with no analytic input.
(The gap bound itself, `W ≥ g(M) ⟹ a coprime exists`, is the remaining periodic step.)
-/

namespace StructuralWindow

/-- The product of the active base of a window with top `T`. -/
def activeBaseProd (T : ℕ) : ℕ := (activeBase T).prod id

/-- A void is precisely a position coprime to the product of the active base. -/
theorem isVoid_iff_coprime (A W n : ℕ) :
    isVoid A W n ↔ Nat.Coprime (activeBaseProd (A + W)) n := by
  unfold isVoid activeBaseProd
  rw [Nat.coprime_prod_left_iff]
  constructor
  · intro h p hp
    exact ((Finset.mem_filter.mp hp).2.1.coprime_iff_not_dvd).mpr (h p hp)
  · intro h p hp
    exact ((Finset.mem_filter.mp hp).2.1.coprime_iff_not_dvd).mp (h p hp)

/-- The window contains a void iff it contains an integer coprime to the active-base product —
    the exact input to the Jacobsthal gap bound. -/
theorem windowHasVoid_iff_exists_coprime (A W : ℕ) :
    windowHasVoid A W ↔ ∃ n ∈ coupledWindow A W, Nat.Coprime (activeBaseProd (A + W)) n := by
  unfold windowHasVoid
  apply exists_congr; intro n
  apply and_congr_right; intro _
  exact isVoid_iff_coprime A W n

end StructuralWindow
