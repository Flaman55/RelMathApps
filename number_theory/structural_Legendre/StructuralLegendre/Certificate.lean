import StructuralLegendre.Legendre

/-!
# StructuralLegendre.Certificate — the generalized forcing; Legendre is a by-product

The object here is not a proof of Legendre's conjecture but the *generalized* coupled-window
mechanism: for a window `(A, A+W]` with **free position `A` and width `W`**, a void is forced
exactly when the window holds an integer coprime to the active-ring product — governed by the
participating rings and their Jacobsthal floor `g`. Bertrand (`A=P, W=P`) and Legendre
(`A=n², W=2n+1`) are two evaluations of the one mechanism; Legendre is at most a by-product.

Where the rings are sparse against the width (`g < W`, the Bertrand end) the void is forced. Where
they are dense (`g ≥ W`, the Legendre end) the mechanism localizes an open frontier — and it does
so without ever being aimed at Legendre.
-/

namespace StructuralLegendre

/-- The generalized forcing condition for a coupled window `(A, A+W]`: a coprime to the active-ring
    product, equivalently a void. Position and width are free — this is the mechanism itself. -/
def WindowForcing (A W : ℕ) : Prop :=
  ∃ m ∈ Finset.Ioc A (A + W), Nat.Coprime (activeBaseProd (A + W)) m

/-- The mechanism is exactly `windowHasVoid`. -/
theorem windowHasVoid_iff_windowForcing (A W : ℕ) :
    windowHasVoid A W ↔ WindowForcing A W :=
  windowHasVoid_iff_exists_coprime A W

/-- Bertrand is one evaluation of the mechanism — sparse rings, forced. -/
example : WindowForcing 7 7 := (windowHasVoid_iff_windowForcing 7 7).mp (by native_decide)

/-- Legendre is another evaluation — the by-product. For any scale where the mechanism supplies a
    void, a prime lies between the squares (`exists_prime_between_squares`); the general such
    supply is the open frontier, reached here only as a consequence, never as the aim. -/
theorem legendre_of_windowForcing (h : ∀ n, 0 < n → WindowForcing (n ^ 2) (2 * n + 1)) :
    LegendreConjecture := by
  intro n hn
  show windowHasVoid (n ^ 2) (2 * n + 1)
  rw [windowHasVoid_iff_windowForcing]
  exact h n hn

example : WindowForcing (7 ^ 2) (2 * 7 + 1) :=
  (windowHasVoid_iff_windowForcing _ _).mp (by native_decide)

end StructuralLegendre
