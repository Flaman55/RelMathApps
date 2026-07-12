import StructuralWindow.Unification
import StructuralWindow.Legendre

/-!
# StructuralWindow.GeneralLaw — the general law, and everything as its corollary

The target is not Legendre but the **general law to infinity**: at every anchor `A`, every window
`(A, A+W]` whose width lies between the Legendre width `2⌊√A⌋+1` and the Bertrand width `A`
contains a new prime. From this one law, Bertrand, Legendre, and every window sitting in the
deterministic range fall out as corollaries — that is its purpose.

`GeneralLaw` is the open target: it implies Legendre (take `W = 2⌊√A⌋+1` at `A = n²`). The point
of this file is the *extraction* — the corollary arrows are proved unconditionally.
-/

namespace StructuralWindow

/-- The general law to infinity: at every anchor, every window from the Legendre width up to the
    Bertrand width contains a void (a new prime). -/
def GeneralLaw : Prop :=
  ∀ A W, 2 ≤ A → 2 * Nat.sqrt A + 1 ≤ W → W ≤ A → windowHasVoid A W

/-- From the general law: a new prime in every window of the family. -/
theorem exists_prime_of_generalLaw (h : GeneralLaw) {A W : ℕ}
    (hA : 2 ≤ A) (hlo : 2 * Nat.sqrt A + 1 ≤ W) (hhi : W ≤ A) :
    ∃ p, A < p ∧ p ≤ A + W ∧ p.Prime :=
  exists_prime_of_windowHasVoid (by omega) (h A W hA hlo hhi)

/-- Legendre falls out of the general law (anchor `A = n²`, width `W = 2n+1`, the lower end). -/
theorem legendreConjecture_of_generalLaw (h : GeneralLaw) : LegendreConjecture := by
  intro n hn
  rcases n with _ | _ | _ | k
  · omega
  · exact (by native_decide : LegendreVoid 1)
  · exact (by native_decide : LegendreVoid 2)
  · show windowHasVoid ((k + 3) ^ 2) (2 * (k + 3) + 1)
    apply h
    · nlinarith
    · simp [Nat.sqrt_eq']
    · nlinarith

/-- Bertrand falls out of the general law too (width `W = A`, the upper end). -/
theorem bertrand_of_generalLaw (h : GeneralLaw) {A : ℕ} (hA : 6 ≤ A) :
    ∃ p, A < p ∧ p ≤ 2 * A ∧ p.Prime := by
  have hlo : 2 * Nat.sqrt A + 1 ≤ A := by
    have hs : Nat.sqrt A ^ 2 ≤ A := Nat.sqrt_le' A
    rcases le_or_lt (Nat.sqrt A) 2 with h2 | h2
    · omega
    · nlinarith [hs, h2]
  obtain ⟨p, h1, h2p, h3⟩ :=
    exists_prime_of_windowHasVoid (by omega : 1 ≤ A) (h A A (by omega) hlo (le_refl A))
  exact ⟨p, h1, by omega, h3⟩

end StructuralWindow
