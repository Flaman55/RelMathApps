import StructuralWindow.Unification
import Mathlib.NumberTheory.Bertrand

/-!
# StructuralWindow.WidthLaw — the family by width law, and the range to infinity

The generalization is parametrized by a **width law** `W : ℕ → ℕ`: the family of windows
`(A, A + W A]` over all anchors `A`. The quantitative question — which laws force a new prime at
*every* anchor, to infinity — is `GapCertificate W`.

Two laws sit at the ends. Bertrand's `W A = A` (the window `(A, 2A]`) is **closed to infinity**
here, using Mathlib's Bertrand. Legendre's `W A = 2⌊√A⌋ + 1` (`= 2n+1` at `A = n²`) is the open
end. The provable range of laws is the analytic frontier: width exponent `1` (Chebyshev) down to
`0.525` (Baker–Harman–Pintz); Legendre's `1/2` is the single gap below it.
-/

namespace StructuralWindow

/-- A width law forces a new prime at every anchor. -/
def GapCertificate (W : ℕ → ℕ) : Prop := ∀ A, 1 ≤ A → windowHasVoid A (W A)

/-- From the certificate: a new prime in every window of the family. -/
theorem exists_prime_of_gapCertificate {W : ℕ → ℕ} (h : GapCertificate W) {A : ℕ} (hA : 1 ≤ A) :
    ∃ p, A < p ∧ p ≤ A + W A ∧ p.Prime :=
  exists_prime_of_windowHasVoid hA (h A hA)

/-- Bertrand's width law: `W A = A`, the window `(A, 2A]`. -/
def bertrandLaw : ℕ → ℕ := fun A => A

/-- Legendre's width law: `W A = 2⌊√A⌋ + 1`; at a square anchor it is the classical `2n+1`. -/
def legendreLaw : ℕ → ℕ := fun A => 2 * Nat.sqrt A + 1

theorem legendreLaw_sq (n : ℕ) : legendreLaw (n ^ 2) = 2 * n + 1 := by
  simp [legendreLaw, Nat.sqrt_eq']

/-- The Bertrand end of the family is closed to infinity (via Mathlib's Bertrand): every window
    `(A, 2A]` contains a void, hence a new prime. -/
theorem gapCertificate_bertrandLaw : GapCertificate bertrandLaw := by
  intro A hA
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul A (by omega)
  refine ⟨p, ?_, ?_⟩
  · rw [coupledWindow, Finset.mem_Ioc]
    refine ⟨hlt, ?_⟩
    simpa [bertrandLaw, two_mul] using hle
  · intro q hq hqp
    rw [activeBase, Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨_, hqprime, hq2⟩ := hq
    have hqeq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime hp).mp hqp
    subst hqeq
    simp only [bertrandLaw, pow_two] at hq2
    nlinarith [hp.two_le, hlt, hq2]

/-- Consequently Bertrand's postulate itself, in the family's form. -/
theorem exists_prime_bertrandLaw {A : ℕ} (hA : 1 ≤ A) : ∃ p, A < p ∧ p ≤ 2 * A ∧ p.Prime := by
  have := exists_prime_of_gapCertificate gapCertificate_bertrandLaw hA
  simpa [bertrandLaw, two_mul] using this

end StructuralWindow
