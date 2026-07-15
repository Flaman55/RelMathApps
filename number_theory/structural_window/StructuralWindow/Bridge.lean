import StructuralWindow.GeneralLaw

/-!
# StructuralWindow.Bridge — the existential entry point

The whole mechanism reduces the general law to a single existential input: *a prime in every
window of the coupled family*. This module supplies the missing connector, `prime ⟹ void`, and
packages it as `generalLaw_of_shortInterval`: plug in any analytic short-interval prime existence
result over the family's range, and `GeneralLaw` — hence Bertrand, Legendre, and a prime in any
window — follows. Nothing else is needed; the structure is complete up to this one estimate.
-/

namespace StructuralWindow

/-- A prime in the window, above the active-base cutoff (`A+W < p²`), is a void: no active-covering
    prime can divide it. -/
theorem isVoid_of_prime {A W p : ℕ} (hp : p.Prime) (hlow : A + W < p ^ 2) : isVoid A W p := by
  intro q hq hqp
  unfold activeBase at hq
  rw [Finset.mem_filter] at hq
  have hq2 : q ^ 2 ≤ A + W := hq.2.2
  have hqp' : q = p := (Nat.prime_dvd_prime_iff_eq hq.2.1 hp).mp hqp
  subst hqp'
  omega

/-- Existential entry point: a prime in the window forces a void. -/
theorem windowHasVoid_of_prime_in_window {A W p : ℕ} (hp : p.Prime)
    (hmem : p ∈ coupledWindow A W) (hlow : A + W < p ^ 2) : windowHasVoid A W :=
  ⟨p, hmem, isVoid_of_prime hp hlow⟩

/-- **The bridge.** A short-interval prime-existence result over the family's range yields the
    general law. Supply any analytic "there is a prime in `(A, A+W]`" for the coupled widths, and
    every downstream corollary — Bertrand, Legendre, a prime in any window — follows through
    `GeneralLaw`. The mechanism is complete up to this one existential estimate. -/
theorem generalLaw_of_shortInterval
    (h : ∀ A W, 2 ≤ A → 2 * Nat.sqrt A + 1 ≤ W → W ≤ A → ∃ p, A < p ∧ p ≤ A + W ∧ p.Prime) :
    GeneralLaw := by
  intro A W hA hlo hhi
  obtain ⟨p, h1, h2, hp⟩ := h A W hA hlo hhi
  refine windowHasVoid_of_prime_in_window hp ?_ ?_
  · rw [coupledWindow, Finset.mem_Ioc]; exact ⟨h1, h2⟩
  · nlinarith [h1, hhi, hA]

end StructuralWindow
