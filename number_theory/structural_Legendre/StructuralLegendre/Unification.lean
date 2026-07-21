import StructuralLegendre.Determinism

/-!
# StructuralLegendre.Unification — one anchor, one base, any width

The full generalization, read off the coupled table: at an anchor `A` the base `≤ √(2A)` has one
deterministic reach `≈ (A, 2A]`, and **any** window `(A, A+W]` sitting inside it has its survivors
equal to new primes. Bertrand (`W = A`, the window that fills the reach) and Legendre
(`W = 2⌊√A⌋`, the narrowest window at the bottom of the reach) are two widths of the one object;
every interval in between is an instance too.

The engine is a single theorem: a void in any window is a new prime there (`prime_of_isVoid`).
-/

namespace StructuralLegendre

/-- Survivors are new primes, for **any** interval sitting in the base's deterministic reach:
    a void in `(A, A+W]` is a prime in `(A, A+W]`. This is the whole law — Bertrand, Legendre and
    everything between are widths `W` at a common anchor `A`. -/
theorem exists_prime_of_windowHasVoid {A W : ℕ} (hA : 1 ≤ A) (h : windowHasVoid A W) :
    ∃ p, A < p ∧ p ≤ A + W ∧ p.Prime := by
  obtain ⟨m, hm, hv⟩ := h
  have hm' := hm
  rw [coupledWindow, Finset.mem_Ioc] at hm'
  exact ⟨m, hm'.1, hm'.2, prime_of_isVoid hm (by omega) hv⟩

-- One anchor `A = 169 = 13²`, base `≤ ⌊√(2·169)⌋ = 18`; three widths, all forcing a new prime.
example : ∃ p, 169 < p ∧ p ≤ 169 + 27 ∧ p.Prime :=      -- Legendre  (169, 196],  W = 2·13+1
  exists_prime_of_windowHasVoid (by norm_num) (by native_decide)

example : ∃ p, 169 < p ∧ p ≤ 169 + 100 ∧ p.Prime :=     -- an intermediate interval (169, 269]
  exists_prime_of_windowHasVoid (by norm_num) (by native_decide)

example : ∃ p, 169 < p ∧ p ≤ 169 + 169 ∧ p.Prime :=     -- Bertrand  (169, 338],  W = A
  exists_prime_of_windowHasVoid (by norm_num) (by native_decide)

end StructuralLegendre
