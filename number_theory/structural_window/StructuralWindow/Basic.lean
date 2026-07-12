import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-!
# StructuralWindow.Basic — anchor-agnostic core

The structural layer of the coupled-window mechanism, written without reference to a specific
anchor. A window `(A, A+W]` is covered by its *active base* — the primes `p` with `p² ≤ A+W`
(a composite `≤ A+W` has a least prime factor `≤ √(A+W)`). A position not divisible by any
active-covering prime is a *void*; inside the deterministic range a void is prime.
-/

namespace StructuralWindow

/-- Coupled window with left endpoint (anchor) `A` and width `W`: the interval `(A, A+W]`. -/
def coupledWindow (A W : ℕ) : Finset ℕ := Finset.Ioc A (A + W)

/-- Active-covering base for a window with top `T`: the primes `p` with `p² ≤ T`. A composite
    `n ≤ T` has least prime factor `≤ √T`, so only these primes can cover the window. -/
def activeBase (T : ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ T)

/-- `n` is a *void* for the window `(A, A+W]`: no active-covering prime of the window divides
    it. Inside the deterministic range this makes `n` prime. -/
def isVoid (A W n : ℕ) : Prop := ∀ p ∈ activeBase (A + W), ¬ p ∣ n

/-- The window `(A, A+W]` contains a void — the anchor-agnostic form of "the window contains a
    prime". -/
def windowHasVoid (A W : ℕ) : Prop := ∃ n ∈ coupledWindow A W, isVoid A W n

instance instDecidableIsVoid (A W n : ℕ) : Decidable (isVoid A W n) := by
  unfold isVoid; infer_instance

instance instDecidableWindowHasVoid (A W : ℕ) : Decidable (windowHasVoid A W) := by
  unfold windowHasVoid; infer_instance

/-- Bertrand's window: anchor `n`, width `n` (so the top is `2n`). -/
def bertrandWindow (n : ℕ) : Finset ℕ := coupledWindow n n

/-- Legendre's window: anchor `n²`, width `2n+1` (so the top is `(n+1)²`). -/
def legendreWindow (n : ℕ) : Finset ℕ := coupledWindow (n ^ 2) (2 * n + 1)

end StructuralWindow
