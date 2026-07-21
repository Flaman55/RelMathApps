import Mathlib

/-!
# StructuralGoldbach — Basic

Additive counterpart of the structural (multiplicative) sieve used for Bertrand.

* Multiplicative void (Bertrand): a number NOT built from the base by a **multiple** = prime.
* Additive void (Goldbach): an even number NOT built from the base by a **sum of two primes**
  = a Goldbach counterexample.

Everything here is decidable, so concrete finite ranges are settled by evaluation
(`decide` / `native_decide`), exactly as in the multiplicative development.
-/

namespace StructuralGoldbach

open Finset

/-- `n` is additively built from the prime base: `n = p + q` with both `p, q` prime. -/
def hasGoldbachRep (n : ℕ) : Prop := ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-- Number of (ordered) Goldbach representations of `n`: witnesses `p ≤ n` with `p` and
    `n - p` both prime. This is the **existential margin** — the additive analogue of the
    covered-run count; it must stay `> 0` for every even `n`. -/
def repCount (n : ℕ) : ℕ :=
  ((range (n + 1)).filter (fun p => p.Prime ∧ (n - p).Prime)).card

/-- Additive void: an even number `≥ 4` with no representation as a sum of two primes. -/
def isAdditiveVoid (n : ℕ) : Prop := Even n ∧ 4 ≤ n ∧ ¬ hasGoldbachRep n

/-- A positive representation count yields an actual representation. -/
theorem hasRep_of_repCount_pos {n : ℕ} (h : 0 < repCount n) : hasGoldbachRep n := by
  unfold repCount at h
  rw [card_pos] at h
  obtain ⟨p, hp⟩ := h
  rw [mem_filter, mem_range] at hp
  obtain ⟨hlt, hpp, hqp⟩ := hp
  exact ⟨p, n - p, hpp, hqp, by omega⟩

/-- **Additive self-containment on a finite range.** Every even `n` with `4 ≤ n ≤ N`
    has a Goldbach representation (no additive void up to `N`). Decidable, so verified
    for concrete `N` by evaluation. -/
abbrev noVoidUpTo (N : ℕ) : Prop :=
  ∀ n < N + 1, ¬ (4 ≤ n ∧ n % 2 = 0 ∧ repCount n = 0)

/-- Finite verification of additive self-containment (extend `N` with `native_decide`). -/
example : noVoidUpTo 200 := by native_decide

end StructuralGoldbach
