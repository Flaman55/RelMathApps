import StructuralWindow.SmallAnchors
import StructuralWindow.Determinism

/-!
# StructuralWindow.Legendre — the instances and the crossover

Bertrand `(P, 2P]` and Legendre `(n², (n+1)²]` are two placements of one object. Concrete windows
are settled by evaluation. The point of interest is the structural crossover at `n = 42`:

* for `n ≤ 41` the Jacobsthal floor of the participating rings is below the width `2n+1`, so a
  void is *structurally forced* (the small-anchor regime);
* at `n = 42`, window `(1764, 1849]`, the prime `43` enters the active set and the floor jumps to
  `g = 90 > 85 = 2·42+1`, so the worst-case CRT arrangement could cover the window — the
  structural forcing gives out.

The Jacobsthal floors of the large primorials are not computable in-kernel, so the crossover
value is the external fact `g(∏ p≤43) = 90` (OEIS A048670). What *is* checkable is that the void
is nonetheless present at and past the crossover: Legendre holds computationally here, even where
the structural bound no longer forces it. That gap — worst-case CRT vs the actual square
positions — is the open problem.
-/

namespace StructuralWindow

/-- The Legendre statement at scale `n`: a void in `(n², (n+1)²]`. With the generative
    determinism `void ⟹ prime` (to be added), this is "a prime between consecutive squares". -/
def LegendreVoid (n : ℕ) : Prop := windowHasVoid (n ^ 2) (2 * n + 1)

instance instDecidableLegendreVoid (n : ℕ) : Decidable (LegendreVoid n) := by
  unfold LegendreVoid; infer_instance

/-- Legendre's conjecture in void form — the target of the development (open). -/
def LegendreConjecture : Prop := ∀ n, 0 < n → LegendreVoid n

/-- A void between consecutive squares is a prime there: `LegendreVoid` really is "a prime in
    `(n², (n+1)²]`". Combines the atom with generative determinism. -/
theorem exists_prime_between_squares {n : ℕ} (hn : 2 ≤ n) (h : LegendreVoid n) :
    ∃ p, n ^ 2 < p ∧ p ≤ (n + 1) ^ 2 ∧ p.Prime := by
  obtain ⟨m, hm, hv⟩ := h
  have hmem := hm
  rw [coupledWindow, Finset.mem_Ioc] at hmem
  have hm1 : 1 < m := by nlinarith [hmem.1, hn]
  have hp : m.Prime := prime_of_isVoid hm hm1 hv
  refine ⟨m, hmem.1, ?_, hp⟩
  have heq : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
  omega

/-- Legendre's conjecture in its usual form follows from the void form. -/
theorem legendre_of_conjecture (h : LegendreConjecture) {n : ℕ} (hn : 2 ≤ n) :
    ∃ p, n ^ 2 < p ∧ p ≤ (n + 1) ^ 2 ∧ p.Prime :=
  exists_prime_between_squares hn (h n (by omega))

-- Concrete Legendre windows carry a void, including the crossover and beyond.
example : LegendreVoid 7 := by native_decide          -- (49, 64]
example : LegendreVoid 41 := by native_decide          -- last structurally forced (g ≤ width)
example : LegendreVoid 42 := by native_decide          -- crossover (1764,1849]: g=90 > 85, void present
example : LegendreVoid 60 := by native_decide          -- well past the crossover

-- Bertrand windows likewise (the near-edge end of the same object).
example : windowHasVoid 7 7 := by native_decide         -- (7, 14]
example : windowHasVoid 97 97 := by native_decide       -- (97, 194]

end StructuralWindow
