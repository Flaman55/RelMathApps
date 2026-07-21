import StructuralLegendre.Basic

/-!
# StructuralLegendre.Covering — the covering / void duality

A window either contains a void or is *fully covered* by its active base. These are exact
complements, and both are decidable, so concrete windows are settled by evaluation
(`decide` / `native_decide`). This is the foundation of the structural forcing engine: the
Jacobsthal floor (built on top) states how narrow a window must be before full coverage — a
void-free run — becomes possible.
-/

namespace StructuralLegendre

/-- The window `(A, A+W]` is *fully covered* by its active base: every position is divisible by
    some active-covering prime. This is the negation of containing a void. -/
def windowCovered (A W : ℕ) : Prop :=
  ∀ n ∈ coupledWindow A W, ∃ p ∈ activeBase (A + W), p ∣ n

/-- A window contains a void iff it is not fully covered — the exact complement. -/
theorem windowHasVoid_iff_not_windowCovered (A W : ℕ) :
    windowHasVoid A W ↔ ¬ windowCovered A W := by
  constructor
  · rintro ⟨n, hn, hv⟩ hcov
    obtain ⟨p, hp, hpn⟩ := hcov n hn
    exact hv p hp hpn
  · intro hcov
    by_contra hnv
    apply hcov
    intro n hn
    by_contra hnp
    exact hnv ⟨n, hn, fun p hp hpn => hnp ⟨p, hp, hpn⟩⟩

/-- Full coverage rules out a void. -/
theorem not_windowHasVoid_of_windowCovered {A W : ℕ} (h : windowCovered A W) :
    ¬ windowHasVoid A W :=
  fun hv => (windowHasVoid_iff_not_windowCovered A W).mp hv h

instance instDecidableWindowCovered (A W : ℕ) : Decidable (windowCovered A W) := by
  unfold windowCovered; infer_instance

/-- Both sides are decidable, so concrete windows are settled by evaluation. -/
example : windowHasVoid 30 7 := by native_decide      -- (30,37], base {2,3,5}; voids 31, 37

example : windowHasVoid 97 97 := by native_decide      -- Bertrand window (97,194]

example : ¬ windowCovered 30 7 := by native_decide     -- the complement, same window

end StructuralLegendre
