import StructuralGoldbach.Basic

/-!
# StructuralGoldbach — Bridge

The reduction, mirroring the Bertrand/Legendre `Bridge`: the whole conjecture collapses to a
single existential estimate on the **margin** `repCount`.

* `Goldbach`         — the general law (open).
* `PositiveMargin`   — the estimate to be proved: `repCount n > 0` for every even `n ≥ 4`.
* `goldbach_of_positiveMargin` — plugging the estimate in yields the general law.

There is deliberately **no proof of Goldbach here** (no `sorry` masquerading as one): the file
only records that the additive structure reduces the conjecture to keeping the margin off zero.
The finite range is already discharged by `noVoidUpTo` in `Basic`; the open content is the jump
to *all* `N`.
-/

namespace StructuralGoldbach

open Finset

/-- Goldbach's conjecture as the "general law": every even `n ≥ 4` is a sum of two primes. -/
def Goldbach : Prop := ∀ n, 4 ≤ n → Even n → hasGoldbachRep n

/-- The existential estimate the structure reduces to: the representation margin never hits zero. -/
def PositiveMargin : Prop := ∀ n, 4 ≤ n → Even n → 0 < repCount n

/-- **Bridge.** A uniform positive margin everywhere yields the general law. -/
theorem goldbach_of_positiveMargin (h : PositiveMargin) : Goldbach :=
  fun n hn he => hasRep_of_repCount_pos (h n hn he)

/-- Conversely the general law forces the margin to be positive (both directions are trivial;
    the point is that `PositiveMargin` is exactly the quantitative heart). -/
theorem positiveMargin_of_goldbach (h : Goldbach) : PositiveMargin := by
  intro n hn he
  obtain ⟨p, q, hp, hq, hpq⟩ := h n hn he
  unfold repCount
  rw [card_pos]
  refine ⟨p, ?_⟩
  rw [mem_filter, mem_range]
  have hnp : n - p = q := by omega
  exact ⟨by omega, hp, by rw [hnp]; exact hq⟩

/-- **Cel kroku 3 — dolny płot Hardy'ego–Littlewooda.** Margines rozkładów jest ograniczony
    z dołu przez dodatnią wielokrotność `n / (log n)²` (empirycznie stała ≈ 0.8). To jest
    addytywny odpowiednik oszacowania pokrycia „dziura < okno", które domknęło Bertranda. -/
def HL_Floor : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 4 ≤ n → Even n →
    c * (n : ℝ) / (Real.log n) ^ 2 ≤ (repCount n : ℝ)

/-- Dolny płot HL wymusza dodatni margines (bo płot jest > 0 dla `n ≥ 4`). -/
theorem positiveMargin_of_HL (h : HL_Floor) : PositiveMargin := by
  obtain ⟨c, hc, hfloor⟩ := h
  intro n hn he
  by_contra hcon
  have h0 : repCount n = 0 := Nat.le_zero.mp (Nat.not_lt.mp hcon)
  have hb := hfloor n hn he
  rw [h0] at hb
  push_cast at hb
  have hnR : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnR
  have hpos : 0 < c * (n : ℝ) / (Real.log n) ^ 2 := by positivity
  linarith

/-- **Domknięcie:** dolny płot HL ⟹ Goldbach (przez margines i most). -/
theorem goldbach_of_HL (h : HL_Floor) : Goldbach :=
  goldbach_of_positiveMargin (positiveMargin_of_HL h)

end StructuralGoldbach
