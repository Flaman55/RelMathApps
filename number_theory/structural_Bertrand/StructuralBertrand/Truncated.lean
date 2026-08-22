import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
# Truncated.lean — Truncated arithmetic: the sparse-base regime (closed, no `sorry`)

This is the unconditionally closable part of Section 7 / Corollary 7.1 of the paper.

**What is not here:** the general Corollary 7.1 for all `P_min`. For `P_min = 2` the window
`(P_max, P_min·P_max]` equals `(P_max, 2·P_max]`, so the general statement would imply
Bertrand, and that requires a size estimate — the quantitative certificate in `Erdos.lean`.

**What is here:** the regime in which a purely structural argument (a union bound) already
suffices: when the total number of covered positions is smaller than the size of the window.
This is exactly the integer form of the condition `Σ_{p ∈ base} 1/p < 1`. Bertrand
(`P_min = 2`) lies outside this regime, since there `Σ 1/p` diverges; this single lemma is
therefore the exact boundary between "structure suffices" and "a size estimate is needed".

Proof: cardinality of a finite union (`card_biUnion_le`) plus the pigeonhole principle. No
analysis.
-/

namespace StructuralBertrand

open Finset

/--
**Union bound (core of the sparse-base regime).**

If, in the window `(lo, hi]`, the total number of multiples of the base elements `B` is
smaller than the size of the window, then some window element is uncovered by every element
of `B` (irreducible with respect to `B`). Purely combinatorial, with no size estimate.
-/
theorem exists_uncovered_of_card_lt
    {B : Finset ℕ} {lo hi : ℕ}
    (hcard : ∑ p ∈ B, ((Finset.Ioc lo hi).filter (fun n => p ∣ n)).card
              < (Finset.Ioc lo hi).card) :
    ∃ n ∈ Finset.Ioc lo hi, ∀ p ∈ B, ¬ p ∣ n := by
  classical
  set W := Finset.Ioc lo hi with hW
  set C := W.filter (fun n => ∃ p ∈ B, p ∣ n) with hC
  -- C is the union over p ∈ B of the multiples of p in the window
  have hCeq : C = B.biUnion (fun p => W.filter (fun n => p ∣ n)) := by
    ext n
    simp only [hC, Finset.mem_filter, Finset.mem_biUnion]
    constructor
    · rintro ⟨hnW, p, hp, hpd⟩; exact ⟨p, hp, hnW, hpd⟩
    · rintro ⟨p, hp, hnW, hpd⟩; exact ⟨hnW, p, hp, hpd⟩
  -- |C| ≤ Σ |multiples of p|
  have hCle : C.card ≤ ∑ p ∈ B, (W.filter (fun n => p ∣ n)).card := by
    rw [hCeq]; exact Finset.card_biUnion_le
  have hCsub : C ⊆ W := by rw [hC]; exact Finset.filter_subset _ _
  have hClt : C.card < W.card := lt_of_le_of_lt hCle hcard
  -- since |C| < |W| and C ⊆ W, the set W \ C is nonempty
  have hne : (W \ C).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    have hWC : W ⊆ C := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have hWeqC : W = C := Finset.Subset.antisymm hWC hCsub
    rw [hWeqC] at hClt
    exact lt_irrefl _ hClt
  obtain ⟨n, hn⟩ := hne
  rw [Finset.mem_sdiff] at hn
  obtain ⟨hnW, hnC⟩ := hn
  refine ⟨n, hnW, ?_⟩
  intro p hp hpd
  exact hnC (by rw [hC, Finset.mem_filter]; exact ⟨hnW, p, hp, hpd⟩)

/--
**Corollary 7.1 (sparse-base regime).**

The window `(P_max, P_min·P_max]` cannot be sieve-closed by the base `B` whenever the base
is sufficiently sparse: the total number of multiples is smaller than the window size. Then
an uncovered element exists (irreducible with respect to `B`), so the interval is not
sieve-closed.

For `P_min = 2` (Bertrand) the hypothesis `hsparse` fails — the sum meets or exceeds the
window size, since `Σ 1/p` diverges — so this lemma does not yield Bertrand. This is the
precise formal description of the regime boundary.
-/
theorem truncated_not_sieve_closed
    {P_min P_max : ℕ} {B : Finset ℕ}
    (hsparse : ∑ p ∈ B, ((Finset.Ioc P_max (P_min * P_max)).filter (fun n => p ∣ n)).card
                < (Finset.Ioc P_max (P_min * P_max)).card) :
    ∃ n, P_max < n ∧ n ≤ P_min * P_max ∧ ∀ p ∈ B, ¬ p ∣ n := by
  obtain ⟨n, hnW, hunc⟩ := exists_uncovered_of_card_lt hsparse
  rw [Finset.mem_Ioc] at hnW
  exact ⟨n, hnW.1, hnW.2, hunc⟩

/-- Size of the truncated window: `|(P_max, P_min·P_max]| = P_min·P_max − P_max`.
    Auxiliary for checking the hypothesis `hsparse`. -/
theorem card_truncated_window (P_min P_max : ℕ) :
    (Finset.Ioc P_max (P_min * P_max)).card = P_min * P_max - P_max := by
  rw [Nat.card_Ioc]

end StructuralBertrand
