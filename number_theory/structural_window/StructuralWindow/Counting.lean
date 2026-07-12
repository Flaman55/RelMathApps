import StructuralWindow.Basic

/-!
# StructuralWindow.Counting — the atom in counting form

The window has a void exactly when the active base fails to cover all `W` positions. This is
the anchor-agnostic analogue of `structural_bertrand`'s `windowHasVoid_iff_coveredCount_lt`, and
it is the point at which the whole question localizes.
-/

namespace StructuralWindow

/-- Number of positions in the window `(A, A+W]` covered by the active base. -/
def coveredCount (A W : ℕ) : ℕ :=
  ((coupledWindow A W).filter (fun n => ∃ p ∈ activeBase (A + W), p ∣ n)).card

/-- The window has exactly `W` positions. -/
theorem card_coupledWindow (A W : ℕ) : (coupledWindow A W).card = W := by
  unfold coupledWindow
  rw [Nat.card_Ioc]
  omega

/-- The atom: the window contains a void iff the base does not cover all `W` positions. -/
theorem windowHasVoid_iff_coveredCount_lt (A W : ℕ) :
    windowHasVoid A W ↔ coveredCount A W < W := by
  have hvoid_iff : ∀ n, isVoid A W n ↔ ¬ (∃ p ∈ activeBase (A + W), p ∣ n) :=
    fun n => ⟨fun h ⟨p, hp, hpn⟩ => h p hp hpn, fun h p hp hpn => h ⟨p, hp, hpn⟩⟩
  have hfilter :
      (coupledWindow A W).filter (isVoid A W)
        = (coupledWindow A W).filter (fun n => ¬ (∃ p ∈ activeBase (A + W), p ∣ n)) :=
    Finset.filter_congr (fun n _ => hvoid_iff n)
  have hpart :
      coveredCount A W + ((coupledWindow A W).filter (isVoid A W)).card = W := by
    unfold coveredCount
    rw [hfilter, Finset.filter_card_add_filter_neg_card_eq_card, card_coupledWindow]
  constructor
  · rintro ⟨n, hn, hv⟩
    have hne : ((coupledWindow A W).filter (isVoid A W)).Nonempty :=
      ⟨n, Finset.mem_filter.mpr ⟨hn, hv⟩⟩
    have := Finset.card_pos.mpr hne
    omega
  · intro h
    have hpos : 0 < ((coupledWindow A W).filter (isVoid A W)).card := by omega
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hn
    exact ⟨n, hn.1, hn.2⟩

end StructuralWindow
