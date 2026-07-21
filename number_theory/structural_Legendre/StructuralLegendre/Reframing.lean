import StructuralLegendre.Basic

/-!
# StructuralLegendre.Reframing — Legendre as Bertrand, narrowed from the left

The Legendre window is Bertrand's window at the same top, with the left edge pushed right. These
are interval identities — provable outright — so they *confirm* the reduction structurally. The
one thing they do NOT (and must not) settle is the localization of a prime into the right sliver;
that stays open at `θ = 1/2`.
-/

namespace StructuralLegendre

/-- The Legendre window `legendreWindow N` has top `(N+1)²`: it is `(N², (N+1)²]`. -/
theorem legendreWindow_eq (N : ℕ) : legendreWindow N = Finset.Ioc (N ^ 2) ((N + 1) ^ 2) := by
  unfold legendreWindow coupledWindow
  rw [show N ^ 2 + (2 * N + 1) = (N + 1) ^ 2 from by ring]

/-- Legendre in Bertrand's frame: the window ending at `(N+1)²` with the left edge narrowed to
    `(N+1)² − (2N+1) = N²`. -/
theorem legendreWindow_narrowed (N : ℕ) :
    legendreWindow N = Finset.Ioc ((N + 1) ^ 2 - (2 * N + 1)) ((N + 1) ^ 2) := by
  rw [legendreWindow_eq, show (N + 1) ^ 2 - (2 * N + 1) = N ^ 2 from by
    have : (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := by ring
    omega]

/-- The Legendre width is at most half its top (for `N ≥ 3`): it is Bertrand's window *narrowed*,
    not the full doubling. -/
theorem legendre_width_le_half (N : ℕ) (hN : 3 ≤ N) : 2 * (2 * N + 1) ≤ (N + 1) ^ 2 := by
  nlinarith [hN]

/-- Legendre's window is the right sliver of Bertrand's window at the same top: it is contained in
    the same-top doubling window `((N+1)²/2, (N+1)²]`. -/
theorem legendreWindow_subset_doubling (N : ℕ) (hN : 3 ≤ N) :
    legendreWindow N ⊆ Finset.Ioc ((N + 1) ^ 2 / 2) ((N + 1) ^ 2) := by
  rw [legendreWindow_eq]
  apply Finset.Ioc_subset_Ioc
  · have h : (N + 1) ^ 2 = N ^ 2 + 2 * N + 1 := by ring
    have h2 : 2 * N + 1 ≤ N ^ 2 := by nlinarith [hN]
    omega
  · exact le_refl _

end StructuralLegendre
