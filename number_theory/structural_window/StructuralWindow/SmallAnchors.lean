import StructuralWindow.Forcing

/-!
# StructuralWindow.SmallAnchors — the anchor experiment, closed structurally

For a fixed active-ring set (product `M`) the Jacobsthal bound `g(M)` is a finite, decidable
fact: over one period `[0, M)`, every window of `g(M)` consecutive residues contains one coprime
to `M`. By periodicity this lifts to *every* position, giving the structural forcing

    every window of width `g(M)` contains an integer coprime to `M`

for the small anchors `3, 5, 7, 11` (products `6, 30, 210, 2310`, floors `4, 6, 10, 14` — the
same values as `structural_bertrand`). Combined with `windowHasVoid_iff_exists_coprime`, this
forces a void wherever the active-base product is `M`.
-/

namespace StructuralWindow

/-- Coprimality to `M` depends only on the residue mod `M`. -/
theorem coprime_of_mod {M x : ℕ} (h : Nat.Coprime M (x % M)) : Nat.Coprime M x := by
  unfold Nat.Coprime at *
  rw [Nat.gcd_rec, Nat.gcd_comm]
  exact h

/-- Periodic lift: a decidable residue-level Jacobsthal core forces a coprime in every window of
    width `g`, at every position. -/
theorem force_of_core {M g : ℕ} (hg : g < M)
    (hcore : ∀ r < M, ∃ i ∈ Finset.Icc 1 g, Nat.Coprime M ((r + i) % M)) (a : ℕ) :
    ∃ n ∈ Finset.Ioc a (a + g), Nat.Coprime M n := by
  have hM : 0 < M := by omega
  obtain ⟨i, hi, hcop⟩ := hcore (a % M) (Nat.mod_lt a hM)
  rw [Finset.mem_Icc] at hi
  refine ⟨a + i, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  apply coprime_of_mod
  have hi' : i % M = i := Nat.mod_eq_of_lt (by omega)
  have hmod : (a + i) % M = (a % M + i) % M := by rw [Nat.add_mod, hi']
  rw [hmod]; exact hcop

-- Residue-level Jacobsthal cores (decidable): g(6)=4, g(30)=6, g(210)=10, g(2310)=14.
theorem core_6 : ∀ r < 6, ∃ i ∈ Finset.Icc 1 4, Nat.Coprime 6 ((r + i) % 6) := by native_decide
theorem core_30 : ∀ r < 30, ∃ i ∈ Finset.Icc 1 6, Nat.Coprime 30 ((r + i) % 30) := by native_decide
theorem core_210 : ∀ r < 210, ∃ i ∈ Finset.Icc 1 10, Nat.Coprime 210 ((r + i) % 210) := by
  native_decide
theorem core_2310 : ∀ r < 2310, ∃ i ∈ Finset.Icc 1 14, Nat.Coprime 2310 ((r + i) % 2310) := by
  native_decide

-- Structural forcing per anchor: every window of width g(M) contains an M-coprime.
theorem force_6 (a : ℕ) : ∃ n ∈ Finset.Ioc a (a + 4), Nat.Coprime 6 n :=
  force_of_core (by norm_num) core_6 a       -- anchor 3

theorem force_30 (a : ℕ) : ∃ n ∈ Finset.Ioc a (a + 6), Nat.Coprime 30 n :=
  force_of_core (by norm_num) core_30 a      -- anchor 5

theorem force_210 (a : ℕ) : ∃ n ∈ Finset.Ioc a (a + 10), Nat.Coprime 210 n :=
  force_of_core (by norm_num) core_210 a     -- anchor 7

theorem force_2310 (a : ℕ) : ∃ n ∈ Finset.Ioc a (a + 14), Nat.Coprime 2310 n :=
  force_of_core (by norm_num) core_2310 a    -- anchor 11

/-- Bridge to the atom: where the window's active-base product is `M`, an `M`-coprime in the
    window is a void. -/
theorem windowHasVoid_of_force {A W M : ℕ} (hprod : activeBaseProd (A + W) = M)
    (hforce : ∃ n ∈ Finset.Ioc A (A + W), Nat.Coprime M n) : windowHasVoid A W := by
  rw [windowHasVoid_iff_exists_coprime, hprod]
  simpa [coupledWindow] using hforce

-- The anchor forcings, delivered as actual voids (given the matching active product).
theorem windowHasVoid_anchor3 {A : ℕ} (h : activeBaseProd (A + 4) = 6) : windowHasVoid A 4 :=
  windowHasVoid_of_force h (force_6 A)

theorem windowHasVoid_anchor5 {A : ℕ} (h : activeBaseProd (A + 6) = 30) : windowHasVoid A 6 :=
  windowHasVoid_of_force h (force_30 A)

theorem windowHasVoid_anchor7 {A : ℕ} (h : activeBaseProd (A + 10) = 210) : windowHasVoid A 10 :=
  windowHasVoid_of_force h (force_210 A)

theorem windowHasVoid_anchor11 {A : ℕ} (h : activeBaseProd (A + 14) = 2310) : windowHasVoid A 14 :=
  windowHasVoid_of_force h (force_2310 A)

/-- End-to-end via the structural route (not a direct decision): the window `(30, 36]` has active
    base `{2,3,5}`, so `force_30` supplies a void. -/
example : windowHasVoid 30 6 := windowHasVoid_anchor5 (by native_decide)

end StructuralWindow
