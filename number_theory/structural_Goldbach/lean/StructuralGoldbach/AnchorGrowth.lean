import StructuralGoldbach.Constructive
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.PSeries

/-!
# StructuralGoldbach — AnchorGrowth (elementary superlinear growth, self-contained)

`MovingCeiling.lean`'s `AnchorDoublingRate` needed a genuine lower bound on how fast the
cascade's anchors grow — Bertrand's postulate alone gives only the matching UPPER bound
(`anchor(k+1) ≤ 2·anchor(k)`), the wrong direction. Investigation showed this Mathlib pin
(`v4.14.0`) has neither the Prime Number Theorem nor explicit prime-gap theorems.

What it DOES have, found on inspection: `not_summable_one_div_on_primes` — Erdős's classical
elementary proof that `∑ 1/p` diverges (`Mathlib.NumberTheory.SumPrimeReciprocals`), fully
self-contained, no PNT. This file uses it to derive a genuine, unconditional, elementary
**superlinear** growth rate for the cascade — weaker than the true (empirically ratio → 2)
doubling rate, but real, proved, and sufficient to establish that the cascade's own reach is
not merely linear in the step count.

## Strategy

1. `anchor_prime` : every cascade anchor is a genuine prime (immediate from `nextAnchor`'s
   Bertrand witness, not yet recorded as its own lemma in `Constructive.lean`).
2. `succ_le_primeCounting_anchor` : `anchor 0, …, anchor k` are `k+1` distinct primes `≤ anchor k`,
   so `k + 1 ≤ π(anchor k)`.
3. The Legendre sieve with a *growing* modulus `a_m := ∏_{p ∈ primesBelow m} p`: the density of
   `a_m`-coprime residues is `φ(a_m)/a_m = ∏_{p ≤ m} (1 - 1/p)`, via `Nat.primeFactors_prod` +
   `Nat.totient_mul_prod_primeFactors` (an identity that holds unconditionally, no squarefreeness
   hypothesis needed). Erdős's divergence, through `-log(1-x) ≥ x`, forces this density to `0`.
4. `Nat.primeCounting'_add_le` (already in Mathlib, an elementary Legendre-sieve bound) turns a
   fixed small-density modulus into an asymptotic upper bound `π(x) ≲ (φ(a_m)/a_m)·x`; letting
   the density shrink (step 3) forces `π(x) = o(x)`.
5. Combined with step 2: `anchor(k)/k → ∞`.

## Status

First pass, not yet build-checked (no local Lean toolchain in this environment). This is
substantially larger and more delicate than anything else in the project so far — expect a
real fix round.
-/

namespace StructuralGoldbach

open Finset Filter Topology

/-! ## Step 1–2: anchors are primes; `k+1 ≤ π(anchor k)` -/

/-- Every cascade anchor is a genuine prime (the `nextAnchor` witness from Bertrand's
    postulate, recorded once and for all). -/
theorem anchor_prime (k : ℕ) : (anchor k).Prime := by
  cases k with
  | zero => simpa [anchor] using Nat.prime_two
  | succ n =>
    have h1 : 1 ≤ anchor n := by have := anchor_ge_two n; omega
    obtain ⟨q, hqp, hqlt, hqle⟩ := Nat.exists_prime_lt_and_le_two_mul (anchor n) (by omega)
    set s := (Finset.Ico (anchor n + 1) (2 * anchor n + 1)).filter Nat.Prime with hs
    have hmem : q ∈ s := by
      rw [hs, Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨by omega, by omega⟩, hqp⟩
    have hne : s.Nonempty := ⟨q, hmem⟩
    have heq : anchor (n + 1) = nextAnchor (anchor n) := rfl
    have heq2 : nextAnchor (anchor n) = s.max' hne := by
      show s.max.getD (2 * anchor n) = s.max' hne
      rw [← Finset.coe_max' hne]; rfl
    rw [heq, heq2]
    have hgoal : s.max' hne ∈ (Finset.Ico (anchor n + 1) (2 * anchor n + 1)).filter Nat.Prime := by
      rw [← hs]
      exact Finset.max'_mem s hne
    exact (Finset.mem_filter.mp hgoal).2

/-- `anchor 0, …, anchor k` are `k+1` distinct primes, all `≤ anchor k`. -/
theorem succ_le_primeCounting_anchor (k : ℕ) : k + 1 ≤ Nat.primeCounting (anchor k) := by
  have hmono : StrictMono anchor := strictMono_nat_of_lt_succ anchor_lt_succ
  have hsub : Finset.image anchor (Finset.range (k + 1)) ⊆ (anchor k + 1).primesBelow := by
    intro x hx
    simp only [Finset.mem_image, Finset.mem_range] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hle : anchor i ≤ anchor k := hmono.monotone (by omega)
    rw [Nat.mem_primesBelow]
    exact ⟨by omega, anchor_prime i⟩
  have hcard : (Finset.image anchor (Finset.range (k + 1))).card = k + 1 := by
    rw [Finset.card_image_of_injective _ hmono.injective, Finset.card_range]
  calc k + 1 = (Finset.image anchor (Finset.range (k + 1))).card := hcard.symm
    _ ≤ (anchor k + 1).primesBelow.card := Finset.card_le_card hsub
    _ = Nat.primeCounting' (anchor k + 1) := Nat.primesBelow_card_eq_primeCounting' _
    _ = Nat.primeCounting (anchor k) := rfl

/-! ## Step 3: the growing-modulus density, from Erdős's divergence -/

/-- The growing modulus: the product of all primes `< m`. -/
noncomputable def modulus (m : ℕ) : ℕ := ∏ p ∈ m.primesBelow, p

theorem modulus_pos (m : ℕ) : 0 < modulus m :=
  Finset.prod_pos fun _ hp ↦ (Nat.prime_of_mem_primesBelow hp).pos

/-- `φ(modulus m) = ∏_{p < m} (p - 1)`, unconditionally (no squarefreeness hypothesis needed:
    `Nat.totient_mul_prod_primeFactors` holds for every `n`). -/
theorem totient_modulus (m : ℕ) :
    Nat.totient (modulus m) = ∏ p ∈ m.primesBelow, (p - 1) := by
  have hpf : (modulus m).primeFactors = m.primesBelow :=
    Nat.primeFactors_prod fun p hp ↦ Nat.prime_of_mem_primesBelow hp
  have hid := Nat.totient_mul_prod_primeFactors (modulus m)
  rw [hpf] at hid
  have hprodeq : ∏ p ∈ m.primesBelow, p = modulus m := rfl
  rw [hprodeq] at hid
  exact Nat.eq_of_mul_eq_mul_right (modulus_pos m) (by linarith [hid])

/-- The density `φ(modulus m)/modulus m`, as a real number, equals `∏_{p<m} (1 - 1/p)`. -/
theorem density_modulus (m : ℕ) :
    (Nat.totient (modulus m) : ℝ) / modulus m = ∏ p ∈ m.primesBelow, (1 - (p : ℝ)⁻¹) := by
  rw [totient_modulus]
  have hcastnum : ((∏ p ∈ m.primesBelow, (p - 1) : ℕ) : ℝ)
      = ∏ p ∈ m.primesBelow, ((p - 1 : ℕ) : ℝ) := by push_cast; ring
  have hcastden : (modulus m : ℝ) = ∏ p ∈ m.primesBelow, (p : ℝ) := by
    unfold modulus; push_cast; ring
  rw [hcastnum, hcastden, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro p hp
  have hpp := Nat.prime_of_mem_primesBelow hp
  have h1p : (1 : ℕ) ≤ p := hpp.one_lt.le
  have hppos : (p : ℝ) ≠ 0 := by exact_mod_cast hpp.pos.ne'
  rw [Nat.cast_sub h1p]
  push_cast
  rw [sub_div, div_self hppos, one_div]

/-- The reciprocal sum diverges: partial sums over `primesBelow m` tend to `+∞`. Converts
    Erdős's `¬ Summable` (`not_summable_one_div_on_primes`) into the `Tendsto` form via the
    general fact for nonnegative series. -/
theorem tendsto_sum_primesBelow_atTop :
    Tendsto (fun m : ℕ ↦ ∑ p ∈ m.primesBelow, (1 / p : ℝ)) atTop atTop := by
  have hnonneg : ∀ n : ℕ, 0 ≤ Set.indicator {p | p.Prime} (fun n : ℕ ↦ (1 : ℝ) / n) n :=
    fun n ↦ Set.indicator_nonneg (fun p _ ↦ by positivity) _
  have htendsto := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnonneg).mp
    not_summable_one_div_on_primes
  have heq : (fun m : ℕ ↦ ∑ i ∈ Finset.range m, Set.indicator {p | p.Prime}
      (fun n : ℕ ↦ (1 : ℝ) / n) i) = (fun m : ℕ ↦ ∑ p ∈ m.primesBelow, (1 / p : ℝ)) := by
    funext m
    unfold Nat.primesBelow
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    simp [Set.indicator_apply, Set.mem_setOf_eq]
  rwa [heq] at htendsto

/-- Every term `1 - 1/p` for a prime `p` lies in `[0, 1)`. -/
private theorem term_nonneg {p : ℕ} (hp : p.Prime) : (0 : ℝ) ≤ 1 - (p : ℝ)⁻¹ := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hinv : (p : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; linarith
  linarith

/-- The density `∏_{p<m} (1 - 1/p) → 0`: Erdős's divergence, through `1 - x ≤ exp(-x)`. -/
theorem tendsto_density_zero :
    Tendsto (fun m : ℕ ↦ ∏ p ∈ m.primesBelow, (1 - (p : ℝ)⁻¹)) atTop (𝓝 0) := by
  have hub : ∀ m : ℕ, ∏ p ∈ m.primesBelow, (1 - (p : ℝ)⁻¹)
      ≤ Real.exp (-∑ p ∈ m.primesBelow, (p : ℝ)⁻¹) := by
    intro m
    have hexp : Real.exp (-∑ p ∈ m.primesBelow, (p : ℝ)⁻¹)
        = ∏ p ∈ m.primesBelow, Real.exp (-(p : ℝ)⁻¹) := by
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
    rw [hexp]
    apply Finset.prod_le_prod
    · intro p hp; exact term_nonneg (Nat.prime_of_mem_primesBelow hp)
    · intro p _
      have := Real.add_one_le_exp (-(p : ℝ)⁻¹)
      linarith
  have hlb : ∀ m : ℕ, (0 : ℝ) ≤ ∏ p ∈ m.primesBelow, (1 - (p : ℝ)⁻¹) :=
    fun m ↦ Finset.prod_nonneg fun p hp ↦ term_nonneg (Nat.prime_of_mem_primesBelow hp)
  have hsum : Tendsto (fun m : ℕ ↦ ∑ p ∈ m.primesBelow, (p : ℝ)⁻¹) atTop atTop := by
    simpa only [one_div] using tendsto_sum_primesBelow_atTop
  have hneg : Tendsto (fun m : ℕ ↦ -∑ p ∈ m.primesBelow, (p : ℝ)⁻¹) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hsum
  have hexp0 : Tendsto (fun m : ℕ ↦ Real.exp (-∑ p ∈ m.primesBelow, (p : ℝ)⁻¹)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hneg
  exact squeeze_zero hlb hub hexp0

/-! ## Step 4–5: superlinear growth of the cascade -/

/-- **Elementary superlinear growth of the cascade** (self-contained: Bertrand's postulate +
    Erdős's divergence of `∑ 1/p`, nothing else). Weaker than the empirically observed doubling
    rate (`AnchorDoublingRate`), but genuinely proved, not measured. -/
theorem anchorSuperlinear : Tendsto (fun k : ℕ ↦ (anchor k : ℝ) / k) atTop atTop := by
  rw [tendsto_atTop]
  intro C
  rcases le_or_lt C 0 with hC0 | hC0
  · filter_upwards [eventually_ge_atTop 1] with k _
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.zero_le k
    have hnn : (0 : ℝ) ≤ (anchor k : ℝ) / k :=
      div_nonneg (by exact_mod_cast Nat.zero_le _) hk0
    linarith
  · set ε : ℝ := 1 / (2 * (C + 1)) with hεdef
    have hε : 0 < ε := by positivity
    have hev := tendsto_density_zero.eventually (Iio_mem_nhds hε)
    obtain ⟨m₀, hm₀⟩ := Filter.eventually_atTop.mp hev
    have hdensity : (Nat.totient (modulus m₀) : ℝ) / modulus m₀ < ε := by
      have h := hm₀ m₀ le_rfl
      rwa [← density_modulus] at h
    have ha₀pos : 0 < modulus m₀ := modulus_pos m₀
    set a₀ := modulus m₀
    set k₀ := a₀ + 1 with hk₀def
    have ha₀ltk₀ : a₀ < k₀ := by omega
    set B : ℝ := (Nat.primeCounting' k₀ : ℝ) + (Nat.totient a₀ : ℝ) with hBdef
    have hπbound : ∀ x : ℕ, k₀ ≤ x + 1 → (Nat.primeCounting' (x + 1) : ℝ) ≤ B + ε * x := by
      intro x hx
      obtain ⟨n, hn⟩ := Nat.le.dest hx
      have hlem := Nat.primeCounting'_add_le ha₀pos ha₀ltk₀ n
      have hd : ((n / a₀ : ℕ) : ℝ) ≤ (n : ℝ) / a₀ := Nat.cast_div_le
      have htot0 : (0 : ℝ) ≤ (Nat.totient a₀ : ℝ) := by positivity
      have step1 : (Nat.primeCounting' (k₀ + n) : ℝ)
          ≤ (Nat.primeCounting' k₀ : ℝ) + (Nat.totient a₀ : ℝ) * ((n : ℝ) / a₀ + 1) := by
        have hcast : ((Nat.primeCounting' k₀ + Nat.totient a₀ * (n / a₀ + 1) : ℕ) : ℝ)
            = (Nat.primeCounting' k₀ : ℝ) + (Nat.totient a₀ : ℝ) * (((n / a₀ : ℕ) : ℝ) + 1) := by
          push_cast; ring
        calc (Nat.primeCounting' (k₀ + n) : ℝ)
            ≤ ((Nat.primeCounting' k₀ + Nat.totient a₀ * (n / a₀ + 1) : ℕ) : ℝ) := by
              exact_mod_cast hlem
          _ = (Nat.primeCounting' k₀ : ℝ) + (Nat.totient a₀ : ℝ) * (((n / a₀ : ℕ) : ℝ) + 1) := hcast
          _ ≤ (Nat.primeCounting' k₀ : ℝ) + (Nat.totient a₀ : ℝ) * ((n : ℝ) / a₀ + 1) := by
              nlinarith [mul_le_mul_of_nonneg_left hd htot0]
      have ha₀pos' : (0 : ℝ) < a₀ := by exact_mod_cast ha₀pos
      have hexpand : (Nat.totient a₀ : ℝ) * ((n : ℝ) / a₀ + 1)
          = (Nat.totient a₀ : ℝ) / a₀ * n + (Nat.totient a₀ : ℝ) := by
        field_simp; ring
      have hnx : (n : ℝ) ≤ x := by exact_mod_cast (by omega : n ≤ x)
      have hεbound : (Nat.totient a₀ : ℝ) / a₀ ≤ ε := le_of_lt hdensity
      have hεpos : (0 : ℝ) ≤ ε := le_of_lt hε
      calc (Nat.primeCounting' (x + 1) : ℝ)
          = (Nat.primeCounting' (k₀ + n) : ℝ) := by rw [hn]
        _ ≤ (Nat.primeCounting' k₀ : ℝ) + (Nat.totient a₀ : ℝ) * ((n : ℝ) / a₀ + 1) := step1
        _ = (Nat.primeCounting' k₀ : ℝ) + (Nat.totient a₀ : ℝ) + (Nat.totient a₀ : ℝ) / a₀ * n := by
            rw [hexpand]; ring
        _ ≤ B + ε * n := by rw [hBdef]; nlinarith
        _ ≤ B + ε * x := by nlinarith
    set T : ℝ := max (k₀ : ℝ) (2 * (C + 1) * (B - 1) / (C + 2) + 1) with hTdef
    have hcastTendsto : Tendsto (fun k : ℕ ↦ (k : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    filter_upwards [hcastTendsto.eventually (eventually_ge_atTop T)] with k hk
    have hkk₀ : (k₀ : ℝ) ≤ (k : ℝ) := le_trans (le_max_left _ _) hk
    have hkk₀' : k₀ ≤ k := by exact_mod_cast hkk₀
    have hxcond : k₀ ≤ anchor k + 1 := by
      have := anchor_ge_add_two k
      omega
    have hbound := hπbound (anchor k) hxcond
    have hcount : (k : ℝ) + 1 ≤ (Nat.primeCounting' (anchor k + 1) : ℝ) := by
      have h := succ_le_primeCounting_anchor k
      have heq : Nat.primeCounting (anchor k) = Nat.primeCounting' (anchor k + 1) := rfl
      rw [heq] at h
      exact_mod_cast h
    have hmain : (k : ℝ) + 1 ≤ B + ε * anchor k := le_trans hcount hbound
    have hanchor_ge : ((k : ℝ) + 1 - B) / ε ≤ (anchor k : ℝ) := by
      rw [div_le_iff₀ hε]
      linarith
    have hTbig : 2 * (C + 1) * (B - 1) / (C + 2) + 1 ≤ (k : ℝ) := le_trans (le_max_right _ _) hk
    have hCp2 : (0 : ℝ) < C + 2 := by linarith
    have hTbig' : 2 * (C + 1) * (B - 1) + (C + 2) ≤ (k : ℝ) * (C + 2) := by
      have hmul := mul_le_mul_of_nonneg_right hTbig (le_of_lt hCp2)
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hCp2), one_mul] at hmul
      linarith [hmul]
    have heqdiv : ((k : ℝ) + 1 - B) / ε = 2 * (C + 1) * ((k : ℝ) + 1 - B) := by
      rw [div_eq_iff hε.ne', hεdef]
      field_simp
    have hfinal : C * (k : ℝ) ≤ ((k : ℝ) + 1 - B) / ε := by
      rw [heqdiv]
      nlinarith [hTbig', hCp2]
    have hCanchor : C * (k : ℝ) ≤ (anchor k : ℝ) := le_trans hfinal hanchor_ge
    have hkpos : (0 : ℝ) < (k : ℝ) := by
      have : 0 < k := by omega
      exact_mod_cast this
    rw [le_div_iff₀ hkpos]
    linarith [hCanchor]

end StructuralGoldbach
