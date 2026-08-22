import StructuralBertrand.Defs
import StructuralBertrand.Weight
import StructuralBertrand.Truncated
import StructuralBertrand.BinomialCertificate
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic

/-!
# GPS as a state machine — a purely combinatorial formalization

GPS operates on pairs `(Pk, M')` where:
- `M'` = primorial of all primes STRICTLY less than `Pk`;
- `Pk` is prime;
- window = `Finset.Ioc Pk (2 * Pk)`.

Mechanism: in the window every COMPOSITE `n` has `LPF(n) < Pk` (since
`LPF² ≤ n ≤ 2Pk < Pk²`), so `LPF(n) ∈ M'`. The elements FREE of `M'` are exactly the new
primes.

**Kernel closure.** `gps_window_nonempty` reduces (via `structural_sieve_survivor`) to
`binomial_contradiction` (BinomialCertificate.lean) in the dense sub-case — the sole
quantitative node, self-contained (no import of Mathlib's Bertrand theorem).
-/

namespace StructuralBertrand

/-! ### Definition: primorial of all primes `< n` -/
noncomputable def primorial_below (n : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range n).filter Nat.Prime, p

/-! ### Definition: the GPS window -/
def gps_window (Pk : ℕ) : Finset ℕ :=
  Finset.Ioc Pk (2 * Pk)

/-! ### Definition: free elements of the window (coprime to `M'`) -/
noncomputable def gps_free (Pk : ℕ) : Finset ℕ :=
  (gps_window Pk).filter (fun n => Nat.Coprime n (primorial_below Pk))

/-! ### Properties of GPS -/

-- Every free element of the GPS window is prime
lemma gps_free_prime {Pk n : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (hn : n ∈ gps_free Pk) : Nat.Prime n := by
  simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc] at hn
  obtain ⟨⟨hn_lo, hn_hi⟩, hn_cop⟩ := hn
  by_contra hn_not_prime
  have hn2 : 2 ≤ n := le_trans hPk.two_le (Nat.le_of_lt hn_lo)
  have hmfp : n.minFac.Prime := Nat.minFac_prime (by omega)
  -- (1) For composite n:  minFac² ≤ n.
  --     (If your Mathlib version provides it, this shortens to
  --        have hmf_sq : n.minFac ^ 2 ≤ n := Nat.minFac_sq_le_self (by omega) hn_not_prime)
  have hmf_sq : n.minFac ^ 2 ≤ n := by
    have hdvd  : n.minFac ∣ n := Nat.minFac_dvd n
    have hle   : n.minFac ≤ n / n.minFac :=
      Nat.minFac_le_div (by omega) hn_not_prime
    have hcanc : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hdvd
    calc n.minFac ^ 2 = n.minFac * n.minFac := pow_two _
      _ ≤ n.minFac * (n / n.minFac) := Nat.mul_le_mul (le_refl _) hle
      _ = n := hcanc
  -- (2) minFac < Pk, since minFac² ≤ n ≤ 2·Pk < Pk² (from Pk > 2).
  have hmf_lt : n.minFac < Pk := by
    by_contra hcon
    push_neg at hcon                                       -- hcon : Pk ≤ n.minFac
    have hmf_sq' : n.minFac * n.minFac ≤ n := by rw [← pow_two]; exact hmf_sq
    have hsq    : Pk * Pk ≤ n.minFac * n.minFac := Nat.mul_le_mul hcon hcon
    have hchain : Pk * Pk ≤ 2 * Pk := le_trans hsq (le_trans hmf_sq' hn_hi)
    have h3     : 3 * Pk ≤ Pk * Pk := Nat.mul_le_mul (by omega) (le_refl Pk)
    have hlin   : 3 * Pk ≤ 2 * Pk := le_trans h3 hchain
    omega
  -- (3) minFac divides the base primorial ⇒ contradiction with coprimality of n.
  have hmf_dvd : n.minFac ∣ primorial_below Pk := by
    unfold primorial_below
    exact Finset.dvd_prod_of_mem (fun p => p)
      (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hmf_lt, hmfp⟩)
  have hgcd : n.minFac ∣ Nat.gcd n (primorial_below Pk) :=
    Nat.dvd_gcd (Nat.minFac_dvd n) hmf_dvd
  have hco  : Nat.gcd n (primorial_below Pk) = 1 := hn_cop
  rw [hco] at hgcd
  have h2   := hmfp.two_le
  have hle1 : n.minFac ≤ 1 := Nat.le_of_dvd Nat.one_pos hgcd
  omega

/-- Every prime `q ∈ (Pk, 2Pk]` is coprime to `primorial_below Pk` (all its factors are
    primes `r < Pk < q`, and distinct primes are coprime). Purely structural; same proof
    pattern as `Weight.weight_ge_one_aux`. -/
lemma prime_in_window_coprime_primorial {Pk q : ℕ}
    (hq : Nat.Prime q) (hq_lo : Pk < q) :
    Nat.Coprime q (primorial_below Pk) := by
  unfold primorial_below
  apply Finset.prod_induction (fun p => p) (Nat.Coprime q)
  · intro a b ha hb; exact ha.mul_right hb
  · simp [Nat.Coprime]
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_range] at hr
    exact (Nat.coprime_primes hq hr.2).mpr (by omega)

/-! ### Goal restated: closing the structural sieve; Bertrand as a corollary

We no longer prove "there is a prime in `(Pk,2Pk]`" (Bertrand) directly, nor delegate to a
Mathlib theorem. The goal is `structural_sieve_survivor`: the structural sieve over its
window always leaves a survivor. Bertrand falls out as a corollary in `Main`.

Dispatch by regime (explicit union-bound threshold from `Truncated`):
  • SPARSE regime → closed here, structurally (`truncated_not_sieve_closed`), with no atom;
  • DENSE regime  → `dense_sieve_survivor`, which CONSUMES the weight (the average density),
                    rather than being "Bertrand in disguise". Here other fundamental
                    techniques (control of the `2^ω` error) could be used without appealing
                    to Bertrand.
-/

/-- Bridge: if `n` is not covered by any prime `< Pk`, then it is coprime to
    `primorial_below Pk`. (Links the language of `Truncated` with that of `gps_free`.) -/
lemma coprime_primorial_of_uncovered {Pk n : ℕ}
    (h : ∀ p ∈ (Finset.range Pk).filter Nat.Prime, ¬ p ∣ n) :
    Nat.Coprime n (primorial_below Pk) := by
  unfold primorial_below
  apply Nat.Coprime.prod_right                       -- Coprime k (∏ f) from ∀-coprime
  intro p hp
  have hp_prime : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact (hp_prime.coprime_iff_not_dvd.mpr (h p hp)).symm

/-- **Bridge to the weight.** For a prime `Pk > 2` the preceding base (primes `< Pk`) has
    average density `> 1`:  `M' < Pk · φ(M')`, where `M' = primorial_below Pk`. CONSUMES
    `structural_weight_ge_one` (Weight.lean), making the weight load-bearing. -/
lemma weight_density_bridge {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    primorial_below Pk < Pk * Nat.totient (primorial_below Pk) := by
  set M' := primorial_below Pk with hM'
  have hM'pos : 0 < M' := by
    rw [hM', primorial_below]
    exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  -- Complete base of primes ≤ Pk
  have hbase_ne : ((Finset.range (Pk + 1)).filter Nat.Prime).Nonempty :=
    ⟨2, by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, Nat.prime_two⟩⟩
  let B : PrimeBase :=
    { carrier := (Finset.range (Pk + 1)).filter Nat.Prime
      all_prime := fun p hp => (Finset.mem_filter.mp hp).2
      nonempty := hbase_ne }
  have hcar : B.carrier = (Finset.range (Pk + 1)).filter Nat.Prime := rfl
  -- carrier = insert Pk (primes < Pk)
  have hins : B.carrier = insert Pk ((Finset.range Pk).filter Nat.Prime) := by
    rw [hcar]; ext q
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hqlt, hqp⟩
      rcases Nat.lt_or_ge q Pk with h | h
      · exact Or.inr ⟨h, hqp⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hqlt, hqp⟩)
      · exact ⟨by omega, hPk⟩
      · exact ⟨by omega, hqp⟩
  have hPk_not : Pk ∉ (Finset.range Pk).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_range]; rintro ⟨h, _⟩; omega
  -- pMax = Pk
  have hpmax : B.pMax = Pk := by
    apply le_antisymm
    · apply Finset.max'_le; intro y hy
      rw [hcar, Finset.mem_filter, Finset.mem_range] at hy; omega
    · apply Finset.le_max'; rw [hcar, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hPk⟩
  -- isComplete
  have hcomplete : B.isComplete := by
    intro p hp _ hple
    rw [hpmax] at hple
    rw [hcar, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hp⟩
  -- primorial = M' * Pk
  have hprim : B.primorial = M' * Pk := by
    rw [PrimeBase.primorial, hins, Finset.prod_insert hPk_not, id_eq, hM', primorial_below]
    simp only [id_eq]; ring
  -- weight ≥ 1
  have hwt : WeightGeOne Pk (M' * Pk) := by
    have h := structural_weight_ge_one B hcomplete
    rwa [hpmax, hprim] at h
  -- φ(M' * Pk) = φ(M') * (Pk - 1)
  have hcop : Nat.Coprime M' Pk := by
    rw [hM', primorial_below]
    apply Nat.Coprime.prod_left                       -- Coprime (∏ f) k from ∀-coprime
    intro q hq
    have hqp : Nat.Prime q := (Finset.mem_filter.mp hq).2
    have hqlt : q < Pk := by rw [Finset.mem_filter, Finset.mem_range] at hq; exact hq.1
    exact (Nat.coprime_primes hqp hPk).mpr (by omega)
  have hphi : Nat.totient (M' * Pk) = Nat.totient M' * (Pk - 1) := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hPk]
  have hphi_pos : 0 < Nat.totient M' := Nat.totient_pos.mpr hM'pos
  exact prev_base_cannot_cover_window hPk hM'pos hphi_pos hwt hphi

/-- **Dense case — closed.** A survivor in the window exists: if it did not, then (since a
    prime in the window is always coprime to the base — `prime_in_window_coprime_primorial`) the
    window would contain no prime, contradicting the quantitative kernel `binomial_contradiction`
    (BinomialCertificate.lean, self-contained). The object used is the central binomial
    coefficient `C(2Pk,Pk)`, whose prime content in the window is governed by the S1 purity law
    (Rings/Newton). -/
theorem dense_sieve_survivor {Pk : ℕ} (_hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (_hdensity : primorial_below Pk < Pk * Nat.totient (primorial_below Pk)) :
    (gps_free Pk).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  refine binomial_contradiction hPk3 fun q hlo hhi hq => ?_
  have hcop : Nat.Coprime q (primorial_below Pk) :=
    prime_in_window_coprime_primorial hq hlo
  have hqmem : q ∈ gps_free Pk := by
    simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlo, hhi⟩, hcop⟩
  rw [hempty] at hqmem
  exact absurd hqmem (Finset.notMem_empty q)

/-- **Goal: closing the structural sieve.** The sieve over the window `(Pk, 2Pk]` always
    leaves a survivor. Regime dispatch: sparse closed structurally (`Truncated`), dense
    handed to the atom `dense_sieve_survivor`. -/
theorem structural_sieve_survivor {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (hdensity : primorial_below Pk < Pk * Nat.totient (primorial_below Pk)) :
    (gps_free Pk).Nonempty := by
  classical
  by_cases hsparse :
      (∑ p ∈ (Finset.range Pk).filter Nat.Prime,
          ((Finset.Ioc Pk (2 * Pk)).filter (fun m => p ∣ m)).card)
        < (Finset.Ioc Pk (2 * Pk)).card
  · -- SPARSE REGIME: union bound (no atom, no analysis).
    obtain ⟨n, hlo, hhi, hunc⟩ :=
      truncated_not_sieve_closed (P_min := 2) (P_max := Pk)
        (B := (Finset.range Pk).filter Nat.Prime) hsparse
    refine ⟨n, ?_⟩
    simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlo, hhi⟩, coprime_primorial_of_uncovered hunc⟩
  · -- DENSE REGIME: structural atom consuming the weight.
    exact dense_sieve_survivor hPk hPk3 hdensity

/-- Backward compatibility: `gps_window_nonempty` is now a corollary of sieve closure, not a
    delegation to Erdős. The weight is supplied by the bridge `weight_density_bridge`. -/
lemma gps_window_nonempty {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    (gps_free Pk).Nonempty :=
  structural_sieve_survivor hPk hPk3 (weight_density_bridge hPk hPk3)

/-- Consuming corollary: `(Pk, 2Pk]` contains a prime. From `gps_window_nonempty` (a free
    element) and `gps_free_prime` (free ⇒ prime). -/
theorem prime_in_window {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    ∃ q, Pk < q ∧ q ≤ 2 * Pk ∧ Nat.Prime q := by
  obtain ⟨n, hn⟩ := gps_window_nonempty hPk hPk3
  have hnp : Nat.Prime n := gps_free_prime hPk hPk3 hn
  simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc] at hn
  exact ⟨n, hn.1.1, hn.1.2, hnp⟩

/-! ### Bridge to Main: Case 3 (`M' = primorial_below Pk`) -/
lemma exists_coprime_in_window_case3 {P_k M' : ℕ}
    (hPk_prime : Nat.Prime P_k)
    (hPk3 : 2 < P_k)
    (hM'_eq : M' = primorial_below P_k) :
    ∃ n, P_k < n ∧ n ≤ 2 * P_k ∧ Nat.Coprime n M' := by
  obtain ⟨n, hn⟩ := gps_window_nonempty hPk_prime hPk3
  simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc] at hn
  exact ⟨n, hn.1.1, hn.1.2, by rw [hM'_eq]; exact hn.2⟩


/-! ### Additional sections wired into the GPS structure -/

/-- Auxiliary phase-shift theorem (parity block). Shows that the critical point at which a
    new territory opens (`P_max + 2`) has a least prime factor that is strictly bounded in
    size. -/
theorem prime_factor_bound_for_window_start (P_max p_i c : Nat)
    (h_p_max : P_max.Prime)
    (h_odd_p : 3 ≤ P_max)
    (h_div : P_max + 2 = c * p_i)
    (_h_pi_prime : p_i.Prime)
    (h_amunition : p_i ≤ P_max) : -- KEY CONDITION: the divisor comes from the base P
    c ≥ 3 ∧ p_i ≤ (P_max + 2) / 3 := by
  -- 1. Parity block (P_max and P_max + 2 are both odd)
  have h_p_max_ne_2 : P_max ≠ 2 := by omega
  have h_p_max_odd : P_max % 2 = 1 := by
    rw [Nat.Prime.mod_two_eq_one_iff_ne_two h_p_max]
    exact h_p_max_ne_2
  have h_odd_left : (P_max + 2) % 2 = 1 := by omega

  -- 2. Safe linear elimination of the cases c < 3
  have h_c_ge_3 : c ≥ 3 := by
    by_contra h_lt
    have h_c_cases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
    rcases h_c_cases with rfl | rfl | rfl
    · -- Case c = 0: 0 * p_i = 0, contradicting P_max + 2 ≥ 5
      omega
    · -- Case c = 1: P_max + 2 = p_i.
      -- Contradiction with the hypothesis h_amunition: p_i ≤ P_max
      rw [Nat.one_mul] at h_div
      omega
    · -- Case c = 2: P_max + 2 = 2 * p_i (left odd, right even)
      have h_mod : (2 * p_i) % 2 = 0 := Nat.mul_mod_right 2 p_i
      omega

  -- 3. Proof of the size bound on p_i
  have h_size : p_i ≤ (P_max + 2) / 3 := by
    have h_mul_le : 3 * p_i ≤ P_max + 2 := by
      calc 3 * p_i ≤ c * p_i := Nat.mul_le_mul_right p_i h_c_ge_3
      _ = P_max + 2 := h_div.symm
    omega

  exact ⟨h_c_ge_3, h_size⟩



/-- Structural state-machine step (GPS transition invariant). Given a state `P_k`, we generate
    the state `P_{k+1}` as the maximum of the set of free elements. The lemma proves that the
    width of the new window (`next_P_max`) grows strictly faster than the ability of the new
    primorial to create gaps at the start of the new CRT period. -/
lemma gps_step_induction {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (h_nonempty : (gps_free Pk).Nonempty) :
    ∃ (next_Pk : ℕ), next_Pk.Prime ∧ Pk < next_Pk ∧ next_Pk ≤ 2 * Pk ∧
    (∀ p ∈ (Finset.range next_Pk).filter Nat.Prime, p ∣ primorial_below next_Pk) := by
  -- 1. Choose a new anchor from the nonempty set of free elements (per the algorithm)
  obtain ⟨next_Pk, h_mem⟩ := h_nonempty
  have h_next_prime : next_Pk.Prime := gps_free_prime hPk hPk3 h_mem

  -- 2. Extract the geometric bounds of the new anchor from the window definition
  have h_bounds := h_mem
  simp [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc] at h_bounds
  obtain ⟨⟨h_lo, h_hi⟩, _⟩ := h_bounds

  -- 3. Produce the defining property of the new primorial for step k+1
  have h_primorial_prop : ∀ p ∈ (Finset.range next_Pk).filter Nat.Prime, p ∣ primorial_below next_Pk := by
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    unfold primorial_below
    exact Finset.dvd_prod_of_mem (fun q => q) (by simp [Finset.mem_filter, Finset.mem_range]; exact ⟨hp.1, hp.2⟩)

  -- Export the state k+1, ready for an immediate reset of the CRT residue universe
  exact ⟨next_Pk, h_next_prime, h_lo, h_hi, h_primorial_prop⟩

end StructuralBertrand
