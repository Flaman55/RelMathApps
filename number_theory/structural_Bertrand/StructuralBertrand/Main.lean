import StructuralBertrand.Defs
import StructuralBertrand.LPF
import StructuralBertrand.ZeroForce
import StructuralBertrand.Weight
import StructuralBertrand.GPS_StateMachine
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
/-!
# Main.lean — Theorem 5.1: Structural Bertrand–Chebyshev Bound

**Note.** `Mathlib.NumberTheory.Bertrand` (and `Nat.bertrand`) are intentionally NOT
imported. All results are derived from the structural lemmas of this project; the single
quantitative step is isolated in `Erdos.erdos_contradiction`.

## Main argument

Assume, for contradiction, that `(P_k, 2·P_k]` contains no prime.

1. Every element is composite.
2. `composites_covered_by_prev`: every composite `n` satisfies `n.minFac < P_k` or
   `n = 2·P_k`.
3. In either case `gcd(n, M') ≥ 2`, so `n` is not coprime to `M'`.
4. `exists_coprime_in_window` (via the GPS generative window = the Erdős kernel): the window
   contains an element coprime to `M'` — a contradiction.

Hence the window contains a prime.
-/

namespace StructuralBertrand

/-! ## Coprime witness in the window (`M'` pinned to the primorial) -/

/--
**Lemma** (coprime witness in the window).

For `M' = primorial_below P_k` the interval `(P_k, 2·P_k]` contains a number coprime to `M'`.

Explicit witnesses for small `M'`, and for `M' ≥ 2·P_k` the GPS generative window
(`exists_coprime_in_window_case3`), closed by the Erdős kernel.
-/
private lemma exists_coprime_in_window {P_k M' : ℕ}
    (hPk_prime : Nat.Prime P_k)
    (hPk3      : 2 < P_k)
    (hM'_pos   : 0 < M')
    (hM'_eq    : M' = primorial_below P_k)
    (hcop      : Nat.Coprime P_k M') :
    ∃ n, P_k < n ∧ n ≤ 2 * P_k ∧ Nat.Coprime n M' := by
  by_cases hle : M' ≤ P_k
  · -- M' ≤ P_k.  Witness n = P_k + M'.
    exact ⟨P_k + M', by omega, by omega, Nat.coprime_add_self_left.mpr hcop⟩
  · push_neg at hle  -- P_k < M'
    by_cases hlt : M' < 2 * P_k
    · -- P_k < M' < 2·P_k.  Witness n = M' + 1.
      refine ⟨M' + 1, by omega, by omega, ?_⟩
      rw [show M' + 1 = 1 + M' from by ring]
      exact Nat.coprime_add_self_left.mpr (by simp [Nat.Coprime])
    · -- M' ≥ 2·P_k.  GPS generative window (the Erdős kernel).
      exact exists_coprime_in_window_case3 hPk_prime hPk3 hM'_eq

/-! ## Theorem 5.1: Structural Bertrand–Chebyshev Bound -/

/--
**Theorem 5.1** (Structural Bertrand–Chebyshev Bound).

For a complete preceding base with primorial `M'` and next prime `P_k`, the interval
`(P_k, 2·P_k]` contains a prime.

The hypotheses `_hprev_wt`, `_hphi_mult`, `_hphi_pos` characterize the structural setting
(the necessary condition: weight ≥ 1). The quantitative closure is carried by the Erdős
kernel through `exists_coprime_in_window`; they are present here but not load-bearing for
this version of the proof.
-/
theorem structural_bertrand_chebyshev
    {P_k M' : ℕ}
    (hPk_prime    : Nat.Prime P_k)
    (hM'_pos      : 0 < M')
    (_hphi_pos    : 0 < Nat.totient M')
    (_hprev_wt    : WeightGeOne P_k (M' * P_k))
    (_hphi_mult   : Nat.totient (M' * P_k) = Nat.totient M' * (P_k - 1))
    (hcop         : Nat.Coprime P_k M')
    (hM'_eq       : M' = primorial_below P_k)
    (hM'_complete : ∀ p : ℕ, p.Prime → p < P_k → p ∣ M') :
    ∃ q : ℕ, P_k < q ∧ q ≤ 2 * P_k ∧ q.Prime := by
  rcases eq_or_lt_of_le hPk_prime.two_le with h2 | hPk3
  · -- P_k = 2: 3 ∈ (2, 4] is prime.
    refine ⟨3, ?_, ?_, by norm_num⟩ <;> omega
  · -- 2 < P_k.
    by_contra h_no_prime
    push_neg at h_no_prime
    obtain ⟨n, hn_lo, hn_hi, hn_cop⟩ :=
      exists_coprime_in_window hPk_prime hPk3 hM'_pos hM'_eq hcop
    have hn_not_prime : ¬ n.Prime := h_no_prime n hn_lo hn_hi
    have hn2 : 2 ≤ n := le_trans hPk_prime.two_le (Nat.le_of_lt hn_lo)
    obtain hfac | hneq :=
      composites_covered_by_prev hPk_prime hn_lo hn_hi hn2 hn_not_prime
    · -- n.minFac < P_k ⇒ n.minFac ∣ M' ⇒ n.minFac ∣ gcd(n,M') = 1, contradiction.
      have hf_prime  : n.minFac.Prime := Nat.minFac_prime (by omega)
      have hf_dvd_M' : n.minFac ∣ M' := hM'_complete n.minFac hf_prime hfac
      have hf_dvd_gcd : n.minFac ∣ Nat.gcd n M' :=
        Nat.dvd_gcd (Nat.minFac_dvd n) hf_dvd_M'
      rw [hn_cop] at hf_dvd_gcd
      exact absurd (Nat.le_of_dvd (by norm_num) hf_dvd_gcd) (by linarith [hf_prime.two_le])
    · -- n = 2·P_k ⇒ 2 ∣ M' and 2 ∣ n ⇒ 2 ∣ gcd = 1, contradiction.
      have h2_dvd_M' : 2 ∣ M' := hM'_complete 2 (by norm_num) hPk3
      have h2_dvd_n  : 2 ∣ n  := ⟨P_k, hneq⟩
      have h2_dvd_gcd : 2 ∣ Nat.gcd n M' := Nat.dvd_gcd h2_dvd_n h2_dvd_M'
      rw [hn_cop] at h2_dvd_gcd
      exact absurd h2_dvd_gcd (by norm_num)

/-! ## Reduction: the largest prime `≤ N` -/

/-- There exists a largest prime `≤ N` (for `N ≥ 2`), with no primes in `(P, N]`. -/
lemma exists_largest_prime_le {N : ℕ} (hN : 2 ≤ N) :
    ∃ P, Nat.Prime P ∧ P ≤ N ∧ ∀ m, P < m → m ≤ N → ¬ Nat.Prime m := by
  have h2mem : 2 ∈ (Finset.range (N + 1)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by norm_num⟩
  have hne : ((Finset.range (N + 1)).filter Nat.Prime).Nonempty := ⟨2, h2mem⟩
  set P := ((Finset.range (N + 1)).filter Nat.Prime).max' hne with hP
  have hPmem : P ∈ (Finset.range (N + 1)).filter Nat.Prime := by
    rw [hP]; exact Finset.max'_mem _ hne
  rw [Finset.mem_filter, Finset.mem_range] at hPmem
  obtain ⟨hPlt, hPp⟩ := hPmem
  refine ⟨P, hPp, by omega, ?_⟩
  intro m hlt hle hm
  have hmmem : m ∈ (Finset.range (N + 1)).filter Nat.Prime := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hm⟩
  have hle2 : m ≤ P := by rw [hP]; exact Finset.le_max' _ m hmmem
  omega

/--
**Corollary 6.1** (Classical Bertrand–Chebyshev).

For every `N > 1` there is a prime `p` with `N < p ≤ 2·N`.

Structural proof (without `Nat.bertrand`): let `P_k` be the largest prime `≤ N`;
`prime_in_window` gives a prime `q ∈ (P_k, 2·P_k]`; maximality of `P_k` yields `q > N`, and
`P_k ≤ N` yields `q ≤ 2·N`.
-/
theorem bertrand_chebyshev (N : ℕ) (hN : 1 < N) :
    ∃ p : ℕ, N < p ∧ p ≤ 2 * N ∧ p.Prime := by
  obtain ⟨P_k, hP_prime, hP_le, hP_max⟩ := exists_largest_prime_le (by omega : 2 ≤ N)
  rcases eq_or_lt_of_le hP_prime.two_le with h2 | hP3
  · -- P_k = 2 ⇒ no primes in (2, N] ⇒ N = 2 (else 3 would be a prime ≤ N for N ≥ 3).
    have hNeq : N = 2 := by
      by_contra hne
      exact hP_max 3 (by omega) (by omega) (by norm_num)
    subst hNeq
    exact ⟨3, by norm_num, by norm_num, by norm_num⟩
  · -- 2 < P_k: use the prime window of P_k.
    obtain ⟨q, hq_lo, hq_hi, hq_prime⟩ := prime_in_window hP_prime hP3
    have hqN : N < q := by
      by_contra hqN'
      push_neg at hqN'
      exact hP_max q hq_lo hqN' hq_prime
    exact ⟨q, hqN, by omega, hq_prime⟩

end StructuralBertrand
