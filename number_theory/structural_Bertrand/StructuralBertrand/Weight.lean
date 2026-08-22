import StructuralBertrand.Defs
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
/-!
# Weight.lean — Lemma 4.4: Structural Weight w(𝒫) ≥ 1

The *structural weight* of a complete generative base `𝒫 = {P_1, …, P_k}` is:
  `w(𝒫) = P_k · φ(M) / M = P_k · ∏_{p ∈ 𝒫} (1 − 1/p)`

where `M = ∏_{p ∈ 𝒫} p` is the primorial.

In integer form: `P_k · φ(M) ≥ M`, i.e., `w(𝒫) ≥ 1`.

**Proof by induction**:
- Base (`k = 1`, `P_1 = 2`): `w = 2 · φ(2)/2 = 2 · 1/2 = 1 ≥ 1`. ✓
- Step: `w(𝒫) = (P_k − 1)/P_{k−1} · w(𝒫')`.
  Since `P_k ≥ P_{k−1} + 2` for consecutive odd primes, `(P_k−1)/P_{k−1} ≥ 1`,
  so `w(𝒫) ≥ w(𝒫') ≥ 1`.

**Key Corollary** (preceding base in current window):
  `P_k · φ(M') / M' = (P_k / (P_k − 1)) · w(𝒫) ≥ P_k / (P_k − 1) > 1`
The preceding base `𝒫'` leaves strictly more than 1 element uncovered
(in density terms) in any window of size `P_k`.
-/

namespace StructuralBertrand

/-! ## Integer formulation of w(𝒫) ≥ 1 -/

/--
The structural weight condition in integer arithmetic:
`P_max · φ(M) ≥ M`, equivalent to `w(𝒫) = P_max · φ(M)/M ≥ 1`.

We work with integers to avoid division.  The rational inequality `w ≥ 1`
is equivalent to `P_max * φ(M) ≥ M` over ℕ.
-/
def WeightGeOne (P_max M : ℕ) : Prop :=
  M ≤ P_max * Nat.totient M

/-! ## Base case -/

/--
Base case: for the base `{2}`, `M = 2`, `φ(2) = 1`, `P_max = 2`.
`w = 2 · 1 / 2 = 1 ≥ 1`. ✓
-/
theorem weight_base : WeightGeOne 2 2 := by
  unfold WeightGeOne
  rw [Nat.totient_prime (by norm_num : Nat.Prime 2)]

/-! ## Inductive step -/

/--
When extending base `𝒫'` (with primorial `M'` and max prime `P_prev`) by
a new prime `P_k > P_prev`, the new primorial is `M = M' · P_k` and
`φ(M) = φ(M') · (P_k − 1)`.

The new weight satisfies:
  `P_k · φ(M) = P_k · φ(M') · (P_k − 1)`
  `M           = M' · P_k`
So `WeightGeOne P_k M ↔ M' · P_k ≤ P_k · φ(M') · (P_k − 1)`.

Since `P_k ≥ 2`, dividing both sides by `P_k` gives:
  `M' ≤ φ(M') · (P_k − 1)`
And since `P_k − 1 ≥ P_prev ≥ 1` and `WeightGeOne P_prev M'`, this holds.
-/
theorem weight_step
    {P_prev P_k M' : ℕ}
    (_hPprev_prime : Nat.Prime P_prev)
    (hPk_prime    : Nat.Prime P_k)
    (hPk_gt       : P_prev < P_k)
    (_hM'_pos     : 0 < M')
    (_hcoprime    : Nat.Coprime P_k M')
    (hphi_mult    : Nat.totient (M' * P_k) = Nat.totient M' * (P_k - 1))
    (hprev_weight : WeightGeOne P_prev M') :
    WeightGeOne P_k (M' * P_k) := by
  simp [WeightGeOne, hphi_mult]
  -- Goal: M' * P_k ≤ P_k * (φ(M') * (P_k - 1))
  -- Equivalently: M' ≤ φ(M') * (P_k - 1)  [divide both sides by P_k > 0]
  have hPk_pos : 0 < P_k := hPk_prime.pos
  rw [show P_k * (Nat.totient M' * (P_k - 1)) = P_k * Nat.totient M' * (P_k - 1) by ring]
  -- M' * P_k ≤ P_k * φ(M') * (P_k - 1)
  have h1 : M' ≤ P_prev * Nat.totient M' := hprev_weight
  have h2 : P_prev ≤ P_k - 1 := by omega
  have h3 : P_prev * Nat.totient M' ≤ (P_k - 1) * Nat.totient M' :=
    Nat.mul_le_mul_right _ h2
  have h4 : M' ≤ (P_k - 1) * Nat.totient M' := le_trans h1 h3
  nlinarith

/-! ## Main weight lemma -/

/--
**Lemma 4.4** (Structural Weight).

For any complete generative prime base `𝒫 = {P_1, …, P_k}` with primorial `M`,
`P_k · φ(M) ≥ M`  (i.e., `w(𝒫) ≥ 1`).

The proof is by induction on the generative process, using `weight_step` at
each extension.  The base case is `weight_base`.

Induction on the cardinality of a finite prime set.
For every nonempty Finset `s` of primes, `WeightGeOne (s.max') (s.prod id)`.

* card = 1 : single prime p — `WeightGeOne p p` since p ≤ p·(p−1) for p ≥ 2.
* card = n+1 : peel off the max prime p, apply IH to `s.erase p`,
               then close with `weight_step`.
-/
private lemma weight_ge_one_aux :
    ∀ (n : ℕ) (s : Finset ℕ) (hs : s.Nonempty),
    s.card = n → (∀ p ∈ s, Nat.Prime p) →
    WeightGeOne (s.max' hs) (s.prod id) := by
  intro n
  induction n with
  | zero =>
    intro s hs hcard _
    exact absurd (Finset.card_pos.mpr hs) (by omega)
  | succ n ih =>
    intro s hs hcard hprime
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- Base case: card = 1, single prime
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hcard
      simp only [Finset.max'_singleton, Finset.prod_singleton, id_eq]
      have hp : Nat.Prime p := hprime p (Finset.mem_singleton_self p)
      have h2 : 2 ≤ p := hp.two_le
      unfold WeightGeOne
      rw [Nat.totient_prime hp]
      -- p ≤ p * (p - 1): p - 1 ≥ 1 since p ≥ 2
      calc p = p * 1       := (Nat.mul_one p).symm
           _ ≤ p * (p - 1) := Nat.mul_le_mul_left p (by omega)
    · -- Inductive step: card = n + 1 ≥ 2; peel off the maximum prime
      have hp_mem   : s.max' hs ∈ s           := Finset.max'_mem s hs
      have hp_prime : Nat.Prime (s.max' hs)   := hprime _ hp_mem
      set s' := s.erase (s.max' hs)
      -- s' has card n and is nonempty (n ≥ 1)
      have hs'_card : s'.card = n := by
        -- avoid ℕ subtraction: show s'.card + 1 = s.card via insert_erase
        have h : s'.card + 1 = s.card := by
          rw [← Finset.card_insert_of_notMem (Finset.notMem_erase _ _),
              Finset.insert_erase hp_mem]
        omega
      have hs'_ne   : s'.Nonempty            := Finset.card_pos.mp (by omega)
      have hprime'  : ∀ q ∈ s', Nat.Prime q :=
        fun q hq => hprime q (Finset.mem_of_mem_erase hq)
      -- IH applied to the smaller set
      have ih' : WeightGeOne (s'.max' hs'_ne) (s'.prod id) :=
        ih s' hs'_ne hs'_card hprime'
      -- Factoring: s.prod id = s'.prod id * s.max'
      have hprod : s.prod id = s'.prod id * s.max' hs := by
        conv_lhs => rw [← Finset.insert_erase hp_mem]
        rw [Finset.prod_insert (Finset.notMem_erase _ _), id_eq]; ring
      -- s'.max' < s.max' (every element of s' is strictly less than s.max')
      have hmax_lt : s'.max' hs'_ne < s.max' hs :=
        lt_of_le_of_ne
          (Finset.le_max' s _ (Finset.mem_of_mem_erase (Finset.max'_mem s' hs'_ne)))
          (Finset.mem_erase.mp (Finset.max'_mem s' hs'_ne)).1
      -- Coprimality: s.max' is prime and strictly greater than every q ∈ s',
      -- so s.max' cannot divide any q ∈ s', hence gcd(s.max', s'.prod id) = 1.
      have hcop : Nat.Coprime (s.max' hs) (s'.prod id) := by
        apply Finset.prod_induction id (Nat.Coprime (s.max' hs))
        · intro a b ha hb; exact ha.mul_right hb
        · simp [Nat.Coprime]
        · intro q hq
          have hq_lt : q < s.max' hs :=
            lt_of_le_of_ne
              (Finset.le_max' s q (Finset.mem_of_mem_erase hq))
              (Finset.mem_erase.mp hq).1
          exact hp_prime.coprime_iff_not_dvd.mpr
            fun hdvd => absurd (Nat.le_of_dvd (hprime' q hq).pos hdvd) (by omega)
      -- Totient factoring: φ(s'.prod id * s.max') = φ(s'.prod id) · (s.max' − 1)
      have hphi : Nat.totient (s'.prod id * s.max' hs) =
          Nat.totient (s'.prod id) * (s.max' hs - 1) := by
        rw [Nat.totient_mul hcop.symm, Nat.totient_prime hp_prime]
      -- Conclude via weight_step
      rw [hprod]
      exact weight_step
        (hprime' (s'.max' hs'_ne) (Finset.max'_mem s' hs'_ne))
        hp_prime hmax_lt
        (Finset.prod_pos (fun q hq => (hprime' q hq).pos))
        hcop hphi ih'

theorem structural_weight_ge_one
    (B : PrimeBase) (_ : B.isComplete) :
    WeightGeOne B.pMax B.primorial :=
  weight_ge_one_aux B.carrier.card B.carrier B.nonempty rfl B.all_prime

/-! ## Corollary: preceding base weight in current window -/

/--
**Corollary** (Preceding base weight in current window).

If `WeightGeOne P_k M` holds, then the *preceding* base with primorial `M' = M / P_k`
and `φ(M') = φ(M) / (P_k − 1)` satisfies:
  `P_k · φ(M') / M' = (P_k / (P_k − 1)) · w(𝒫) ≥ P_k / (P_k − 1) > 1`

In integer form: `M' < P_k · φ(M')`, i.e., the preceding base cannot cover
all `P_k` elements of the window.
-/
theorem prev_base_cannot_cover_window
    {P_k M' : ℕ}
    (hPk_prime : Nat.Prime P_k)
    (_hM'_pos  : 0 < M')
    (hphi_pos  : 0 < Nat.totient M')
    (hprev_wt  : WeightGeOne P_k (M' * P_k))
    (hphi_mult : Nat.totient (M' * P_k) = Nat.totient M' * (P_k - 1)) :
    M' < P_k * Nat.totient M' := by
  simp [WeightGeOne, hphi_mult] at hprev_wt
  -- hprev_wt : M' * P_k ≤ P_k * (M'.totient * (P_k - 1))
  have hPk_pos : 0 < P_k := hPk_prime.pos
  have hPk_ge2 : 2 ≤ P_k := hPk_prime.two_le
  by_contra h_ge
  push_neg at h_ge
  -- h_ge : P_k * M'.totient ≤ M'
  have h1 : P_k * Nat.totient M' * P_k ≤ M' * P_k :=
    Nat.mul_le_mul_right P_k h_ge
  have h2 : M' * P_k ≤ P_k * Nat.totient M' * (P_k - 1) := by
    have heq : P_k * (Nat.totient M' * (P_k - 1)) = P_k * Nat.totient M' * (P_k - 1) := by ring
    linarith
  have h3 : P_k * Nat.totient M' * (P_k - 1) < P_k * Nat.totient M' * P_k :=
    Nat.mul_lt_mul_of_pos_left (by omega) (mul_pos hPk_pos hphi_pos)
  linarith

end StructuralBertrand
