import StructuralBertrand.Defs
import StructuralBertrand.LPF
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
/-!
# ZeroForce.lean — Lemma 4.3: Zero Effective Force

When P_k is added to a complete generative base, it contributes **zero new coverage**
to its own window `(P_k, 2·P_k]`.

**Reason**: the only multiple of P_k in `(P_k, 2·P_k]` is `2·P_k = 2 · P_k`,
which is already divisible by `2` — the minimal prime, always present in the
preceding base `𝒫' = {P_1, …, P_{k−1}}`.

**Corollary** (exact, no approximation):
  `n ∈ (P_k, 2·P_k]` is composite  ↔  `n.minFac < P_k`  or  `n = 2·P_k`.
In both cases `n` is already covered by `𝒫'`.
Hence composites in the window are **exactly** the elements covered by the
preceding base `𝒫'`.
-/

namespace StructuralBertrand

/-! ## Lemma 4.3: Zero Effective Force -/

/--
**Lemma 4.3** (Zero Effective Force).

The only multiple of an odd prime `P_k` in the window `(P_k, 2·P_k]` is `2·P_k`.
Since `2 ∣ 2·P_k`, this element is covered by the factor `2` already present in
the preceding base.  Therefore `P_k` adds no new coverage to its own window.
-/
theorem zero_effective_force
    {P_k : ℕ} (hP : Nat.Prime P_k)
    {n : ℕ}
    (hn_lo  : P_k < n)
    (hn_hi  : n ≤ 2 * P_k)
    (hdvd   : P_k ∣ n) :
    n = 2 * P_k := by
  obtain ⟨j, hj⟩ := hdvd
  -- P_k * j = n, with P_k < P_k * j ≤ 2 * P_k
  have hj_lo : 1 < j := by
    rcases j with _ | _ | j
    · simp at hj; omega
    · simp at hj; omega
    · omega
  have hj_hi : j ≤ 2 := by
    have hPk_pos : 0 < P_k := hP.pos
    nlinarith [hj ▸ hn_hi]
  have hj2 : j = 2 := by omega
  subst hj2; linarith

/--
**Corollary 4.4** (Composites are covered by the preceding base).

For every composite `n ∈ (P_k, 2·P_k]`, either:
- `n.minFac < P_k`  (covered by a prime strictly smaller than P_k, hence in 𝒫'), or
- `n = 2·P_k`       (covered by `2`, the minimal element of 𝒫').

In either case `n` is sieve-covered by the preceding base `𝒫'`.
This result is **exact** — it uses only divisibility, not density.
-/
theorem composites_covered_by_prev
    {P_k : ℕ} (hP : Nat.Prime P_k)
    {n : ℕ}
    (hn_lo   : P_k < n)
    (hn_hi   : n ≤ 2 * P_k)
    (hn2     : 2 ≤ n)
    (hn_comp : ¬ n.Prime) :
    n.minFac < P_k ∨ n = 2 * P_k := by
  -- n is composite, so n.minFac ≤ P_k by LPF (with P_min = P_k ≤ P_max = P_k, window ≤ P_k²)
  have hfac_le : n.minFac ≤ P_k :=
    least_prime_factor_bound hP.pos le_rfl hn_lo (by nlinarith [hP.two_le]) hn2 hn_comp
  -- Either n.minFac < P_k (strictly inside 𝒫') or n.minFac = P_k
  rcases lt_or_eq_of_le hfac_le with h | h
  · exact Or.inl h
  · -- n.minFac = P_k means P_k ∣ n
    right
    have hdvd : P_k ∣ n := h ▸ Nat.minFac_dvd n
    exact zero_effective_force hP hn_lo hn_hi hdvd

/--
**Remark**: the converse also holds.

Any element `n ∈ (P_k, 2·P_k]` with `n.minFac > P_k` must be prime
(Corollary 3.2).  Combined with `composites_covered_by_prev`, we obtain
the exact characterization:
  `n ∈ (P_k, 2·P_k]` is prime  ↔  `n` is NOT covered by the preceding base `𝒫'`.
-/
theorem prime_iff_uncovered_by_prev
    {P_k : ℕ} (hP : Nat.Prime P_k)
    {n : ℕ}
    (hn_lo : P_k < n)
    (hn_hi : n ≤ 2 * P_k)
    (hn2   : 2 ≤ n) :
    n.Prime ↔ ¬ SieveCovered P_k n := by
  constructor
  · -- prime → uncovered: a prime > P_k has minFac = itself > P_k
    intro hn_prime
    simp only [SieveCovered, not_le]
    rw [Nat.Prime.minFac_eq hn_prime]
    exact hn_lo
  · -- uncovered → prime: by Corollary 3.2 (LPF contrapositive)
    intro huncov
    exact uncovered_is_prime hP.pos le_rfl hn_lo (by nlinarith [hP.two_le]) hn2 huncov

end StructuralBertrand
