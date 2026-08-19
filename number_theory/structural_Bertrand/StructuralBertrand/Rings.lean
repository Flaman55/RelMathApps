import StructuralBertrand.GPS_StateMachine
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Tactic

/-!
# Rings.lean — a residue/divisibility reformulation of the sieve

A restatement of the sieve in terms of residues modulo the base primes. It is logically
equivalent to the coprimality formulation, but organized around the divisibility conditions
`p ∣ n` (residues `n mod p`) rather than the single gcd condition.

For a prime `p`:
  • `p` divides `n`  ⟺  `n ≡ 0 (mod p)`;
  • `n` is a *void* for a set `S` of primes if no `p ∈ S` divides `n`;
  • these conditions are defined for all `n`, with no anchor or window.

The anchor `Pk` and the window `(Pk, 2Pk]` enter only when the residue conditions are
restricted to that interval (`gps_free`).

NOTE: this file does not itself close non-emptiness of the window (that is
`dense_sieve_survivor`, closed in `GPS_StateMachine` via the certificate). It provides the
residue/divisibility formulation and its equivalence with coprimality.
-/

namespace StructuralBertrand

/-- `aligned p n` holds when `p ∣ n`, i.e. `n ≡ 0 (mod p)`. -/
def aligned (p n : ℕ) : Prop := p ∣ n

/-- **Void** at `n` with respect to a set of primes `S`: no `p ∈ S` divides `n`.
    Defined for every `n` — no window, no anchor. -/
def isVoid (S : Finset ℕ) (n : ℕ) : Prop := ∀ p ∈ S, ¬ aligned p n

/-- **Equivalence with coprimality.** Being a void with respect to a set of primes `S` is
    equivalent to coprimality with the product `∏_{p∈S} p`. -/
lemma isVoid_iff_coprime {S : Finset ℕ} {n : ℕ} (hS : ∀ p ∈ S, Nat.Prime p) :
    isVoid S n ↔ Nat.Coprime n (∏ p ∈ S, p) := by
  constructor
  · intro h
    apply Nat.Coprime.prod_right
    intro p hp
    exact Nat.coprime_comm.mpr (((hS p hp).coprime_iff_not_dvd).mpr (h p hp))
  · intro h p hp
    have hc : Nat.Coprime n p :=
      Nat.Coprime.coprime_dvd_right (Finset.dvd_prod_of_mem (fun q => q) hp) h
    exact ((hS p hp).coprime_iff_not_dvd).mp (Nat.coprime_comm.mp hc)

/-- **A void in the window is prime.** A void in the GPS window (an `n` not divisible by any
    prime `< Pk`) is prime, by the least-prime-factor argument. Here the anchor and window enter
    the residue formulation. -/
lemma void_in_window_prime {Pk n : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (hn : n ∈ gps_window Pk)
    (hvoid : isVoid ((Finset.range Pk).filter Nat.Prime) n) :
    Nat.Prime n := by
  apply gps_free_prime hPk hPk3
  rw [gps_free, Finset.mem_filter]
  refine ⟨hn, ?_⟩
  -- `∏ p ∈ (range Pk).filter Prime, p` = `primorial_below Pk` (by definition)
  exact (isVoid_iff_coprime (fun p hp => (Finset.mem_filter.mp hp).2)).mp hvoid

/-- **Non-emptiness of the window** = a void exists in `(Pk, 2Pk]`. This is the atom B
    (`dense_sieve_survivor`), stated in the residue/divisibility formulation. A restatement,
    not a new proof. -/
def windowHasVoid (Pk : ℕ) : Prop :=
  ∃ n ∈ gps_window Pk, isVoid ((Finset.range Pk).filter Nat.Prime) n

/-- A void in the window ⟺ nonempty `gps_free`; the two formulations agree. -/
lemma windowHasVoid_iff_gps_free_nonempty {Pk : ℕ} (_hPk : Nat.Prime Pk) (_hPk3 : 2 < Pk) :
    windowHasVoid Pk ↔ (gps_free Pk).Nonempty := by
  constructor
  · rintro ⟨n, hn, hvoid⟩
    refine ⟨n, ?_⟩
    rw [gps_free, Finset.mem_filter]
    refine ⟨hn, ?_⟩
    exact (isVoid_iff_coprime (fun p hp => (Finset.mem_filter.mp hp).2)).mp hvoid
  · rintro ⟨n, hn⟩
    rw [gps_free, Finset.mem_filter] at hn
    refine ⟨n, hn.1, ?_⟩
    rw [isVoid_iff_coprime (fun p hp => (Finset.mem_filter.mp hp).2)]
    exact hn.2

/-! ## Residues and the successor map -/

/-- **Offset** of `p` at `n` = `n mod p`, the residue of `n` modulo `p`. -/
def offset (p n : ℕ) : ℕ := n % p

/-- `p ∣ n` ⟺ `n mod p = 0`. -/
lemma aligned_iff_offset_zero (p n : ℕ) : aligned p n ↔ offset p n = 0 := by
  unfold aligned offset
  exact Nat.dvd_iff_mod_eq_zero

/-- **Void ⟺ all residues nonzero.** `n` is a void for `S` iff `n mod p ≠ 0` for every
    `p ∈ S`. -/
lemma isVoid_iff_offsets_nonzero (S : Finset ℕ) (n : ℕ) :
    isVoid S n ↔ ∀ p ∈ S, offset p n ≠ 0 := by
  simp only [isVoid, aligned_iff_offset_zero]

/-- **Successor map**: `n ↦ n+1` sends every residue `n mod p` to `(n mod p + 1) mod p`. -/
lemma offset_succ (p n : ℕ) : offset p (n + 1) = (offset p n + 1) % p := by
  simp [offset, Nat.add_mod]

/-! ## The base cannot fully cover the window -/

/-- **Full coverage**: every window position is divisible by some prime `< Pk`.
    This is the case "the window contains no new prime" — every position is composite. -/
def fullCoverage (Pk : ℕ) : Prop :=
  ∀ n ∈ gps_window Pk, ¬ isVoid ((Finset.range Pk).filter Nat.Prime) n

/-- No void ⟺ full coverage (de Morgan, by definition). -/
lemma not_windowHasVoid_iff_fullCoverage (Pk : ℕ) :
    ¬ windowHasVoid Pk ↔ fullCoverage Pk := by
  simp only [windowHasVoid, fullCoverage, not_exists, not_and]

/-- **The base cannot fully cover the window.** For a prime `Pk > 2` the primes `< Pk` do not
    cover the whole window — a void (a new prime) always remains. Equivalent to
    `dense_sieve_survivor` via `gps_free`; the content still rests on that theorem. -/
theorem not_fullCoverage {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    ¬ fullCoverage Pk := by
  rw [← not_windowHasVoid_iff_fullCoverage, not_not,
      windowHasVoid_iff_gps_free_nonempty hPk hPk3]
  exact gps_window_nonempty hPk hPk3

/-! ## Successive upper bounds on the location of a void

Bound 0 (Euclid): a void exists somewhere above `Pk`. Free, independent of the atom.
Bound 1 (primorial): a void below `primorial(≤Pk)+1`. Explicit, free.
Below that (a linear bound `c·Pk`): the quantitative work begins. -/

/-- **A void above `Pk` (Euclid).** For the base of primes `< Pk` there is always a void above
    `Pk` (the next prime). Independent of the atom. -/
theorem exists_void_above (Pk : ℕ) :
    ∃ n, Pk < n ∧ isVoid ((Finset.range Pk).filter Nat.Prime) n := by
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (Pk + 1)
  refine ⟨q, by omega, ?_⟩
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  rw [aligned]
  intro hpq
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp.2 hq_prime).mp hpq
  omega

/-- **Explicit upper bound (primorial).** A void exists in `(Pk, primorial(≤Pk)+1]`.
    Euclid's construction: `M+1` is coprime to all primes `≤ Pk`, so its least prime divisor
    `q > Pk` is a void. Independent of the atom. -/
theorem exists_void_below_primorial (Pk : ℕ) :
    ∃ n, Pk < n ∧ n ≤ primorial_below (Pk + 1) + 1 ∧
         isVoid ((Finset.range Pk).filter Nat.Prime) n := by
  set M := primorial_below (Pk + 1) with hM
  have hM_pos : 0 < M := by
    rw [hM, primorial_below]
    exact Finset.prod_pos (fun p hp => (Finset.mem_filter.mp hp).2.pos)
  obtain ⟨q, hq_prime, hq_dvd⟩ := Nat.exists_prime_and_dvd (n := M + 1) (by omega)
  have hq_ndvd_M : ¬ q ∣ M := by
    intro h
    have h1 : q ∣ 1 := by have := Nat.dvd_sub' hq_dvd h; simpa using this
    exact hq_prime.one_lt.ne' (Nat.dvd_one.mp h1)
  have hq_gt : Pk < q := by
    by_contra h
    push_neg at h
    apply hq_ndvd_M
    rw [hM, primorial_below]
    exact Finset.dvd_prod_of_mem (fun p => p)
      (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hq_prime⟩)
  refine ⟨q, hq_gt, Nat.le_of_dvd (by omega) hq_dvd, ?_⟩
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  rw [aligned]
  intro hpq
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp.2 hq_prime).mp hpq
  omega

/-- **The √(2Pk) truncation.** Every composite in the window `(Pk,2Pk]` is divisible by a prime
    `p` with `p² ≤ 2Pk` (its least factor). Hence the window is covered exclusively by primes
    `≤ √(2Pk)` — finitely many, `O(√Pk/ln)`. This makes the disjoint minFac decomposition of the
    window finite (and telescoping to `Pk·∏(1−1/p)`). Same technique as in `gps_free_prime`. -/
lemma window_composite_minFac_sq_le {Pk n : ℕ} (_hPk3 : 2 < Pk)
    (hn : n ∈ gps_window Pk) (hcomp : ¬ Nat.Prime n) :
    n.minFac ^ 2 ≤ 2 * Pk := by
  simp only [gps_window, Finset.mem_Ioc] at hn
  obtain ⟨hlo, hhi⟩ := hn
  have hmf_sq : n.minFac ^ 2 ≤ n := by
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hle : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hcomp
    have hcanc : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hdvd
    calc n.minFac ^ 2 = n.minFac * n.minFac := pow_two _
      _ ≤ n.minFac * (n / n.minFac) := Nat.mul_le_mul (le_refl _) hle
      _ = n := hcanc
  omega

/-- **Buildability edge = 2Pmax.** Every composite in the window `(Pk, 2Pk]` is fully
    buildable from the base: ALL of its prime factors are `≤ Pk`. For if it had a factor
    `q > Pk`, then `n = q·m` with `m ≥ 2`, so `n ≥ 2q > 2Pk` — a contradiction. The first
    composite NOT buildable from the base is `2·nextprime(Pk) > 2Pk`. This is the structural
    reason WHY `2Pmax`: exactly there buildability of composites from the base ends.
    Elementary, no atom. -/
theorem window_composite_smooth {Pk n : ℕ}
    (hn : n ∈ gps_window Pk) (hcomp : ¬ Nat.Prime n) :
    ∀ q, Nat.Prime q → q ∣ n → q ≤ Pk := by
  intro q hq hqn
  by_contra hlt
  push_neg at hlt
  simp only [gps_window, Finset.mem_Ioc] at hn
  obtain ⟨m, hm⟩ := hqn
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · interval_cases m
    · simp at hm; omega
    · rw [mul_one] at hm; rw [hm] at hcomp; exact hcomp hq
  · have hn2q : 2 * q ≤ n := by rw [hm]; nlinarith [hm2]
    omega

/-- **Buildability principle — generalized (self-similar, `x = Pmin`).** A composite `n` with
    least factor `≥ Pmin` and `n ≤ Pmin·Pmax` is fully buildable from the base `≤ Pmax`: all of
    its factors are `≤ Pmax`. For a factor `q > Pmax` would give `n = q·m` with cofactor
    `m ≥ Pmin` (Pmin-rough), so `n ≥ (Pmax+1)·Pmin > Pmin·Pmax` — a contradiction. The
    buildability edge for `minFac = Pmin` is exactly `Pmin·Pmax`; the first unbuildable is
    `Pmin·nextprime(Pmax)`. `window_composite_smooth` is the case `Pmin = 2`. -/
theorem rough_composite_smooth {Pmin Pmax n : ℕ} (hPmin : 2 ≤ Pmin) (hn2 : 2 ≤ n)
    (hrough : Pmin ≤ n.minFac) (hn_le : n ≤ Pmin * Pmax) (hcomp : ¬ Nat.Prime n) :
    ∀ q, Nat.Prime q → q ∣ n → q ≤ Pmax := by
  intro q hq hqn
  by_contra hlt
  push_neg at hlt
  obtain ⟨m, hm⟩ := hqn
  have hm_ne1 : m ≠ 1 := by rintro rfl; rw [mul_one] at hm; rw [hm] at hcomp; exact hcomp hq
  have hm_ne0 : m ≠ 0 := by rintro rfl; simp at hm; omega
  have hmn : m ∣ n := ⟨q, by rw [hm]; ring⟩
  have hmf_dvd_n : m.minFac ∣ n := (Nat.minFac_dvd m).trans hmn
  have h1 : n.minFac ≤ m.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime hm_ne1).two_le hmf_dvd_n
  have h2 : m.minFac ≤ m := Nat.minFac_le (by omega)
  have hmPmin : Pmin ≤ m := le_trans hrough (le_trans h1 h2)
  have hprod : (Pmax + 1) * Pmin ≤ q * m := Nat.mul_le_mul (by omega) hmPmin
  rw [← hm] at hprod
  nlinarith [hprod, hn_le, hPmin]

/-- **The `Pk²` upper bound (lowest free one).** A void exists in `(Pk, Pk²]`, with witness
    `Pk²`: its only prime factor is `Pk`, which is not `< Pk`, so no prime `< Pk` divides it.
    This is the lowest bound reachable by an explicit composite witness: below `Pk²` every void
    is already prime (no free witness), so going lower requires the quantitative argument. -/
theorem exists_void_below_sq {Pk : ℕ} (hPk : Nat.Prime Pk) :
    ∃ n, Pk < n ∧ n ≤ Pk ^ 2 ∧ isVoid ((Finset.range Pk).filter Nat.Prime) n := by
  have h1 : 1 < Pk := hPk.one_lt
  have hsq : Pk ^ 2 = Pk * Pk := by ring
  refine ⟨Pk ^ 2, ?_, le_refl _, ?_⟩
  · nlinarith [h1, hsq]
  · intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [aligned]
    intro hpsq
    have hpp : p ∣ Pk := hp.2.dvd_of_dvd_pow hpsq
    have heq : p = Pk := (Nat.prime_dvd_prime_iff_eq hp.2 hPk).mp hpp
    omega

/-! ## Determinism of the window and its boundary at 2Pmax

Full determinism inside `(Pk, 2Pk]`: void ⟺ prime. The sieve mechanism is unambiguous here —
no element has any freedom. Above `2Pk` this determinism breaks: a void appears that is NOT
prime (`q²` for a prime `q > Pk`). This is the structural boundary of determinism, exactly
at `2Pmax`. -/

/-- Every prime `q > Pk` is a void with respect to the primes `< Pk` (none divides it). The
    converse of the least-factor lemma `void_in_window_prime`. -/
lemma prime_isVoid_of_lt {Pk q : ℕ} (hq : Nat.Prime q) (hq_lo : Pk < q) :
    isVoid ((Finset.range Pk).filter Nat.Prime) q := by
  intro p hp
  rw [Finset.mem_filter, Finset.mem_range] at hp
  rw [aligned]
  intro hpq
  have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp.2 hq).mp hpq
  omega

/-- **Determinism of the window.** Inside `(Pk, 2Pk]`: void ⟺ prime.
    The sieve is fully deterministic here — an equivalence, not merely an implication.
    (`→` is the least-factor lemma `void_in_window_prime`; `←` is `prime_isVoid_of_lt`.) -/
theorem void_iff_prime_in_window {Pk n : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (hn : n ∈ gps_window Pk) :
    isVoid ((Finset.range Pk).filter Nat.Prime) n ↔ Nat.Prime n := by
  constructor
  · exact void_in_window_prime hPk hPk3 hn
  · intro hnp
    have hlo : Pk < n := by
      simp only [gps_window, Finset.mem_Ioc] at hn; exact hn.1
    exact prime_isVoid_of_lt hnp hlo

/-- **Boundary of the equivalence "void ⟺ prime" — this is NOT the meaning of 2Pmax.** The
    equivalence holds up to `p²` (a composite has minFac ≤ √n), and breaks only at `q²` for the
    least prime `q > Pk`: `q²` is a void, lies above `2Pk`, and is NOT prime. Note: this is the
    higher boundary, of order `p²`. The sharp determinism edge at `2Pmax` is self-containment
    (`window_self_contained_dvd` below), not this equivalence. -/
theorem determinism_breaks_above {Pk : ℕ} (_hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    ∃ n, 2 * Pk < n ∧ isVoid ((Finset.range Pk).filter Nat.Prime) n ∧ ¬ Nat.Prime n := by
  obtain ⟨q, hq_ge, hq_prime⟩ := Nat.exists_infinite_primes (Pk + 1)
  have hqq : q ^ 2 = q * q := by ring
  have h1q : 1 < q := hq_prime.one_lt
  refine ⟨q ^ 2, ?_, ?_, ?_⟩
  · -- q² > 2Pk: since q ≥ Pk+1 ⇒ q² ≥ (Pk+1)² = Pk²+2Pk+1 > 2Pk
    have hprod : (Pk + 1) * (Pk + 1) ≤ q * q := Nat.mul_le_mul hq_ge hq_ge
    nlinarith [hprod, hqq, hPk3]
  · -- void: p < Pk prime, p ∣ q² ⇒ p ∣ q ⇒ p = q > Pk, contradiction
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    rw [aligned]
    intro hpq2
    have hpq : p ∣ q := hp.2.dvd_of_dvd_pow hpq2
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp.2 hq_prime).mp hpq
    omega
  · -- q² is not prime: 1 < q < q², so q is a proper divisor
    have hlt : q < q ^ 2 := by nlinarith [hqq, h1q]
    intro hp2
    have hdvd : q ∣ q ^ 2 := ⟨q, by ring⟩
    rcases hp2.eq_one_or_self_of_dvd q hdvd with h | h
    · omega
    · omega

/-! ## Self-containment — the true meaning of determinism, sharp exactly at 2Pmax

This is the precise content of "above 2Pmax determinism breaks": not `p²`, but the window edge.
In `(Pk, 2Pk]` no element is a proper multiple of another — every composite is eliminated
exclusively by the base (≤Pk), never by an in-window survivor. It fails immediately past `2Pk`
(the first such multiple is `2·(Pk+1)`). Small bases are no exception: the property is universal
(no threshold `Pk>7`); a small window is simply too narrow to contain such a multiple —
narrowness, not a threshold. -/

/-- **Self-containment of the window.** In `(Pk, 2Pk]`: `m ∣ n ⟹ m = n`. No proper
    divisibility between window elements — elimination goes only through the base. Universal,
    no threshold. -/
theorem window_self_contained_dvd {Pk m n : ℕ}
    (hm : m ∈ gps_window Pk) (hn : n ∈ gps_window Pk) (hdvd : m ∣ n) : m = n := by
  simp only [gps_window, Finset.mem_Ioc] at hm hn
  obtain ⟨hm_lo, hm_hi⟩ := hm
  obtain ⟨hn_lo, hn_hi⟩ := hn
  rcases eq_or_lt_of_le (Nat.le_of_dvd (by omega) hdvd) with h | hlt
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := hdvd
    have hk2 : 2 ≤ k := by rcases k with _ | _ | k <;> omega
    have h2m : 2 * m ≤ n := by rw [hk]; nlinarith [hk2]
    omega

/-- **Sharp edge — self-containment fails just past 2Pmax.** `Pk+1` lies in the window, but its
    proper multiple `2·(Pk+1)` already lies outside (`> 2Pk`). This is the first such multiple:
    determinism fails immediately past the edge, not at `p²`. -/
theorem self_containment_breaks_just_above {Pk : ℕ} (hPk1 : 1 ≤ Pk) :
    (Pk + 1) ∈ gps_window Pk ∧
    (Pk + 1) ∣ (2 * (Pk + 1)) ∧ Pk + 1 ≠ 2 * (Pk + 1) ∧ 2 * Pk < 2 * (Pk + 1) := by
  refine ⟨?_, ⟨2, by ring⟩, by omega, by omega⟩
  simp only [gps_window, Finset.mem_Ioc]; omega

/-! ## Scale invariance — self-similarity, not coordinate reflection

A numerical test shows that the symmetry `[2,Pmax] ↔ (Pmax,2Pmax]` is NOT a coordinate
reflection: no map `n ↦ c−n` carries voids to primes. The actual invariance is
self-similarity across scale: the sieve law has the same form at every anchor, and every prime
in the base was itself a void in an earlier window. Each void becomes part of the base at the
next scale. -/

/-- **Scale-invariant mechanism.** The window law — void ⟺ prime — has an identical form at
    EVERY anchor `Pk`. The mechanism does not change with scale: this is the mathematical
    content of "it works the same at the start and at any later point". Proved with no `sorry`
    (the universal quantification `void_iff_prime_in_window`). -/
theorem mechanism_scale_invariant :
    ∀ (Pk : ℕ), Nat.Prime Pk → 2 < Pk → ∀ n ∈ gps_window Pk,
      isVoid ((Finset.range Pk).filter Nat.Prime) n ↔ Nat.Prime n :=
  fun _Pk hPk hPk3 _n hn => void_iff_prime_in_window hPk hPk3 hn

/-- **A void becomes part of the base.** A survivor `q` in the window `(Pk,2Pk]` is prime and
    `> Pk`, so at its own scale it belongs to the base: `q ∣ primorial_below (q+1)`. No `sorry`. -/
theorem survivor_absorbed_into_base {Pk q : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (hq : q ∈ gps_free Pk) :
    Nat.Prime q ∧ Pk < q ∧ q ∣ primorial_below (q + 1) := by
  have hqp : Nat.Prime q := gps_free_prime hPk hPk3 hq
  simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc] at hq
  refine ⟨hqp, hq.1.1, ?_⟩
  unfold primorial_below
  exact Finset.dvd_prod_of_mem (fun p => p)
    (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hqp⟩)

/-! ## Scale recursion forces non-emptiness — modulo the one atom

Scale recursion gives the form. For the chain of anchors never to stop, every window must have
a void — this is exactly the atom `dense_sieve_survivor`. The chain below advances modulo that
one atom; this section adds no new open step, it only shows where the single existing one
enters the recursion. -/

/-- **The recursion produces the next anchor, modulo the atom.** At every anchor `Pk>2` the
    window has a void (`gps_window_nonempty`), so the recursion (`gps_step_induction`) produces
    the next anchor `Pk' ∈ (Pk, 2Pk]`, whose base includes the previous state. The whole weight
    rests on one atom (`dense_sieve_survivor`), explicitly localized — no new `sorry` here. -/
theorem mirror_forces_next_anchor {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    ∃ Pk', Nat.Prime Pk' ∧ Pk < Pk' ∧ Pk' ≤ 2 * Pk ∧
      (∀ p ∈ (Finset.range Pk').filter Nat.Prime, p ∣ primorial_below Pk') :=
  gps_step_induction hPk hPk3 (gps_window_nonempty hPk hPk3)

/-! ## Reducing the atom to a covering inequality (truncated arithmetic)

A port of "truncated arithmetic" from variant A (`Truncated.exists_uncovered_of_card_lt`, the
pigeonhole without Erdős), but via the DISJOINT decomposition by `minFac` — without the
union-bound sparsity assumption. The whole weight of B is reduced to one cardinality
inequality: `coveredCount Pk < Pk`. From here we no longer prove "a void in the window", only
this inequality. -/

/-- `isVoid` is decidable (a finite conjunction of divisibilities). Hence `coveredCount` is
    computable — the base cases (small `Pk`) go through `decide`. -/
instance decidableIsVoid (S : Finset ℕ) (n : ℕ) : Decidable (isVoid S n) := by
  unfold isVoid aligned; infer_instance

/-- **Number of covered positions in the window** — aligned by some ring `< Pk` (the
    composites in the window). Disjointly by `minFac` this is `Σ_p A_p`. -/
def coveredCount (Pk : ℕ) : ℕ :=
  ((gps_window Pk).filter
    (fun n => ¬ isVoid ((Finset.range Pk).filter Nat.Prime) n)).card

/-- Size of the ring window: `|(Pk, 2Pk]| = Pk`. -/
lemma gps_window_card (Pk : ℕ) : (gps_window Pk).card = Pk := by
  rw [gps_window, Nat.card_Ioc]; omega

/-- **Structural reduction of the atom.** A void in the window exists ⟺ the base primes cover
    STRICTLY fewer than `Pk` positions. Same pigeonhole as in `Truncated`, but WITHOUT the
    sparsity assumption — via the disjoint split of the window into covered/voids.
    From here B = the single inequality `coveredCount Pk < Pk`. -/
lemma windowHasVoid_iff_coveredCount_lt {Pk : ℕ} :
    windowHasVoid Pk ↔ coveredCount Pk < Pk := by
  simp only [windowHasVoid, coveredCount]
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := gps_window Pk) (p := fun n => isVoid ((Finset.range Pk).filter Nat.Prime) n)
  rw [gps_window_card] at hsplit
  constructor
  · rintro ⟨n, hn, hv⟩
    have hpos : 0 < ((gps_window Pk).filter
        (fun n => isVoid ((Finset.range Pk).filter Nat.Prime) n)).card :=
      Finset.card_pos.mpr ⟨n, Finset.mem_filter.mpr ⟨hn, hv⟩⟩
    omega
  · intro hlt
    have hpos : 0 < ((gps_window Pk).filter
        (fun n => isVoid ((Finset.range Pk).filter Nat.Prime) n)).card := by omega
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hpos
    rw [Finset.mem_filter] at hn
    exact ⟨n, hn.1, hn.2⟩

/-- **Goal B in cardinality form.** If the coverage of the window is strictly less than `Pk`,
    the window has a survivor (a new prime). This is equivalent to the atom
    `dense_sieve_survivor`, but expressed as a countable inequality — here the telescope
    `Σ A_p ≈ Pk·∏(1−1/p)` enters. -/
theorem coveredCount_lt_imp_nonempty {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (h : coveredCount Pk < Pk) : (gps_free Pk).Nonempty :=
  (windowHasVoid_iff_gps_free_nonempty hPk hPk3).mp
    (windowHasVoid_iff_coveredCount_lt.mpr h)

/-- **Union bound: `coveredCount ≤ sigma`.** The actual coverage (DISTINCT positions,
    `coveredCount`) is bounded by the sum of hits WITH MULTIPLICITY
    `sigma = Σ_p |multiples of p|`. Proof: covered = `⋃_p (multiples of p)`, and `card` of a
    union `≤` the sum of `card` (`card_biUnion_le`).
    This makes the difference explicit: `sigma` counts OVERLAPS (15=3·5 counted twice), so
    `sigma ≥ coveredCount`. Hence `sigma` alone does NOT close `coveredCount < Pk`, because
    `sigma > Pk`. The closure lives in `coveredCount = sigma − overlaps`: the goal
    `coveredCount < Pk` ⟺ `overlaps > sigma − Pk`. This one lower bound on the redundancy
    (growing with Pk — "hardest at the start") is the only remaining step. -/
lemma coveredCount_le_sigma (Pk : ℕ) :
    coveredCount Pk ≤ ∑ p ∈ (Finset.range Pk).filter Nat.Prime,
        ((gps_window Pk).filter (fun n => p ∣ n)).card := by
  unfold coveredCount
  refine le_trans (Finset.card_le_card
    (show (gps_window Pk).filter (fun n => ¬ isVoid ((Finset.range Pk).filter Nat.Prime) n)
        ⊆ ((Finset.range Pk).filter Nat.Prime).biUnion
            (fun p => (gps_window Pk).filter (fun n => p ∣ n)) from ?_))
    Finset.card_biUnion_le
  intro n hn
  rw [Finset.mem_filter] at hn
  obtain ⟨hnw, hcov⟩ := hn
  rw [Finset.mem_biUnion]
  by_contra hc
  push_neg at hc
  apply hcov
  intro p hp
  rw [aligned]
  intro hpn
  exact hc p hp (Finset.mem_filter.mpr ⟨hnw, hpn⟩)

/-! ## Telescope identity — disjoint decomposition of coverage by minFac

`coveredCount` decomposes DISJOINTLY into fibers by least prime factor:
`coveredCount Pk = Σ_{p<Pk prime} A_p`, where `A_p = #{n∈(Pk,2Pk] : minFac n = p}`.
This is "the structure counts once" in Lean: every covered position falls into exactly ONE
fiber (its own minFac), so there is no double counting (the multiplicity disappears — a
disjoint sum, not a `Σ` with multiplicity). By `window_composite_minFac_sq_le` only the fibers
`p ≤ √(2Pk)` are nonzero. -/
theorem coveredCount_eq_sum_minFac_fiber {Pk : ℕ} (_hPk3 : 2 < Pk) :
    coveredCount Pk
      = ∑ p ∈ (Finset.range Pk).filter Nat.Prime,
          ((gps_window Pk).filter (fun n => n.minFac = p)).card := by
  unfold coveredCount
  set base := (Finset.range Pk).filter Nat.Prime with hbase
  -- every covered position has minFac in the base (less than Pk and prime)
  have hmem : ∀ n ∈ (gps_window Pk).filter (fun n => ¬ isVoid base n),
      n.minFac ∈ base := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnw, hcov⟩ := hn
    rw [gps_window, Finset.mem_Ioc] at hnw
    have hn2 : n ≠ 1 := by omega
    have hmfp : n.minFac.Prime := Nat.minFac_prime hn2
    have hex : ∃ p, p ∈ base ∧ p ∣ n := by
      by_contra hc
      push_neg at hc
      exact hcov (fun p hp => by rw [aligned]; exact hc p hp)
    obtain ⟨p, hp, hpn⟩ := hex
    rw [hbase, Finset.mem_filter, Finset.mem_range] at hp
    have hmf_le : n.minFac ≤ p := Nat.minFac_le_of_dvd hp.2.two_le hpn
    rw [hbase, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hmfp⟩
  rw [Finset.card_eq_sum_card_fiberwise hmem]
  -- fiber at p<Pk: the condition ¬isVoid is automatic (minFac=p divides n, p∈base)
  apply Finset.sum_congr rfl
  intro p hp
  rw [hbase, Finset.mem_filter, Finset.mem_range] at hp
  congr 1
  ext n
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hnw, _⟩, hmf⟩
    exact ⟨hnw, hmf⟩
  · rintro ⟨hnw, hmf⟩
    refine ⟨⟨hnw, ?_⟩, hmf⟩
    intro hvoid
    have hpn : p ∣ n := hmf ▸ Nat.minFac_dvd n
    have hpbase : p ∈ base := by
      rw [hbase, Finset.mem_filter, Finset.mem_range]; exact ⟨hp.1, hp.2⟩
    exact (hvoid p hpbase) (by rw [aligned]; exact hpn)

/-- **Truncation of the sum to √(2Pk).** Fibers with `p² > 2Pk` are EMPTY (a composite in the
    window has `minFac² ≤ 2Pk`), so coverage sums only over primes `p ≤ √(2Pk)` — finitely
    many, `O(√Pk/ln)`. This is "finitely many rings" in code. -/
theorem coveredCount_eq_sum_truncated {Pk : ℕ} (hPk3 : 2 < Pk) :
    coveredCount Pk
      = ∑ p ∈ (Finset.range Pk).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ 2 * Pk),
          ((gps_window Pk).filter (fun n => n.minFac = p)).card := by
  rw [coveredCount_eq_sum_minFac_fiber hPk3]
  symm
  apply Finset.sum_subset
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  · intro p hp hp'
    rw [Finset.mem_filter, Finset.mem_range] at hp
    have hp2 : 2 * Pk < p ^ 2 := by
      by_contra hle
      push_neg at hle
      exact hp' (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.1, hp.2, hle⟩)
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro n hn hmf
    have hnw := hn
    simp only [gps_window, Finset.mem_Ioc] at hnw
    have hncomp : ¬ Nat.Prime n := by
      intro hnp
      have hpdvd : p ∣ n := hmf ▸ Nat.minFac_dvd n
      have hpeq : p = n := (Nat.prime_dvd_prime_iff_eq hp.2 hnp).mp hpdvd
      omega
    have hsq := window_composite_minFac_sq_le hPk3 hn hncomp
    rw [hmf] at hsq
    omega

/-- **Scale bijection — self-similarity as an identity.** The fiber `A_p` in the window
    `(Pk,2Pk]` is in bijection (via `n = p·m`) with the coprimes in the RESCALED window:
    `A_p = #{m ∈ (Pk/p, 2Pk/p] : m coprime to primorial_below p}`.
    This is EXACTLY the same problem one scale down — the recursion engine (scale invariance as
    an equation). Proved with no `sorry`. -/
theorem coverFiber_eq_scaled {Pk p : ℕ} (hp : Nat.Prime p) :
    ((gps_window Pk).filter (fun n => n.minFac = p)).card
      = ((Finset.Ioc (Pk / p) (2 * Pk / p)).filter
          (fun m => Nat.Coprime m (primorial_below p))).card := by
  have hp0 : 0 < p := hp.pos
  have hkey : (gps_window Pk).filter (fun n => n.minFac = p)
      = ((Finset.Ioc (Pk / p) (2 * Pk / p)).filter
          (fun m => Nat.Coprime m (primorial_below p))).image (fun m => p * m) := by
    ext n
    simp only [gps_window, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨hlo, hhi⟩, hmf⟩
      have hpn : p ∣ n := hmf ▸ Nat.minFac_dvd n
      refine ⟨n / p, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hp0, Nat.div_mul_cancel hpn]; exact hlo
      · exact Nat.div_le_div_right hhi
      · unfold primorial_below
        apply Nat.Coprime.prod_right
        intro q hq
        rw [Finset.mem_filter, Finset.mem_range] at hq
        rw [Nat.coprime_comm, hq.2.coprime_iff_not_dvd]
        intro hqdvd
        have hqn : q ∣ n := hqdvd.trans ⟨p, (Nat.div_mul_cancel hpn).symm⟩
        have hle := Nat.minFac_le_of_dvd hq.2.two_le hqn
        rw [hmf] at hle
        omega
      · exact Nat.mul_div_cancel' hpn
    · rintro ⟨m, ⟨⟨hmlo, hmhi⟩, hmcop⟩, rfl⟩
      have hm1m : 1 ≤ m := lt_of_le_of_lt (Nat.zero_le _) hmlo
      have h2 : 2 ≤ p * m := by
        have := Nat.mul_le_mul hp.two_le hm1m; simpa using this
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h := (Nat.div_lt_iff_lt_mul hp0).mp hmlo
        rwa [mul_comm] at h
      · have h := (Nat.le_div_iff_mul_le hp0).mp hmhi
        rwa [mul_comm] at h
      · apply le_antisymm
        · exact Nat.minFac_le_of_dvd hp.two_le (dvd_mul_right p m)
        · by_contra hlt
          push_neg at hlt
          set r := (p * m).minFac with hr
          have hrp : r.Prime := Nat.minFac_prime (by omega)
          have hrdvd : r ∣ p * m := Nat.minFac_dvd _
          rcases hrp.dvd_mul.mp hrdvd with hrp' | hrm
          · have : r = p := (Nat.prime_dvd_prime_iff_eq hrp hp).mp hrp'
            omega
          · have hrprim : r ∣ primorial_below p := by
              unfold primorial_below
              exact Finset.dvd_prod_of_mem (fun x => x)
                (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hlt, hrp⟩)
            have hg : Nat.gcd m (primorial_below p) = 1 := hmcop
            have hd : r ∣ Nat.gcd m (primorial_below p) := Nat.dvd_gcd hrm hrprim
            rw [hg] at hd
            have := Nat.le_of_dvd Nat.one_pos hd
            have := hrp.two_le
            omega
  rw [hkey, Finset.card_image_of_injective _ (mul_right_injective₀ hp0.ne')]

/-- **The first sieve term, exactly: ring 2.** `A_2 = Pk − Pk/2` (the evens in the window),
    since `primorial_below 2 = 1`, so the coprimality condition vanishes and the whole rescaled
    interval `(Pk/2, Pk]` remains. We split off this dominant term from `coveredCount` exactly. -/
theorem coveredCount_split_two {Pk : ℕ} (hPk3 : 2 < Pk) :
    coveredCount Pk
      = (Pk - Pk / 2)
        + ∑ p ∈ ((Finset.range Pk).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ 2 * Pk)).erase 2,
            ((gps_window Pk).filter (fun n => n.minFac = p)).card := by
  rw [coveredCount_eq_sum_truncated hPk3]
  have h2mem : 2 ∈ (Finset.range Pk).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ 2 * Pk) := by
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Nat.prime_two, by rw [pow_two]; omega⟩
  rw [← Finset.add_sum_erase _ _ h2mem]
  congr 1
  rw [coverFiber_eq_scaled Nat.prime_two]
  have hpb2 : primorial_below 2 = 1 := by
    have h0 : (Finset.range 2).filter Nat.Prime = ∅ := by decide
    rw [primorial_below, h0, Finset.prod_empty]
  rw [hpb2, Finset.filter_true_of_mem (fun x _ => Nat.coprime_one_right x), Nat.card_Ioc]
  omega

/-- **Step-1 goal halved.** Non-emptiness of the window ⟺ the odd composites do not fill the
    odd half: `Σ_{3≤p≤√(2Pk)} A_p < Pk/2`. Ring 2 handled exactly; what remains is the sieve
    over the ODD active rings. -/
theorem windowHasVoid_iff_oddSum_lt {Pk : ℕ} (hPk3 : 2 < Pk) :
    windowHasVoid Pk ↔
    (∑ p ∈ ((Finset.range Pk).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ 2 * Pk)).erase 2,
            ((gps_window Pk).filter (fun n => n.minFac = p)).card) < Pk / 2 := by
  rw [windowHasVoid_iff_coveredCount_lt, coveredCount_split_two hPk3]
  omega

/-! ## Generalized window (Pmax, Pmin·Pmax] — architecture of the generalized family

Bertrand is the instance `Pmin = 2`. For larger `Pmin` the window is WIDER (looser), and the
wide end is FREE (a Euclid witness). The whole weight is the descent in `Pmin` down to `2` —
we do not "prove" Bertrand separately; it is a member of the proven family.

Structural note (fact): self-containment (`window_self_contained_dvd`) holds ONLY for
`Pmin = 2` — wider windows contain `2·(Pmax+1)` and are not self-contained. The tightest window
therefore carries the most structure, which is exactly the case hardest to establish. -/

/-- Generalized window `(Pmax, Pmin·Pmax]`. `Pmin = 2` is the Bertrand window. -/
def gwindow (Pmin Pmax : ℕ) : Finset ℕ := Finset.Ioc Pmax (Pmin * Pmax)

/-- A void in the generalized window: coprime to the base of primes `< Pmax`. -/
def gwindowHasVoid (Pmin Pmax : ℕ) : Prop :=
  ∃ n ∈ gwindow Pmin Pmax, isVoid ((Finset.range Pmax).filter Nat.Prime) n

/-- `Pmin = 2` is exactly the Bertrand window. -/
theorem gwindow_two_eq_window (Pmax : ℕ) : gwindow 2 Pmax = gps_window Pmax := by
  rw [gwindow, gps_window]

/-- **Bertrand = the instance `Pmin = 2`** of the generalized non-emptiness. We do not prove
    Bertrand separately — it falls out of the family at `Pmin = 2`. -/
theorem gwindowHasVoid_two_iff (Pmax : ℕ) :
    gwindowHasVoid 2 Pmax ↔ windowHasVoid Pmax := by
  rw [gwindowHasVoid, windowHasVoid, gwindow_two_eq_window]

/-- **Wide regime — FREE (the easy end of the family).** When `Pmin·Pmax` reaches the
    primorial, the Euclid witness lies in the window and yields a void — with no atom. -/
theorem gwindowHasVoid_of_wide {Pmin Pmax : ℕ}
    (hwide : primorial_below (Pmax + 1) + 1 ≤ Pmin * Pmax) :
    gwindowHasVoid Pmin Pmax := by
  obtain ⟨n, hlo, hhi, hvoid⟩ := exists_void_below_primorial Pmax
  exact ⟨n, by rw [gwindow, Finset.mem_Ioc]; exact ⟨hlo, le_trans hhi hwide⟩, hvoid⟩

/-- A wider window contains the narrower: `Pmin ≤ Pmin' ⟹ gwindow Pmin ⊆ gwindow Pmin'`. -/
theorem gwindow_subset {Pmin Pmin' Pmax : ℕ} (h : Pmin ≤ Pmin') :
    gwindow Pmin Pmax ⊆ gwindow Pmin' Pmax := by
  rw [gwindow, gwindow]
  exact Finset.Ioc_subset_Ioc_right (mul_le_mul_right' h Pmax)

/-- **Direction of the family: bottom to top.** A void in the window `Pmin` propagates to
    EVERY wider `Pmin' ≥ Pmin` — the narrower window is a subset of the wider, and the base and
    the void do not change. The implication runs NARROW ⟹ WIDE. -/
theorem gwindowHasVoid_mono {Pmin Pmin' Pmax : ℕ} (h : Pmin ≤ Pmin')
    (hv : gwindowHasVoid Pmin Pmax) : gwindowHasVoid Pmin' Pmax := by
  obtain ⟨n, hn, hvoid⟩ := hv
  exact ⟨n, gwindow_subset h hn, hvoid⟩

/-- **Bertrand GENERATES the family.** A void in the tightest window (`Pmin = 2`) yields a void
    in ALL wider ones (`Pmin ≥ 2`). Consequence: the wide regime is free but INDEPENDENT — it
    does not flow downward. The kernel stays at the bottom, at `Pmin = 2` (= the atom
    `windowHasVoid`). The generalization frames the family but does NOT reduce it. -/
theorem gwindowHasVoid_of_bertrand {Pmin Pmax : ℕ} (h : 2 ≤ Pmin)
    (hb : windowHasVoid Pmax) : gwindowHasVoid Pmin Pmax :=
  gwindowHasVoid_mono h ((gwindowHasVoid_two_iff Pmax).mpr hb)

/-! ## Proof by contradiction — assume "empty window" and derive the forced parameters

Assume the window `(Pk, 2Pk]` is EMPTY (fully covered by composites). We derive what MUST hold:
(1) every position must be covered by a ring from the FULL BASE `p < Pk` (a ring `> Pk` has
first multiple `2·(>Pk) > 2Pk`, outside the window — it covers NOTHING); (2) the disjoint sum
of coverages `Σ_{p<Pk} A_p` must fill the ENTIRE window: `= Pk`. No `√` here — full base, reach
`2Pk`.

Trichotomy of failure: for this to hold, one of the following would have to break:
  • STRUCTURAL SIEVE — `Σ A_p = Pk` contradicts `Σ A_p < Pk` (the atom),
  • 2Pmax — a prime position would require a ring `> Pk` (its only divisor is itself), whose
    multiple falls `> 2Pk` (outside the window),
  • PEANO/offsets — the offsets of the base rings `< Pk` would have to cover all `Pk` positions,
    even though the density of the union is `1 − ∏(1−1/p) < 1`.
Parts (1)+(2) are proved WITHOUT the atom; the contradiction remains on the atom. -/
theorem fullCoverage_forces_structure {Pk : ℕ} (_hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (hempty : fullCoverage Pk) :
    (∀ n ∈ gps_window Pk, ∃ p ∈ (Finset.range Pk).filter Nat.Prime, p ∣ n)
    ∧ (∑ p ∈ (Finset.range Pk).filter Nat.Prime,
          ((gps_window Pk).filter (fun n => n.minFac = p)).card) = Pk := by
  refine ⟨?_, ?_⟩
  · -- (1) every position covered by a base ring p < Pk
    intro n hn
    have hcov := hempty n hn
    by_contra hc
    push_neg at hc
    exact hcov (fun p hp => by rw [aligned]; exact hc p hp)
  · -- (2) Σ_{p<Pk} A_p = Pk  (coverage fills the whole window)
    rw [← coveredCount_eq_sum_minFac_fiber hPk3]
    have hle : coveredCount Pk ≤ Pk := by
      unfold coveredCount
      exact le_trans (Finset.card_filter_le _ _) (le_of_eq (gps_window_card Pk))
    have hnot : ¬ coveredCount Pk < Pk := by
      rw [← windowHasVoid_iff_coveredCount_lt, not_windowHasVoid_iff_fullCoverage]
      exact hempty
    omega

/-- **A prime position is uncoverable (the "2Pmax" horn).** A prime `q` in the window is not
    divided by any ring `< Pk` — its only ring is itself, `q > Pk`, and `2q > 2Pk` lies outside
    the window. -/
theorem prime_position_uncoverable {Pk q : ℕ} (hq : Nat.Prime q) (hq_lo : Pk < q) :
    ∀ p ∈ (Finset.range Pk).filter Nat.Prime, ¬ p ∣ q :=
  fun p hp => prime_isVoid_of_lt hq hq_lo p hp

/-- **Contradiction modulo the atom.** Full coverage forces `Σ_{p<Pk} A_p = Pk`, while the
    structural sieve gives `Σ A_p < Pk`. The two cannot hold at once (`not_fullCoverage`). -/
theorem fullCoverage_iff_sum_eq {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    fullCoverage Pk →
    (∑ p ∈ (Finset.range Pk).filter Nat.Prime,
          ((gps_window Pk).filter (fun n => n.minFac = p)).card) = Pk :=
  fun h => (fullCoverage_forces_structure hPk hPk3 h).2

/-! ## Base cases by computation — the sieve as an oracle

`coveredCount` is computable, so non-emptiness of the window for small `Pk` is closed by
`decide`, which literally runs the sieve inside the proof — INDEPENDENTLY of the atom
`dense_sieve_survivor`. Here the practical generator (`sieve_bertrand_check`) enters the formal
proof as a base-case tactic. Each such line is one base case closed with no `sorry`. -/

theorem windowHasVoid_3  : windowHasVoid 3  := by
  rw [windowHasVoid_iff_coveredCount_lt]; decide
theorem windowHasVoid_5  : windowHasVoid 5  := by
  rw [windowHasVoid_iff_coveredCount_lt]; decide
theorem windowHasVoid_7  : windowHasVoid 7  := by
  rw [windowHasVoid_iff_coveredCount_lt]; decide
theorem windowHasVoid_11 : windowHasVoid 11 := by
  rw [windowHasVoid_iff_coveredCount_lt]; decide
theorem windowHasVoid_13 : windowHasVoid 13 := by
  rw [windowHasVoid_iff_coveredCount_lt]; decide

/-- These base windows are closed INDEPENDENTLY of the atom — by computing the sieve.
    This is the lower part of the family `Pmin = 2`, closed by machine. -/
example : windowHasVoid 7 ∧ windowHasVoid 11 ∧ windowHasVoid 13 :=
  ⟨windowHasVoid_7, windowHasVoid_11, windowHasVoid_13⟩

/-! ## Test of a logical connective — the dichotomy "empty window ⇒ larger base / other bound"

Proposed connective: "the window cannot be empty, because a void would force a larger base,
and a larger base means a different Pmax; and if the base and Pmax stay, the only remaining
route is a bound other than 2Pmax — but 2Pmax is an arithmetic bound."

Result of the formal test (below, by machine):

(1) An empty window does NOT force a larger base. It forces exactly this: the next prime lies
    `> 2Pk`, and the base of primes `< Pk` stays THE SAME (`fullCoverage_means_next_prime_far`
    — provable, no contradiction). The step "void ⇒ larger base" tacitly assumes the current
    base CANNOT cover the window — precisely the thesis the connective was meant to prove
    (petitio principii). There is no contradiction with the laws of arithmetic here.

(2) Position enters through ONE fact: the window elements are small (`n ≤ 2Pk`), so a composite
    has a factor `≤ √(2Pk)` (`window_composite_minFac_sq_le`). This restricts the covering primes
    from the full base to the TRUNCATED base — and only for the latter does the question "can it
    cover Pk consecutive positions" have a chance of answering NO. This is the true "geometry of
    numbers": the Jacobsthal function of the truncated primorial. Reduction below
    (`windowHasVoid_iff_trunc_coprime`).

Gap table (computed): base {2,3,5}: g=6 vs windows from Pk=13 (margin ×2.2);
{2,3,5,7}: g=10 vs Pk≥29 (×2.9); {…,11}: g=14 vs Pk≥61 (×4.4); {…,13}: g=22 vs Pk≥89 (×4.0);
{…,17}: g=26 vs Pk≥149 (×5.7); {…,19}: g=34 vs Pk≥181 (×5.3). The margin grows (OEIS A048670),
but the GENERAL inequality `g(truncPrimorial Pk) ≤ Pk` is quantitative — of the order of
Iwaniec's theorem `g(M) ≪ (log M)²` with an explicit constant. This is the atom in its final,
sharpest form. -/

/-- **(1) The dichotomy settled by proof.** An empty window (full coverage) does NOT force a
    larger base — it forces exactly: every prime `> Pk` lies `> 2Pk`. The base stays, Pmax
    stays, the bound 2Pmax stays. No purely logical contradiction; the contradiction lives
    solely in the coverage question (the atom). -/
theorem fullCoverage_means_next_prime_far {Pk : ℕ} (hfull : fullCoverage Pk) :
    ∀ q, Nat.Prime q → Pk < q → 2 * Pk < q := by
  intro q hq hlo
  by_contra hle
  push_neg at hle
  have hqw : q ∈ gps_window Pk := by
    simp only [gps_window, Finset.mem_Ioc]; exact ⟨hlo, hle⟩
  exact hfull q hqw (prime_isVoid_of_lt hq hlo)

/-! ## Jacobsthal reduction — the atom as the gap geometry of the truncated base -/

/-- **Truncated primorial**: the product of primes `p` with `p² ≤ 2Pk` (the only primes that
    can cover the window at all — `window_composite_minFac_sq_le`). -/
def truncPrimorial (Pk : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range Pk).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ 2 * Pk), p

/-- **Window determinism, truncated version.** In the window: void with respect to the FULL
    base ⟺ coprimality with the TRUNCATED primorial. The harder direction: a number coprime to
    the truncated primorial and divisible by some `p < Pk` would be composite, so its
    `minFac² ≤ 2Pk` — and then `minFac` divides the truncated primorial, a contradiction. No
    `sorry`. -/
theorem void_iff_coprime_trunc {Pk n : ℕ} (hPk3 : 2 < Pk) (hn : n ∈ gps_window Pk) :
    isVoid ((Finset.range Pk).filter Nat.Prime) n ↔ Nat.Coprime n (truncPrimorial Pk) := by
  have htrS : ∀ p ∈ (Finset.range Pk).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ 2 * Pk),
      Nat.Prime p := fun p hp => (Finset.mem_filter.mp hp).2.1
  constructor
  · intro hvoid
    unfold truncPrimorial
    rw [← isVoid_iff_coprime htrS]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact hvoid p (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hp.1, hp.2.1⟩)
  · intro hcop p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hplt, hpp⟩ := hp
    rw [aligned]
    intro hpn
    have hnw := hn
    simp only [gps_window, Finset.mem_Ioc] at hnw
    -- p < Pk < n, so p ≠ n; p ∣ n ⇒ n composite
    have hncomp : ¬ Nat.Prime n := by
      intro hnp
      rcases hnp.eq_one_or_self_of_dvd p hpn with h1 | hself
      · exact hpp.ne_one h1
      · omega
    have hn1 : n ≠ 1 := by omega
    have hmfp : n.minFac.Prime := Nat.minFac_prime hn1
    have hsq : n.minFac ^ 2 ≤ 2 * Pk := window_composite_minFac_sq_le hPk3 hn hncomp
    have hmf_lt : n.minFac < Pk := by
      by_contra hge
      push_neg at hge
      have h1 : Pk * Pk ≤ n.minFac * n.minFac := Nat.mul_le_mul hge hge
      have h2 : n.minFac * n.minFac ≤ 2 * Pk := by rw [← pow_two]; exact hsq
      have h3 : 3 * Pk ≤ Pk * Pk := Nat.mul_le_mul (by omega) (le_refl Pk)
      omega
    have hdvd : n.minFac ∣ truncPrimorial Pk := by
      unfold truncPrimorial
      exact Finset.dvd_prod_of_mem (fun q => q)
        (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hmf_lt, hmfp, hsq⟩)
    have hg : n.minFac ∣ Nat.gcd n (truncPrimorial Pk) :=
      Nat.dvd_gcd (Nat.minFac_dvd n) hdvd
    have hco : Nat.gcd n (truncPrimorial Pk) = 1 := hcop
    rw [hco] at hg
    have hle1 : n.minFac ≤ 1 := Nat.le_of_dvd Nat.one_pos hg
    have := hmfp.two_le
    omega

/-- **The atom in its sharpest form.** A void in the window ⟺ `(Pk, 2Pk]` contains a number
    coprime to the TRUNCATED primorial (`p² ≤ 2Pk`), not the full one. From here all of Bertrand
    is a question about GAPS of the truncated base, not about primes. -/
theorem windowHasVoid_iff_trunc_coprime {Pk : ℕ} (hPk3 : 2 < Pk) :
    windowHasVoid Pk ↔ ∃ n ∈ gps_window Pk, Nat.Coprime n (truncPrimorial Pk) := by
  constructor
  · rintro ⟨n, hn, hvoid⟩
    exact ⟨n, hn, (void_iff_coprime_trunc hPk3 hn).mp hvoid⟩
  · rintro ⟨n, hn, hcop⟩
    exact ⟨n, hn, (void_iff_coprime_trunc hPk3 hn).mpr hcop⟩

/-- Interface to the atom `dense_sieve_survivor`: a number coprime to the TRUNCATED primorial
    in the window ⇒ a survivor in `gps_free`. -/
theorem survivor_of_trunc_coprime {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk)
    (h : ∃ n ∈ gps_window Pk, Nat.Coprime n (truncPrimorial Pk)) :
    (gps_free Pk).Nonempty :=
  (windowHasVoid_iff_gps_free_nonempty hPk hPk3).mp
    ((windowHasVoid_iff_trunc_coprime hPk3).mpr h)

/-- **(3) The Jacobsthal condition — position is no longer needed.** If EVERY run of `Pk`
    consecutive integers contains a number coprime to the truncated primorial (i.e. the
    Jacobsthal function `g(truncPrimorial Pk) ≤ Pk`), then the window has a void. This is the
    only place where quantitative content remains after the reduction — and it is pure gap
    geometry, with no primes. -/
theorem windowHasVoid_of_jacobsthal {Pk : ℕ} (hPk3 : 2 < Pk)
    (hJ : ∀ a : ℕ, ∃ n ∈ Finset.Ioc a (a + Pk), Nat.Coprime n (truncPrimorial Pk)) :
    windowHasVoid Pk := by
  rw [windowHasVoid_iff_trunc_coprime hPk3]
  obtain ⟨n, hn, hcop⟩ := hJ Pk
  refine ⟨n, ?_, hcop⟩
  rw [gps_window, two_mul]
  exact hn

/-- Coprimality depends only on the residue mod M (periodicity): the Jacobsthal condition need
    only be checked on ONE period. -/
lemma coprime_mod_left (n M : ℕ) : Nat.Coprime (n % M) M ↔ Nat.Coprime n M := by
  unfold Nat.Coprime
  rw [← Nat.gcd_rec, Nat.gcd_comm]

/-- **g(30) = 6, proved for ALL positions** (truncated base {2,3,5}): every run of 6
    consecutive integers contains a number coprime to 30. One period by `decide`, the rest by
    periodicity. No primes, no position. -/
lemma jacobsthal_thirty (a : ℕ) : ∃ n ∈ Finset.Ioc a (a + 6), Nat.Coprime n 30 := by
  have h : ∀ r < 30, ∃ d < 7, 0 < d ∧ Nat.Coprime ((r + d) % 30) 30 := by decide
  obtain ⟨d, hd7, hd0, hcop⟩ := h (a % 30) (Nat.mod_lt _ (by norm_num))
  refine ⟨a + d, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [← coprime_mod_left (a + d) 30, Nat.add_mod,
      Nat.mod_eq_of_lt (show d < 30 by omega)]
  exact hcop

/-- **The whole {2,3,5} regime closed by one gap bound.** For every `Pk ≥ 6` with truncated
    base {2,3,5} (i.e. `truncPrimorial Pk = 30`) a void is forced by `g(30)=6 ≤ Pk` — with no
    knowledge of where the window lies, and no counting of primes. -/
theorem windowHasVoid_of_trunc30 {Pk : ℕ} (hPk3 : 2 < Pk) (h6 : 6 ≤ Pk)
    (htr : truncPrimorial Pk = 30) : windowHasVoid Pk := by
  apply windowHasVoid_of_jacobsthal hPk3
  intro a
  obtain ⟨n, hn, hcop⟩ := jacobsthal_thirty a
  rw [Finset.mem_Ioc] at hn
  exact ⟨n, Finset.mem_Ioc.mpr ⟨hn.1, by omega⟩, by rw [htr]; exact hcop⟩

/-- Windows Pk = 13, 17, 19, 23 closed by the gap geometry of the base {2,3,5} (regime
    `25 ≤ 2Pk < 49`, plus the edge `2·13 ≥ 25`): one Jacobsthal inequality instead of four
    sieve computations. -/
theorem windowHasVoid_17 : windowHasVoid 17 :=
  windowHasVoid_of_trunc30 (by norm_num) (by norm_num) (by decide)
theorem windowHasVoid_19 : windowHasVoid 19 :=
  windowHasVoid_of_trunc30 (by norm_num) (by norm_num) (by decide)
theorem windowHasVoid_23 : windowHasVoid 23 :=
  windowHasVoid_of_trunc30 (by norm_num) (by norm_num) (by decide)

/-! ## The deterministic zone Pk² — formalized

The coupling of the base with its reach, formalized: the equivalence "void ⟺ prime" holds in
the ENTIRE zone `(Pk, Pk²)`, not only in the window. Inside the zone a gap of coprimes is
LITERALLY a gap between primes (no CRT freedom). Only above `Pk²` does the equivalence break
(`determinism_breaks_above`), and CRT periodicity produces long gaps unrelated to primes. This
is why a "counterexample" like 9440–9460 (base of primes < 17) can exist only outside its
base's zone: `17² = 289 < 9440`.

The honest other side: inside the zone, "a gap ≥ Pk just past Pk" now reads "a prime gap ≥ Pk
past Pk" — the equivalence renames the atom, it does not prove it. -/

/-- **Deterministic reach of the sieve = Pk².** For `Pk < n < Pk²`: void ⟺ prime.
    Generalizes `void_iff_prime_in_window` from the window `(Pk, 2Pk]` to the whole zone. -/
theorem void_iff_prime_in_deterministic_zone {Pk n : ℕ} (hPk3 : 2 < Pk)
    (hlo : Pk < n) (hhi : n < Pk ^ 2) :
    isVoid ((Finset.range Pk).filter Nat.Prime) n ↔ Nat.Prime n := by
  constructor
  · intro hvoid
    by_contra hncomp
    have hn1 : n ≠ 1 := by omega
    have hmfp : n.minFac.Prime := Nat.minFac_prime hn1
    have hmf_sq : n.minFac ^ 2 ≤ n := by
      have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
      have hle : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hncomp
      have hcanc : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hdvd
      calc n.minFac ^ 2 = n.minFac * n.minFac := pow_two _
        _ ≤ n.minFac * (n / n.minFac) := Nat.mul_le_mul (le_refl _) hle
        _ = n := hcanc
    have hmf_lt : n.minFac < Pk := by
      by_contra hge
      push_neg at hge
      have h1 : Pk ^ 2 ≤ n.minFac ^ 2 := Nat.pow_le_pow_left hge 2
      omega
    exact (hvoid n.minFac
        (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hmf_lt, hmfp⟩))
      (by rw [aligned]; exact Nat.minFac_dvd n)
  · intro hnp
    exact prime_isVoid_of_lt hnp hlo

/-! ## The staircase of regimes — each truncated-base regime closed by ONE period

The pattern of `windowHasVoid_of_trunc30` generalized: the gap law `g(M) ≤ g` checked on one
period `M` (`decide`, kernel-checked -- windows here are never at an arbitrary position, so
Jacobsthal's worst-case bound doesn't apply and the periodic check needs no `native_decide`
hedge) + periodicity = a void in ALL windows of the regime
`truncPrimorial Pk = M`, without looking into the window. The staircase (computed):
  {2,3,5}    → g(30)   = 6  → Pk = 13, 17, 19, 23          (margin ×2.2)
  {2,3,5,7}  → g(210)  = 10 → Pk = 29, 31, 37, 41, 43, 47, 53, 59   (×2.9)
  {…,11}     → g(2310) = 14 → Pk = 61, 67, 71, 73, 79, 83   (×4.4)
One statement for the whole staircase at once: `g(truncPrimorial Pk) ≤ Pk` — this is the atom. -/

/-- **Periodicity, in general.** A gap law checked on one period `M` transfers to all positions:
    if from every residue `r < M` the nearest coprime is `≤ g < M`, then every run `(a, a+g]`
    contains a number coprime to `M`. -/
lemma jacobsthal_of_period {M g : ℕ} (hM : 0 < M) (hgM : g < M)
    (h : ∀ r < M, ∃ d < g + 1, 0 < d ∧ Nat.Coprime ((r + d) % M) M) :
    ∀ a : ℕ, ∃ n ∈ Finset.Ioc a (a + g), Nat.Coprime n M := by
  intro a
  obtain ⟨d, hdg, hd0, hcop⟩ := h (a % M) (Nat.mod_lt _ hM)
  refine ⟨a + d, Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  rw [← coprime_mod_left (a + d) M, Nat.add_mod,
      Nat.mod_eq_of_lt (show d < M by omega)]
  exact hcop

/-- **A regime closed by the gap law, in general.** `g(M) ≤ g ≤ Pk` on one period
    + `truncPrimorial Pk = M` ⇒ a void in the window. The window's position is unused. -/
theorem windowHasVoid_of_trunc_gap {Pk M g : ℕ} (hPk3 : 2 < Pk) (hg : g ≤ Pk)
    (htr : truncPrimorial Pk = M)
    (hJ : ∀ a : ℕ, ∃ n ∈ Finset.Ioc a (a + g), Nat.Coprime n M) :
    windowHasVoid Pk := by
  apply windowHasVoid_of_jacobsthal hPk3
  intro a
  obtain ⟨n, hn, hcop⟩ := hJ a
  rw [Finset.mem_Ioc] at hn
  exact ⟨n, Finset.mem_Ioc.mpr ⟨hn.1, by omega⟩, by rw [htr]; exact hcop⟩

/-- **g(210) = 10** (truncated base {2,3,5,7}): one period by `decide`. -/
lemma jacobsthal_210 : ∀ a : ℕ, ∃ n ∈ Finset.Ioc a (a + 10), Nat.Coprime n 210 :=
  jacobsthal_of_period (by norm_num) (by norm_num)
    (by decide)

/-- **g(2310) = 14** (truncated base {2,3,5,7,11}): one period by `decide`. -/
lemma jacobsthal_2310 : ∀ a : ℕ, ∃ n ∈ Finset.Ioc a (a + 14), Nat.Coprime n 2310 :=
  jacobsthal_of_period (by norm_num) (by norm_num)
    (by decide)

/-- Regime {2,3,5,7} (`49 ≤ 2Pk < 121`): eight windows by the single law g(210)=10. -/
theorem windowHasVoid_29 : windowHasVoid 29 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210
theorem windowHasVoid_31 : windowHasVoid 31 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210
theorem windowHasVoid_37 : windowHasVoid 37 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210
theorem windowHasVoid_41 : windowHasVoid 41 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210
theorem windowHasVoid_43 : windowHasVoid 43 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210
theorem windowHasVoid_47 : windowHasVoid 47 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210
theorem windowHasVoid_53 : windowHasVoid 53 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210
theorem windowHasVoid_59 : windowHasVoid 59 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_210

/-- Regime {2,3,5,7,11} (`121 ≤ 2Pk < 169`): six windows by the single law g(2310)=14. -/
theorem windowHasVoid_61 : windowHasVoid 61 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_2310
theorem windowHasVoid_67 : windowHasVoid 67 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_2310
theorem windowHasVoid_71 : windowHasVoid 71 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_2310
theorem windowHasVoid_73 : windowHasVoid 73 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_2310
theorem windowHasVoid_79 : windowHasVoid 79 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_2310
theorem windowHasVoid_83 : windowHasVoid 83 :=
  windowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by decide) jacobsthal_2310

/-- The staircase 13–83 in one place: all windows of the three regimes closed by gap geometry,
    without counting primes, without the window's position. -/
example : windowHasVoid 13 ∧ windowHasVoid 29 ∧ windowHasVoid 59 ∧ windowHasVoid 83 :=
  ⟨windowHasVoid_13, windowHasVoid_29, windowHasVoid_59, windowHasVoid_83⟩

/-! ## Variant B — Jacobsthal reduction for the whole family (Pmax, Pmin·Pmax]

Generalization of truncated arithmetic: we prove statements about the FAMILY of windows
`(Pmax, Pmin·Pmax]`, Bertrand being the tightest variant `Pmin = 2`. The reduction carries over
directly:

  a void in `(Pmax, Pmin·Pmax]`  ⟺  a number coprime to `∏ {p < Pmax : p² ≤ Pmin·Pmax}`.

**Estimate for the family (how to estimate for Pmax → Pmin·Pmax):** the family atom is
`g(gtruncPrimorial) ≤ (Pmin−1)·Pmax`. With `y = √(Pmin·Pmax)` one needs
`g(∏ p≤y) ≤ (1 − 1/Pmin)·y²`. The Jacobsthal CONSTANT of the family is `1 − 1/Pmin`:
  · `Pmin = 2` (Bertrand): constant `1/2` — tightest, the family kernel;
  · `Pmin` grows: constant → `1` — exactly the order of Iwaniec's theorem `g ≪ y²`;
  · `Pmin·Pmax ≥ primorial+1`: free (`gwindowHasVoid_of_wide`, Euclid).
The descent in Pmin to 2 = sharpening the constant from 1 to 1/2. Each truncated-base regime
closes for ALL Pmin at once by one period (below: {2,3,5} simultaneously closes the (2,17],
(3,11], (4,9], (5,7) families). Note on variant A: Erdős-type counting also generalizes
(Sylvester–Erdős, C(Pmin·n, n)) — but it remains counting; in B we stay with gap geometry. -/

/-- Family truncated primorial: primes `p < Pmax` with `p² ≤ Pmin·Pmax`
    (the only primes able to cover the generalized window). -/
def gtruncPrimorial (Pmin Pmax : ℕ) : ℕ :=
  ∏ p ∈ (Finset.range Pmax).filter (fun p => Nat.Prime p ∧ p ^ 2 ≤ Pmin * Pmax), p

/-- Truncation in the family: a composite in `(Pmax, Pmin·Pmax]` has `minFac² ≤ Pmin·Pmax`. -/
lemma gwindow_composite_minFac_sq_le {Pmin Pmax n : ℕ} (hPmax : 0 < Pmax)
    (hn : n ∈ gwindow Pmin Pmax) (hcomp : ¬ Nat.Prime n) :
    n.minFac ^ 2 ≤ Pmin * Pmax := by
  simp only [gwindow, Finset.mem_Ioc] at hn
  obtain ⟨hlo, hhi⟩ := hn
  have hmf_sq : n.minFac ^ 2 ≤ n := by
    have hdvd : n.minFac ∣ n := Nat.minFac_dvd n
    have hle : n.minFac ≤ n / n.minFac := Nat.minFac_le_div (by omega) hcomp
    have hcanc : n.minFac * (n / n.minFac) = n := Nat.mul_div_cancel' hdvd
    calc n.minFac ^ 2 = n.minFac * n.minFac := pow_two _
      _ ≤ n.minFac * (n / n.minFac) := Nat.mul_le_mul (le_refl _) hle
      _ = n := hcanc
  omega

/-- **Truncated determinism in the family.** In `(Pmax, Pmin·Pmax]`: void with respect to the
    full base `< Pmax` ⟺ coprimality with the family truncated primorial. No `sorry`. -/
theorem gvoid_iff_coprime_trunc {Pmin Pmax n : ℕ} (hPmax : 0 < Pmax)
    (hn : n ∈ gwindow Pmin Pmax) :
    isVoid ((Finset.range Pmax).filter Nat.Prime) n
      ↔ Nat.Coprime n (gtruncPrimorial Pmin Pmax) := by
  constructor
  · intro hvoid
    unfold gtruncPrimorial
    rw [← isVoid_iff_coprime (fun p hp => (Finset.mem_filter.mp hp).2.1)]
    intro p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    exact hvoid p (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hp.1, hp.2.1⟩)
  · intro hcop p hp
    rw [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨hplt, hpp⟩ := hp
    rw [aligned]
    intro hpn
    have hnw := hn
    simp only [gwindow, Finset.mem_Ioc] at hnw
    have hncomp : ¬ Nat.Prime n := by
      intro hnp
      rcases hnp.eq_one_or_self_of_dvd p hpn with h1 | hself
      · exact hpp.ne_one h1
      · omega
    have hn1 : n ≠ 1 := by omega
    have hmfp : n.minFac.Prime := Nat.minFac_prime hn1
    have hsq : n.minFac ^ 2 ≤ Pmin * Pmax :=
      gwindow_composite_minFac_sq_le hPmax hn hncomp
    have hmf_le : n.minFac ≤ p := Nat.minFac_le_of_dvd hpp.two_le hpn
    have hdvd : n.minFac ∣ gtruncPrimorial Pmin Pmax := by
      unfold gtruncPrimorial
      exact Finset.dvd_prod_of_mem (fun q => q)
        (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hmfp, hsq⟩)
    have hg : n.minFac ∣ Nat.gcd n (gtruncPrimorial Pmin Pmax) :=
      Nat.dvd_gcd (Nat.minFac_dvd n) hdvd
    have hco : Nat.gcd n (gtruncPrimorial Pmin Pmax) = 1 := hcop
    rw [hco] at hg
    have hle1 : n.minFac ≤ 1 := Nat.le_of_dvd Nat.one_pos hg
    have := hmfp.two_le
    omega

/-- **Family atom.** A void in `(Pmax, Pmin·Pmax]` ⟺ the window contains a number coprime to
    the family truncated primorial. The whole family = a question about gaps of truncated bases. -/
theorem gwindowHasVoid_iff_trunc_coprime {Pmin Pmax : ℕ} (hPmax : 0 < Pmax) :
    gwindowHasVoid Pmin Pmax
      ↔ ∃ n ∈ gwindow Pmin Pmax, Nat.Coprime n (gtruncPrimorial Pmin Pmax) := by
  constructor
  · rintro ⟨n, hn, hvoid⟩
    exact ⟨n, hn, (gvoid_iff_coprime_trunc hPmax hn).mp hvoid⟩
  · rintro ⟨n, hn, hcop⟩
    exact ⟨n, hn, (gvoid_iff_coprime_trunc hPmax hn).mpr hcop⟩

/-- **A family regime closed by the gap law.** `g(M) ≤ g` on the period + `g` fits within the
    window length `(Pmin−1)·Pmax` + `gtruncPrimorial = M` ⇒ a void. For ALL `Pmin` at once —
    the window's position is unused. -/
theorem gwindowHasVoid_of_trunc_gap {Pmin Pmax M g : ℕ} (hPmax : 0 < Pmax)
    (hle : Pmax ≤ Pmin * Pmax) (hg : g ≤ Pmin * Pmax - Pmax)
    (htr : gtruncPrimorial Pmin Pmax = M)
    (hJ : ∀ a : ℕ, ∃ n ∈ Finset.Ioc a (a + g), Nat.Coprime n M) :
    gwindowHasVoid Pmin Pmax := by
  rw [gwindowHasVoid_iff_trunc_coprime hPmax]
  obtain ⟨n, hn, hcop⟩ := hJ Pmax
  rw [Finset.mem_Ioc] at hn
  refine ⟨n, ?_, by rw [htr]; exact hcop⟩
  rw [gwindow, Finset.mem_Ioc]
  omega

/-- Family {2,3,5}: ONE law g(30)=6 closes windows of different `Pmin` simultaneously —
    (11,33], (13,39], (9,36], (7,35]. The descent in Pmin works on a shared mechanism. -/
theorem gwindowHasVoid_3_11 : gwindowHasVoid 3 11 :=
  gwindowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by norm_num)
    (by decide) jacobsthal_thirty
theorem gwindowHasVoid_3_13 : gwindowHasVoid 3 13 :=
  gwindowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by norm_num)
    (by decide) jacobsthal_thirty
theorem gwindowHasVoid_4_9 : gwindowHasVoid 4 9 :=
  gwindowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by norm_num)
    (by decide) jacobsthal_thirty
theorem gwindowHasVoid_5_7 : gwindowHasVoid 5 7 :=
  gwindowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by norm_num)
    (by decide) jacobsthal_thirty

/-- Family {2,3,5,7}: g(210)=10 closes e.g. (29,87] and (37,111] at `Pmin = 3`. -/
theorem gwindowHasVoid_3_29 : gwindowHasVoid 3 29 :=
  gwindowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by norm_num)
    (by decide) jacobsthal_210
theorem gwindowHasVoid_3_37 : gwindowHasVoid 3 37 :=
  gwindowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by norm_num)
    (by decide) jacobsthal_210

/-- Consistency with the kernel: at `Pmin = 2` the family atom coincides with the Bertrand atom
    (`gtruncPrimorial 2 Pk = truncPrimorial Pk` by definition, via `2 * Pk = Pk * 2`; here in
    theorem form for a concrete case). -/
example : gwindowHasVoid 2 17 :=
  gwindowHasVoid_of_trunc_gap (by norm_num) (by norm_num) (by norm_num)
    (by decide) jacobsthal_thirty

/-! ## Inclusion–exclusion (Legendre) identity

This is inclusion–exclusion over the truncated base. Its core is ONE recursive step: adjoining
a prime `p` to a set with product `M` splits the survivors into those also coprime to `p`, plus
a copy of the whole problem at scale `1/p`:

    #surv(S∪{p}, (a,b]]  =  #surv(S, (a,b]]  −  #surv(S, (a/p, b/p]]

(here in additive form, avoiding subtraction in ℕ). Unfolding this recursion over all primes is
exactly the Legendre sum `Σ_T (−1)^{|T|}·…` at full depth. The identity is exact (verified:
P=101→20, 503→72, 1009→137, 5003→559). The partial sums by order oscillate
(1009→−647→489→83→137); positivity of the full sum for EVERY window at once is the atom. -/

/-- **The anchor is idle in its own window (equivalence of conventions).** The survivors in
    `(Pk, 2Pk]` with respect to the base `≤ Pk` (where the base maximum defines the window) and
    with respect to the base `< Pk` (where the anchor is itself a survivor and the smaller base
    does the sieving) are THE SAME set. Reason: the only multiple of `Pk` in the window is `2Pk`,
    which is divisible by `2`. No result of the project depends on the choice of convention. -/
theorem anchor_idle_in_own_window {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    (gps_window Pk).filter (fun n => Nat.Coprime n (primorial_below (Pk + 1)))
      = gps_free Pk := by
  have hins : (Finset.range (Pk + 1)).filter Nat.Prime
      = insert Pk ((Finset.range Pk).filter Nat.Prime) := by
    ext q
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
  have hprod : primorial_below (Pk + 1) = Pk * primorial_below Pk := by
    rw [primorial_below, primorial_below, hins, Finset.prod_insert hPk_not]
  have h2M : 2 ∣ primorial_below Pk := by
    unfold primorial_below
    exact Finset.dvd_prod_of_mem (fun q => q)
      (by rw [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, Nat.prime_two⟩)
  unfold gps_free
  ext n
  simp only [Finset.mem_filter, gps_window, Finset.mem_Ioc]
  rw [hprod, Nat.coprime_mul_iff_right]
  constructor
  · rintro ⟨hn, _, hM⟩
    exact ⟨hn, hM⟩
  · rintro ⟨⟨hlo, hhi⟩, hM⟩
    refine ⟨⟨hlo, hhi⟩, ?_, hM⟩
    -- Coprime n Pk: otherwise Pk ∣ n ⇒ n = 2Pk ⇒ 2 ∣ n, but 2 ∣ M' — contradiction with hM
    rw [Nat.coprime_comm, hPk.coprime_iff_not_dvd]
    intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    have hk1 : 1 < k := by
      by_contra h
      push_neg at h
      interval_cases k <;> omega
    have hk3 : k < 3 := by
      by_contra h
      push_neg at h
      have h3 : 3 * Pk ≤ Pk * k := by
        calc 3 * Pk = Pk * 3 := by ring
          _ ≤ Pk * k := Nat.mul_le_mul_left Pk h
      omega
    have hk2 : k = 2 := by omega
    subst hk2
    have h2n : 2 ∣ n := ⟨Pk, by omega⟩
    have hdg : 2 ∣ Nat.gcd n (primorial_below Pk) := Nat.dvd_gcd h2n h2M
    have hco : Nat.gcd n (primorial_below Pk) = 1 := hM
    rw [hco] at hdg
    have := Nat.le_of_dvd Nat.one_pos hdg
    omega

/-- **Inclusion–exclusion — the recursive step.** For a prime `p ∉ S` (S a set of primes, product
    `M = ∏S`): the survivors of the system `S∪{p}` in `(a,b]` plus a copy of the problem `S` at
    scale `1/p` = the survivors of the system `S` in `(a,b]`. Exact, no approximation;
    self-similarity of scale as an equation on cardinalities. -/
theorem interference_step {p : ℕ} (hp : Nat.Prime p) {S : Finset ℕ}
    (hS : ∀ q ∈ S, Nat.Prime q) (hpS : p ∉ S) (a b : ℕ) :
    ((Finset.Ioc a b).filter (fun n => Nat.Coprime n (p * ∏ q ∈ S, q))).card
      + ((Finset.Ioc (a / p) (b / p)).filter (fun m => Nat.Coprime m (∏ q ∈ S, q))).card
    = ((Finset.Ioc a b).filter (fun n => Nat.Coprime n (∏ q ∈ S, q))).card := by
  have hp0 : 0 < p := hp.pos
  set M := ∏ q ∈ S, q with hM
  have hpM : Nat.Coprime p M := by
    rw [hM]
    apply Nat.Coprime.prod_right
    intro q hq
    exact (Nat.coprime_primes hp (hS q hq)).mpr (fun h => hpS (h ▸ hq))
  -- Split the survivors of S in (a,b] according to divisibility by p
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.Ioc a b).filter (fun n => Nat.Coprime n M))
    (p := fun n => p ∣ n)
  -- (I) those NOT divisible by p = survivors of the system S∪{p}
  have hfree : ((Finset.Ioc a b).filter (fun n => Nat.Coprime n M)).filter
      (fun n => ¬ p ∣ n)
      = (Finset.Ioc a b).filter (fun n => Nat.Coprime n (p * M)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Nat.coprime_mul_iff_right]
    constructor
    · rintro ⟨⟨hn, hcopM⟩, hnd⟩
      refine ⟨hn, ?_, hcopM⟩
      exact Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hnd)
    · rintro ⟨hn, hcopp, hcopM⟩
      refine ⟨⟨hn, hcopM⟩, ?_⟩
      exact hp.coprime_iff_not_dvd.mp (Nat.coprime_comm.mp hcopp)
  -- (II) those DIVISIBLE by p = a copy of the problem S at scale 1/p (bijection n = p·m)
  have hscaled : ((Finset.Ioc a b).filter (fun n => Nat.Coprime n M)).filter
      (fun n => p ∣ n)
      = ((Finset.Ioc (a / p) (b / p)).filter
          (fun m => Nat.Coprime m M)).image (fun m => p * m) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨hlo, hhi⟩, hcop⟩, hpn⟩
      refine ⟨n / p, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul hp0, Nat.div_mul_cancel hpn]; exact hlo
      · exact Nat.div_le_div_right hhi
      · exact Nat.Coprime.coprime_dvd_left ⟨p, (Nat.div_mul_cancel hpn).symm⟩ hcop
      · exact Nat.mul_div_cancel' hpn
    · rintro ⟨m, ⟨⟨hmlo, hmhi⟩, hmcop⟩, rfl⟩
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, dvd_mul_right p m⟩
      · have h := (Nat.div_lt_iff_lt_mul hp0).mp hmlo
        rwa [mul_comm] at h
      · have h := (Nat.le_div_iff_mul_le hp0).mp hmhi
        rwa [mul_comm] at h
      · exact Nat.coprime_comm.mp
          ((Nat.coprime_comm.mp hpM).mul_right (Nat.coprime_comm.mp hmcop))
  rw [hfree, hscaled,
      Finset.card_image_of_injective _ (mul_right_injective₀ hp0.ne')] at hsplit
  omega

/-- **Inclusion–exclusion identity (Legendre).** The number of survivors of a set of primes
    `S` in `(a,b]` equals the sum over ALL subsets `T ⊆ S` with the parity sign:
    `Σ_T (−1)^|T| · (⌊b/∏T⌋ − ⌊a/∏T⌋)`. Exact and deterministic — the order-by-order layers are
    its (oscillating) partial sums; the whole is an identity. Proof: unfolding the recursion
    `interference_step` by induction on the base. -/
theorem interference_formula (S : Finset ℕ) :
    (∀ q ∈ S, Nat.Prime q) → ∀ a b : ℕ, a ≤ b →
    (((Finset.Ioc a b).filter (fun n => Nat.Coprime n (∏ q ∈ S, q))).card : ℤ)
      = ∑ T ∈ S.powerset,
          (-1 : ℤ) ^ T.card
            * (↑(b / ∏ q ∈ T, q) - ↑(a / ∏ q ∈ T, q)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      intro _ a b hab
      rw [Finset.prod_empty,
          Finset.filter_true_of_mem (fun n _ => Nat.coprime_one_right n),
          Nat.card_Ioc, Finset.powerset_empty, Finset.sum_singleton]
      simp [Nat.cast_sub hab]
  | @insert p S hpS ih =>
      intro hS a b hab
      have hp : Nat.Prime p := hS p (Finset.mem_insert_self p S)
      have hS' : ∀ q ∈ S, Nat.Prime q := fun q hq => hS q (Finset.mem_insert_of_mem hq)
      -- recursive step (interference_step) in ℤ
      have hstep := interference_step hp hS' hpS a b
      have hstepZ : (((Finset.Ioc a b).filter
            (fun n => Nat.Coprime n (p * ∏ q ∈ S, q))).card : ℤ)
          = (((Finset.Ioc a b).filter (fun n => Nat.Coprime n (∏ q ∈ S, q))).card : ℤ)
            - (((Finset.Ioc (a / p) (b / p)).filter
                (fun m => Nat.Coprime m (∏ q ∈ S, q))).card : ℤ) := by
        have h := congrArg (fun k : ℕ => (k : ℤ)) hstep
        push_cast at h
        linarith
      -- combinatorial side: subsets of (insert p S) = subsets of S ⊔ images of (insert p)
      have hdisj : Disjoint S.powerset (S.powerset.image (insert p)) := by
        rw [Finset.disjoint_left]
        intro T hT hT'
        obtain ⟨T', _, rfl⟩ := Finset.mem_image.mp hT'
        exact hpS (Finset.mem_powerset.mp hT (Finset.mem_insert_self p T'))
      have hinj : ∀ T₁ ∈ S.powerset, ∀ T₂ ∈ S.powerset,
          insert p T₁ = insert p T₂ → T₁ = T₂ := by
        intro T₁ h₁ T₂ h₂ h
        have hp₁ : p ∉ T₁ := fun hmem => hpS (Finset.mem_powerset.mp h₁ hmem)
        have hp₂ : p ∉ T₂ := fun hmem => hpS (Finset.mem_powerset.mp h₂ hmem)
        rw [← Finset.erase_insert hp₁, ← Finset.erase_insert hp₂, h]
      -- terms containing p in the overlap = minus a copy of the formula at scale 1/p
      have hsum2 : ∀ T ∈ S.powerset,
          (-1 : ℤ) ^ (insert p T).card
              * (↑(b / ∏ q ∈ insert p T, q) - ↑(a / ∏ q ∈ insert p T, q))
            = -((-1 : ℤ) ^ T.card
              * (↑(b / p / ∏ q ∈ T, q) - ↑(a / p / ∏ q ∈ T, q))) := by
        intro T hT
        have hpT : p ∉ T := fun hmem => hpS (Finset.mem_powerset.mp hT hmem)
        rw [Finset.card_insert_of_not_mem hpT, Finset.prod_insert hpT, pow_succ,
            ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul]
        ring
      rw [Finset.prod_insert hpS, hstepZ,
          ih hS' a b hab, ih hS' (a / p) (b / p) (Nat.div_le_div_right hab),
          Finset.powerset_insert, Finset.sum_union hdisj, Finset.sum_image hinj,
          Finset.sum_congr rfl hsum2, Finset.sum_neg_distrib]
      ring

/-! ## The S1 purity law and the central binomial coefficient

The central binomial coefficient `C(2n,n)` is a classical object; Erdős used it. Its prime
content in the window is controlled by the source purity law (S1 — in Lean
`window_composite_smooth`/`window_self_contained_dvd`): a source `q ∈ (n, 2n]` divides `(2n)!`
exactly once, because its first multiple `2q` exceeds `2n` (`2q > 2n`), and does not divide
`(n!)²` at all (`q > n`). This is the same role of `2` and the same self-containment as at
`Pmin = 2`. -/

/-- The product of DISTINCT primes divides a common multiple
    (induction via coprimality of distinct primes). -/
lemma prod_primes_dvd (s : Finset ℕ) :
    (∀ p ∈ s, Nat.Prime p) → ∀ n : ℕ, (∀ p ∈ s, p ∣ n) → (∏ p ∈ s, p) ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _ n _
      simp
  | @insert p s hps ih =>
      intro hs n h
      rw [Finset.prod_insert hps]
      have hp : Nat.Prime p := hs p (Finset.mem_insert_self p s)
      have hcop : Nat.Coprime p (∏ q ∈ s, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        exact (Nat.coprime_primes hp (hs q (Finset.mem_insert_of_mem hq))).mpr
          (fun heq => hps (heq ▸ hq))
      exact hcop.mul_dvd_of_dvd_of_dvd (h p (Finset.mem_insert_self p s))
        (ih (fun q hq => hs q (Finset.mem_insert_of_mem hq)) n
            (fun q hq => h q (Finset.mem_insert_of_mem hq)))

/-- **Product of new sources divides `C(2n,n)`.** The product of ALL new sources of the window
    (primes in `(n, 2n]`) divides the central binomial coefficient `C(2n, n)` — the window's
    content recorded in its factorization, by the S1 purity law. No `sorry`. -/
theorem window_primes_prod_dvd_centralBinom (n : ℕ) :
    (∏ q ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, q) ∣ Nat.choose (2 * n) n := by
  apply prod_primes_dvd
  · intro q hq
    exact (Finset.mem_filter.mp hq).2
  · intro q hq
    rw [Finset.mem_filter, Finset.mem_Ioc] at hq
    obtain ⟨⟨hlo, hhi⟩, hqp⟩ := hq
    rw [two_mul]
    exact hqp.dvd_choose_add hlo hlo (by omega)

end StructuralBertrand
