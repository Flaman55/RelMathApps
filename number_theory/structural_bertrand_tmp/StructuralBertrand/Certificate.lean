import StructuralBertrand.GPS_StateMachine
import StructuralBertrand.Erdos
import StructuralBertrand.BinomialCertificate
import Mathlib.Tactic

/-!
# Certificate.lean — the quantitative atom as a pluggable interface

The structural reduction sends Bertrand to a single quantitative statement (the atom): for
`2 < n`, the window `(n, 2n]` cannot be empty of primes. This file abstracts that statement as
`WindowCertificate` and proves that the closure of the atom — hence the whole theorem — depends
*only* on the certificate, not on how it is proved. Any certificate of the required strength
plugs in.

* Instance A (binomial via Mathlib): `erdos_certificate`, from `Erdos.erdos_contradiction`.
* Instance B (self-contained binomial): `binomial_certificate`, from
  `BinomialCertificate.binomial_contradiction`, built WITHOUT Mathlib's Bertrand theorem.

This makes modularity a theorem, not a claim: `dense_sieve_survivor_of_certificate` and
`prime_in_window_of_certificate` are parameterized over an arbitrary `WindowCertificate`.
-/

namespace StructuralBertrand

/-- **The quantitative atom, abstracted.** A *window certificate* is any proof that an empty
    window is impossible: for every `n > 2`, if `(n, 2n]` contains no prime, a contradiction
    follows. -/
def WindowCertificate : Prop :=
  ∀ n : ℕ, 2 < n → (∀ q, n < q → q ≤ 2 * n → ¬ Nat.Prime q) → False

/-- **Instance A — the binomial certificate via Mathlib.** `erdos_contradiction` is exactly a
    `WindowCertificate` (it imports Mathlib's two inequalities on `C(2n,n)`). -/
theorem erdos_certificate : WindowCertificate :=
  fun _n hn h => erdos_contradiction hn h

/-- **Instance B — the self-contained binomial certificate.** `binomial_contradiction`
    (`BinomialCertificate.lean`) is a `WindowCertificate` built from the two bounds on
    `C(2n,n)` plus a local oracle, WITHOUT importing `Mathlib.NumberTheory.Bertrand`. Two
    independent instances closing the same atom — modularity as a fact. -/
theorem binomial_certificate : WindowCertificate :=
  fun _n hn h => binomial_contradiction hn h

/-- **Modularity, as a theorem.** Given ANY window certificate, the structural sieve leaves a
    survivor in every window `(Pk, 2Pk]`. The proof body is identical to `dense_sieve_survivor`
    except that the quantitative step is supplied by the `cert` argument, not hard-wired to
    Erdős. -/
theorem dense_sieve_survivor_of_certificate (cert : WindowCertificate)
    {Pk : ℕ} (hPk3 : 2 < Pk) :
    (gps_free Pk).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  refine cert Pk hPk3 (fun q hlo hhi hq => ?_)
  have hcop : Nat.Coprime q (primorial_below Pk) :=
    prime_in_window_coprime_primorial hq hlo
  have hqmem : q ∈ gps_free Pk := by
    simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hlo, hhi⟩, hcop⟩
  rw [hempty] at hqmem
  exact absurd hqmem (Finset.not_mem_empty q)

/-- **Consuming corollary, parameterized.** Any window certificate yields a prime in
    `(Pk, 2Pk]`. Plugging `erdos_certificate` recovers the existing `prime_in_window`. -/
theorem prime_in_window_of_certificate (cert : WindowCertificate)
    {Pk : ℕ} (hPk : Nat.Prime Pk) (hPk3 : 2 < Pk) :
    ∃ q, Pk < q ∧ q ≤ 2 * Pk ∧ Nat.Prime q := by
  obtain ⟨n, hn⟩ := dense_sieve_survivor_of_certificate cert hPk3
  have hnp : Nat.Prime n := gps_free_prime hPk hPk3 hn
  simp only [gps_free, gps_window, Finset.mem_filter, Finset.mem_Ioc] at hn
  exact ⟨n, hn.1.1, hn.1.2, hnp⟩

/-- Sanity check: the SAME interface, fed either certificate, produces a prime in `(17, 34]`.
    Both instances plug into the identical slot — modularity as a fact. -/
example : ∃ q, 17 < q ∧ q ≤ 2 * 17 ∧ Nat.Prime q :=
  prime_in_window_of_certificate erdos_certificate (by norm_num) (by norm_num)

example : ∃ q, 17 < q ∧ q ≤ 2 * 17 ∧ Nat.Prime q :=
  prime_in_window_of_certificate binomial_certificate (by norm_num) (by norm_num)

end StructuralBertrand
