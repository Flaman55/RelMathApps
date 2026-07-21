import StructuralBertrand.Rings
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Newton.lean — the central binomial coefficient and the window's prime content

The central binomial coefficient `C(2n,n)` is used here as a classical combinatorial object
(an entry of the binomial expansion), not as an analytic estimate: `4^n = (1+1)^{2n}` is the
sum of the `2n+1` binomial coefficients of order `2n`, of which the central one is the largest.
Its prime factorization in the window is controlled by the S1 purity law:

  · NEW sources (primes in `(n, 2n]`) each divide `C(2n,n)` exactly once, because the first
    multiple `2q` exceeds `2n` (S1 purity law);
    reference: `window_primes_prod_dvd_centralBinom` (Rings.lean);
  · OLD sources (`p ≤ n`) — if the window contains no prime, every prime factor of `C(2n,n)`
    is `≤ n` (`centralBinom_prime_factor_le` below).

The "empty window" contradiction thus compares two bounds on the same integer `C(2n,n)`: an
upper bound from the old sources (each contributing `p^ν ≤ 2n`) against the lower bound
`4^n/(2n+1)`.
-/

namespace StructuralBertrand

/-- Restatement of `window_primes_prod_dvd_centralBinom` for `Nat.centralBinom`: the product of
    the window's new sources divides the central binomial coefficient. -/
theorem window_primes_prod_dvd_centralBinom' (n : ℕ) :
    (∏ q ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, q) ∣ Nat.centralBinom n := by
  unfold Nat.centralBinom
  exact window_primes_prod_dvd_centralBinom n

/-- **Product of new sources ≤ C(2n,n).** The product of all new sources of the window does not
    exceed `C(2n,n)` (a divisor of a positive number). -/
theorem window_primes_prod_le_centralBinom (n : ℕ) :
    (∏ q ∈ (Finset.Ioc n (2 * n)).filter Nat.Prime, q) ≤ Nat.centralBinom n :=
  Nat.le_of_dvd (Nat.centralBinom_pos n) (window_primes_prod_dvd_centralBinom' n)

/-- **Lower bound on C(2n,n).** `4^n = Σ_{k=0}^{2n} C(2n,k)` is a sum of `2n+1` terms, each
    `≤` the central one. Hence `4^n ≤ (2n+1)·C(2n,n)`, proved directly from the expansion of
    `(1+1)^{2n}`. -/
theorem four_pow_le_newton (n : ℕ) :
    4 ^ n ≤ (2 * n + 1) * Nat.centralBinom n := by
  have h4 : (4 : ℕ) ^ n = 2 ^ (2 * n) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  have hmid : ∀ i, (2 * n).choose i ≤ Nat.centralBinom n := by
    intro i
    have h := Nat.choose_le_middle i (2 * n)
    have h2 : 2 * n / 2 = n := by omega
    rw [h2] at h
    exact h
  calc 4 ^ n = ∑ i ∈ Finset.range (2 * n + 1), (2 * n).choose i := by
        rw [Nat.sum_range_choose, h4]
    _ ≤ ∑ _i ∈ Finset.range (2 * n + 1), Nat.centralBinom n :=
        Finset.sum_le_sum fun i _ => hmid i
    _ = (2 * n + 1) * Nat.centralBinom n := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Empty window ⇒ every prime factor is an old source.** Every prime factor of `C(2n,n)`
    is `≤ 2n` (it divides `(2n)!`), and with no new sources in `(n, 2n]` it is `≤ n`. This is
    the upper-bound side of the forthcoming contradiction. -/
theorem centralBinom_prime_factor_le {n p : ℕ}
    (h_no : ∀ q, n < q → q ≤ 2 * n → ¬ Nat.Prime q)
    (hp : Nat.Prime p) (hdvd : p ∣ Nat.centralBinom n) : p ≤ n := by
  have h1 : Nat.centralBinom n ∣ Nat.factorial (2 * n) := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    exact ⟨Nat.factorial n * Nat.factorial (2 * n - n), by
      unfold Nat.centralBinom
      rw [← h, mul_assoc]⟩
  have h2 : p ∣ Nat.factorial (2 * n) := hdvd.trans h1
  have h3 : p ≤ 2 * n := (Nat.Prime.dvd_factorial hp).mp h2
  by_contra hgt
  push_neg at hgt
  exact h_no p hgt h3 hp

end StructuralBertrand
