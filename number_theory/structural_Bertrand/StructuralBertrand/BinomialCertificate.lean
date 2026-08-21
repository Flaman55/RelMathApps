import StructuralBertrand.BinomialBound
import StructuralBertrand.Threshold
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic

/-!
# BinomialCertificate.lean — the self-contained binomial contradiction

`binomial_contradiction` closes the quantitative atom entirely within our own development:
for `2 < n`, an empty window `(n, 2n]` is impossible. It imports only

* `BinomialBound` — the upper bound `window_centralBinom_le`, reproved from Legendre/Kummer +
  primorial primitives (the Erdős-specific content, ours);
* `Threshold` — the prime-free size inequality `threshold_inequality`;
* `Mathlib.Data.Nat.Choose.Central` — the lower bound `four_pow_lt_mul_centralBinom`
  (`4^n < n · C(2n,n)`) and the definition of `centralBinom`.

Crucially it does NOT import `Mathlib.NumberTheory.Bertrand`: the closure is assembled from
the two bounds on `C(2n,n)` plus a computational oracle for the small cases, none of which is
Mathlib's Bertrand theorem. Plugs into `WindowCertificate` as instance B.
-/

open Nat

namespace StructuralBertrand

-- `witness_search`: shared closing tactic for `small_window_oracle` below. `first` tries every
-- prime below 1024 in increasing order as the witness `p`, stopping at the one satisfying
-- `n < p ∧ p ≤ 2n` (Bertrand guarantees one exists for every literal `n` this is used on). Each
-- attempt is one flat `decide` on closed numerals, so no bounded quantifier survives to be
-- unfolded by the kernel. (A doc comment can't precede a `macro` command, so the rationale for
-- the whole small-windows proof lives on `small_window_oracle` itself, below.)
macro "witness_search" : tactic => `(tactic| first
  | exact ⟨2, by decide⟩
  | exact ⟨3, by decide⟩
  | exact ⟨5, by decide⟩
  | exact ⟨7, by decide⟩
  | exact ⟨11, by decide⟩
  | exact ⟨13, by decide⟩
  | exact ⟨17, by decide⟩
  | exact ⟨19, by decide⟩
  | exact ⟨23, by decide⟩
  | exact ⟨29, by decide⟩
  | exact ⟨31, by decide⟩
  | exact ⟨37, by decide⟩
  | exact ⟨41, by decide⟩
  | exact ⟨43, by decide⟩
  | exact ⟨47, by decide⟩
  | exact ⟨53, by decide⟩
  | exact ⟨59, by decide⟩
  | exact ⟨61, by decide⟩
  | exact ⟨67, by decide⟩
  | exact ⟨71, by decide⟩
  | exact ⟨73, by decide⟩
  | exact ⟨79, by decide⟩
  | exact ⟨83, by decide⟩
  | exact ⟨89, by decide⟩
  | exact ⟨97, by decide⟩
  | exact ⟨101, by decide⟩
  | exact ⟨103, by decide⟩
  | exact ⟨107, by decide⟩
  | exact ⟨109, by decide⟩
  | exact ⟨113, by decide⟩
  | exact ⟨127, by decide⟩
  | exact ⟨131, by decide⟩
  | exact ⟨137, by decide⟩
  | exact ⟨139, by decide⟩
  | exact ⟨149, by decide⟩
  | exact ⟨151, by decide⟩
  | exact ⟨157, by decide⟩
  | exact ⟨163, by decide⟩
  | exact ⟨167, by decide⟩
  | exact ⟨173, by decide⟩
  | exact ⟨179, by decide⟩
  | exact ⟨181, by decide⟩
  | exact ⟨191, by decide⟩
  | exact ⟨193, by decide⟩
  | exact ⟨197, by decide⟩
  | exact ⟨199, by decide⟩
  | exact ⟨211, by decide⟩
  | exact ⟨223, by decide⟩
  | exact ⟨227, by decide⟩
  | exact ⟨229, by decide⟩
  | exact ⟨233, by decide⟩
  | exact ⟨239, by decide⟩
  | exact ⟨241, by decide⟩
  | exact ⟨251, by decide⟩
  | exact ⟨257, by decide⟩
  | exact ⟨263, by decide⟩
  | exact ⟨269, by decide⟩
  | exact ⟨271, by decide⟩
  | exact ⟨277, by decide⟩
  | exact ⟨281, by decide⟩
  | exact ⟨283, by decide⟩
  | exact ⟨293, by decide⟩
  | exact ⟨307, by decide⟩
  | exact ⟨311, by decide⟩
  | exact ⟨313, by decide⟩
  | exact ⟨317, by decide⟩
  | exact ⟨331, by decide⟩
  | exact ⟨337, by decide⟩
  | exact ⟨347, by decide⟩
  | exact ⟨349, by decide⟩
  | exact ⟨353, by decide⟩
  | exact ⟨359, by decide⟩
  | exact ⟨367, by decide⟩
  | exact ⟨373, by decide⟩
  | exact ⟨379, by decide⟩
  | exact ⟨383, by decide⟩
  | exact ⟨389, by decide⟩
  | exact ⟨397, by decide⟩
  | exact ⟨401, by decide⟩
  | exact ⟨409, by decide⟩
  | exact ⟨419, by decide⟩
  | exact ⟨421, by decide⟩
  | exact ⟨431, by decide⟩
  | exact ⟨433, by decide⟩
  | exact ⟨439, by decide⟩
  | exact ⟨443, by decide⟩
  | exact ⟨449, by decide⟩
  | exact ⟨457, by decide⟩
  | exact ⟨461, by decide⟩
  | exact ⟨463, by decide⟩
  | exact ⟨467, by decide⟩
  | exact ⟨479, by decide⟩
  | exact ⟨487, by decide⟩
  | exact ⟨491, by decide⟩
  | exact ⟨499, by decide⟩
  | exact ⟨503, by decide⟩
  | exact ⟨509, by decide⟩
  | exact ⟨521, by decide⟩
  | exact ⟨523, by decide⟩
  | exact ⟨541, by decide⟩
  | exact ⟨547, by decide⟩
  | exact ⟨557, by decide⟩
  | exact ⟨563, by decide⟩
  | exact ⟨569, by decide⟩
  | exact ⟨571, by decide⟩
  | exact ⟨577, by decide⟩
  | exact ⟨587, by decide⟩
  | exact ⟨593, by decide⟩
  | exact ⟨599, by decide⟩
  | exact ⟨601, by decide⟩
  | exact ⟨607, by decide⟩
  | exact ⟨613, by decide⟩
  | exact ⟨617, by decide⟩
  | exact ⟨619, by decide⟩
  | exact ⟨631, by decide⟩
  | exact ⟨641, by decide⟩
  | exact ⟨643, by decide⟩
  | exact ⟨647, by decide⟩
  | exact ⟨653, by decide⟩
  | exact ⟨659, by decide⟩
  | exact ⟨661, by decide⟩
  | exact ⟨673, by decide⟩
  | exact ⟨677, by decide⟩
  | exact ⟨683, by decide⟩
  | exact ⟨691, by decide⟩
  | exact ⟨701, by decide⟩
  | exact ⟨709, by decide⟩
  | exact ⟨719, by decide⟩
  | exact ⟨727, by decide⟩
  | exact ⟨733, by decide⟩
  | exact ⟨739, by decide⟩
  | exact ⟨743, by decide⟩
  | exact ⟨751, by decide⟩
  | exact ⟨757, by decide⟩
  | exact ⟨761, by decide⟩
  | exact ⟨769, by decide⟩
  | exact ⟨773, by decide⟩
  | exact ⟨787, by decide⟩
  | exact ⟨797, by decide⟩
  | exact ⟨809, by decide⟩
  | exact ⟨811, by decide⟩
  | exact ⟨821, by decide⟩
  | exact ⟨823, by decide⟩
  | exact ⟨827, by decide⟩
  | exact ⟨829, by decide⟩
  | exact ⟨839, by decide⟩
  | exact ⟨853, by decide⟩
  | exact ⟨857, by decide⟩
  | exact ⟨859, by decide⟩
  | exact ⟨863, by decide⟩
  | exact ⟨877, by decide⟩
  | exact ⟨881, by decide⟩
  | exact ⟨883, by decide⟩
  | exact ⟨887, by decide⟩
  | exact ⟨907, by decide⟩
  | exact ⟨911, by decide⟩
  | exact ⟨919, by decide⟩
  | exact ⟨929, by decide⟩
  | exact ⟨937, by decide⟩
  | exact ⟨941, by decide⟩
  | exact ⟨947, by decide⟩
  | exact ⟨953, by decide⟩
  | exact ⟨967, by decide⟩
  | exact ⟨971, by decide⟩
  | exact ⟨977, by decide⟩
  | exact ⟨983, by decide⟩
  | exact ⟨991, by decide⟩
  | exact ⟨997, by decide⟩
  | exact ⟨1009, by decide⟩
  | exact ⟨1013, by decide⟩
  | exact ⟨1019, by decide⟩
  | exact ⟨1021, by decide⟩
  )

set_option maxHeartbeats 4000000 in
/-- **Small windows (`2 < n < 512`).** A prime in `(n, 2n]`, no `native_decide`.
    Two earlier attempts both crashed the native kernel stack:
    (1) chunking only the outer `n`-range and leaving `∃ p < 1024` as one `decide` —
    that inner search alone is past the depth ceiling (`jacobsthal_210` at 210 safe,
    `jacobsthal_2310` at 2310 not, Rings.lean);
    (2) eliminating the search via explicit witnesses but running `interval_cases n`
    on the full width-509 range in one call — 509 is itself past the same ceiling,
    independent of what closes each branch, since `interval_cases`'s case split is
    exactly the kind of construction the ceiling bounds.
    Fix: do both — split the width-509 range into sixteen 32-wide chunks (`rcases
    lt_or_ge`, comfortably under the 210 mark) and run `interval_cases n` only inside
    each 32-wide chunk, closing every resulting literal `n` with `witness_search` (above).
    `maxHeartbeats` raised: this is pure elaboration cost (trying up to 172 candidates per
    literal `n`, 509 literals total), not a stack-depth problem — no `stack_space_exception`
    here, just more arithmetic than the default budget. (Same statement as
    `Erdos.small_window_prime`, redefined here so this file stays free of the Bertrand
    import.) -/
lemma small_window_oracle :
    ∀ n < 512, 2 < n → ∃ p < 1024, n < p ∧ p ≤ 2 * n ∧ Nat.Prime p := by
  intro n hn h2
  rcases lt_or_ge n 32 with hc0 | hc0
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 64 with hc1 | hc1
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 96 with hc2 | hc2
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 128 with hc3 | hc3
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 160 with hc4 | hc4
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 192 with hc5 | hc5
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 224 with hc6 | hc6
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 256 with hc7 | hc7
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 288 with hc8 | hc8
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 320 with hc9 | hc9
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 352 with hc10 | hc10
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 384 with hc11 | hc11
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 416 with hc12 | hc12
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 448 with hc13 | hc13
  · interval_cases n <;> witness_search
  rcases lt_or_ge n 480 with hc14 | hc14
  · interval_cases n <;> witness_search
  interval_cases n <;> witness_search

/-- **Self-contained quantitative kernel.** For `2 < n`, if `(n, 2n]` has no prime then a
    contradiction follows: the lower bound `4^n < n · C(2n,n)` and the empty-window upper bound
    `window_centralBinom_le` on the same integer `C(2n,n)` are incompatible. Built without
    Mathlib's Bertrand theorem. -/
theorem binomial_contradiction {n : ℕ} (hn3 : 2 < n)
    (h_no_prime : ∀ q, n < q → q ≤ 2 * n → ¬ Nat.Prime q) : False := by
  rcases Nat.lt_or_ge n 512 with hsmall | hbig
  · -- small windows: witness from the oracle
    obtain ⟨p, _, hlo, hhi, hp⟩ := small_window_oracle n hsmall hn3
    exact h_no_prime p hlo hhi hp
  · -- large windows: combine the two bounds on C(2n,n)
    have no_prime : ¬∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≤ 2 * n := by
      rintro ⟨p, hp, h1, h2⟩
      exact h_no_prime p h1 h2 hp
    have hub := window_centralBinom_le n hn3 no_prime
    have hmain := threshold_inequality hbig
    have hlb := Nat.four_pow_lt_mul_centralBinom n (by omega)
    have hchain : (4 : ℕ) ^ n < 4 ^ n :=
      calc (4 : ℕ) ^ n < n * Nat.centralBinom n := hlb
        _ ≤ n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) :=
            Nat.mul_le_mul_left n hub
        _ = n * (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by ring
        _ ≤ 4 ^ n := hmain
    exact absurd hchain (lt_irrefl _)

end StructuralBertrand
