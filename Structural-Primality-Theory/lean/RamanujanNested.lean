import RamanujanNested.Defs
import RamanujanNested.Bounds
import RamanujanNested.Monotone
import RamanujanNested.Convergence
import RamanujanNested.ControlledNegative
import RamanujanNested.IdentityChain
import RamanujanNested.Reconstruction
import RamanujanNested.Oscillatory
import RamanujanNested.TargetRadical
import RamanujanNested.UnboundedChain
import RamanujanNested.HerschfeldClosure
import RamanujanNested.PrimeChain
import RamanujanNested.LinearChain
import RamanujanNested.LinearChainGeneral
import RamanujanNested.LinearChainTight

/-!
# RamanujanNested — Lean 4 formalization

Formalization accompanying the paper "Nested Radicals of Ramanujan's Type with
Arbitrary Coefficient Sequences" (A. Flamandzki) — plus, in three of the later
files (`TargetRadical.lean`, `UnboundedChain.lean`, `HerschfeldClosure.lean`),
original extensions of the paper's own general framework (Section 4) to a case
the paper itself doesn't establish: unbounded coefficient sequences. See
"Known gap" below for exactly which of the paper's own claims these extensions
bear on, and `README.md` for a top-level summary.

## Status

Builds cleanly (`lake build`), zero `sorry`, confirmed — including
`PrimeChain.lean`, `LinearChain.lean`, and `LinearChainGeneral.lean`.
`LinearChainTight.lean` added and pending build confirmation (uses
`Real.sq_sqrt` / `linear_combination`, less battle-tested in this project
than the earlier files' tactics).

## What's covered, file by file

* `Defs.lean` — the general recursion `rollUp a T d`, matching Algorithm 1's
  loop with `a 1` always outermost regardless of depth. Seed `T = 1` recovers
  the paper's `R_1^{(N)}` exactly (`truncRadical`); `T = 0` recovers the
  Table 2 "forward evaluation" convention. Also `rStar` (`r*`) and its
  defining property `r*² = 1 + A·r*`.

* `Bounds.lean` — `rollUp_bounded`: Section 4.1's boundedness half
  (`a_k ≤ A` ⟹ every truncation lies in `[0, r*]`). Note: the proof needs no
  lower bound on `a_k` at all — see the file docstring.

* `Monotone.lean` — `truncRadical_monotone`: Section 4.1's monotonicity half
  (`a_k ≥ 0` ⟹ the truncated sequence is nondecreasing in depth).

* `Convergence.lean` — `truncRadical_converges`: combines the two above via
  Mathlib's monotone-bounded convergence theorem to get the paper's actual
  stated conclusion — existence of a finite limit as `N → ∞`. This is the
  piece flagged as missing in the first pass.

* `ControlledNegative.lean` — Lemma 1: coefficients may dip to `-A₋` (with
  `A₋ ≤ 1/r*`) and the radicand at every step stays nonnegative — the
  "well-defined in ℝ" claim, made precise (Lean's `Real.sqrt` is total and
  would silently return `0` on negative input, so boundedness of the output
  alone would not capture what the paper means by this).

* `IdentityChain.lean` — Appendix A.1, Algorithm 3: the closed form
  `R_k = N+k-1` satisfies the stated recursion exactly, for any `N ≥ 2`.

* `Reconstruction.lean` — Algorithm 4, the general inverse construction: for
  ANY target profile `R`, the coefficient `(R_k²-1)/R_{k+1}` makes `R`
  satisfy the recursion. `IdentityChain.lean`'s Algorithm 3 is recovered as
  the special case `R_k = N+k-1` (`reconstructCoeff_chainClosedForm`).

* `Oscillatory.lean` — Appendix A.2's `a_k = 1 + α sin k` family. Bounds it
  unconditionally within `[1-α, 1+α]`; shows `0 ≤ α ≤ 1` needs none of
  Lemma 1's machinery; states the paper's vague "provided α satisfies the
  admissibility constraints of Lemma 1" as the explicit, checkable inequality
  `α ≤ 1/rStar(1+α)`; and discharges it concretely at `α = 1/10`.

* `TargetRadical.lean` — not from the paper directly, but from working out
  a strategy for the gap below: instead of proving the classical unbounded
  `a_k = k` radical converges, build a genuinely different, structurally
  simple radical from a CONSTANT coefficient `a_k = t - 1/t`, and prove it
  converges to the target `t` *exactly* — with an explicit geometric error
  bound, using only `Bounds.lean`'s already-built machinery (no new gap
  introduced). `targetRadical_tendsto` is the main result.

* `UnboundedChain.lean` — a genuine, if partial, advance on the gap below:
  for the paper's own Algorithm-3 family `a_k = N+k-2` (unbounded, same shape
  as classical `a_k = k` up to a shift), a *moving-ceiling* induction proves
  the truncated radical converges to a finite limit `L ≤ N`
  (`classicalRadical_converges`) — a family Section 4.1 as stated does not
  cover at all. Whether `L = N` exactly is still open; the file docstring
  records a concrete attempt (a tail-sensitivity/telescoping estimate) that
  was tried and found too lossy, rather than leaving the difficulty
  unstated.

* `HerschfeldClosure.lean` — closes the exact-value half of the gap below.
  `limitVal_functional_eq` derives `L(N) = √(1+(N-1)L(N+1))` by passing the
  paper's own recursion to the limit; `deficit_recursion` and (the key new
  result) `deficit_growth` turn this into a single GLOBAL bound
  `δ(N+1) ≥ δ(N)(N+1)/(N-1)` — no arbitrary cutoff, valid everywhere, using
  only the trivial ceiling `δ(N) ≤ N-1`. Telescoped over `j` steps this beats
  the linear ceiling quadratically, forcing `δ ≡ 0`, i.e. `L(N) = N` exactly
  (`limitVal_eq_self`). No `sorry`, confirmed building.

* `PrimeChain.lean` — targets the last genuinely unformalized case:
  `a_k = p_k` (Appendix A.2). Primes have no
  algebraic self-similarity under shifting, so `UnboundedChain.lean`'s exact
  technique doesn't transfer. Instead: a general `rollUp_geomBounded` lemma
  (any coefficient growing at most geometrically, `a_k ≤ r^k` for fixed
  `r > 1`, already gives a genuine depth-independent ceiling, via a moving
  ceiling `A·r^i` that closes to a fixed constant at the top level); primes
  satisfy `p_k ≤ 4^k` (`nth_prime_le_four_pow`), itself derived from
  Bertrand's postulate (Mathlib's `Nat.bertrand`, not Artur's own
  independently-verified `structural_bertrand` — see the file docstring for
  why, and how to swap it in). Result: `primeRadical_converges` — EXISTENCE
  of a finite limit only, not the exact value (unlike `HerschfeldClosure`'s
  `L(N) = N`). This is a materially weaker claim than the linear family's
  closure, chosen deliberately: existence is the bar the paper itself leaves
  open, and this is enough to clear it without needing the exact-value
  machinery primes don't admit.

* `LinearChain.lean` — generalizes `UnboundedChain.lean` from slope exactly
  `1` (`a_k = N+k-2`) to any slope `m ≥ 1` (`linearCoeff m N k = N+m(k-2)`),
  via the same moving-ceiling technique with the ceiling now shifting by `m`
  per layer instead of by a fixed `1`. The linear closed-form ansatz used in
  `HerschfeldClosure.lean` only balances when `m² = 1`, so slope `1` is the
  only slope with a known exact value; `linearRadical_converges` gives
  existence only for `m ≥ 1` in general (`L ≤ N`), the same weaker bar as
  `PrimeChain.lean`. Confirmed recovering `UnboundedChain.lean` exactly at
  `m = 1` (`linearRadical_converges_one`). Not from the paper — motivated by
  checking whether a literature family with a different linear slope
  (Kusniec's difference-of-oblongs Radiciatory, slope `q-1`) could be
  absorbed; it is, for every `q ≥ 2`.

* `LinearChainGeneral.lean` — closes the remaining `0 < m < 1` range left
  open by `LinearChain.lean`, and in fact covers all `m > 0` in a single
  argument, by using a looser ceiling `C(N) = N+1` instead of `C(N) = N`.
  The key inequality becomes `0 ≤ N+m+m²`, true unconditionally for `m > 0`
  — no case split on the slope is needed. Gives the weaker bound `L ≤ N+1`
  (use `LinearChain.lean`'s `linearRadical_converges` instead whenever
  `m ≥ 1`, for the tight `L ≤ N`). With this file, Kusniec's
  difference-of-oblongs family is covered for every `q > 1`, not just `q ≥ 2`
  — existence of a limit is now known across the entire positive-slope
  range.

* `LinearChainTight.lean` — replaces `LinearChainGeneral.lean`'s loose
  `+1` slack with the exact minimal shift `s(m) = (√(5m²+4)-3m)/2` (the
  positive root of the equality case `s²+3ms+m²=1`), giving the tightest
  bound this technique can give for every `m` in `(0,1]`: `L ≤ N+s(m)`,
  matching `LinearChain.lean`'s `L ≤ N` exactly at `m=1` (`tightShift_one`).
  Together with `LinearChain.lean` (`m ≥ 1`), this closes the entire
  positive-slope range with the tightest available bound at every point —
  no gap remains for existence of a limit across `m > 0`.

## Known gap in the paper itself (largely resolved here)

Section 5.1 claims the classical Ramanujan radical (`a_k = k`) converges "by
the general boundedness results established in Section 4.1" — but `a_k = k`
is unbounded, so `Bounds.lean`'s hypothesis (`a_k ≤ A` for a fixed `A`) is
never satisfied. The same issue affects the prime-coefficient example
(`a_k = p_k`, Appendix A.2), which the paper also attributes to "the bounds
established in Section 4.1."

`UnboundedChain.lean` + `HerschfeldClosure.lean` together now give existence
*and* the exact value (`L(N) = N`) for the family `a_k = N+k-2`, via a
moving-ceiling induction plus a functional-equation argument Section 4.1
doesn't state — fully proven, no `sorry`. The classical radical is `N = 3`;
`a_k = k` is already covered too, with no reindexing needed at all — it is
exactly `N = 2` (`classicalCoeff 2 k = 2+k-2 = k`), so `limitVal_eq_self`
applied at `N = 2` gives `a_k = k` converging to `2`, not the classical
value `3` (the paper's own "classical" formula and the `a_k = k`
attribution both had an indexing error — see below). The prime-coefficient
example now has an existence-only answer via `PrimeChain.lean`
(`primeRadical_converges`, confirmed building); its exact value remains
open, as it does in the paper.
`TargetRadical.lean` sidesteps this gap rather than closing it: a distinct,
provably-convergent constant-coefficient radical reaching the same targets,
built from the paper's own general framework (Section 4, constant `f`) —
"a different product of equivalent strength," not a fix for the classical
construction itself.

## Not attempted

The higher-order-root variants (Section 5.2, a different nonlinear operator)
and the complex-valued extension mentioned in the Conclusion.
-/
