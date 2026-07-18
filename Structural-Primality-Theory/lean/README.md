# RamanujanNested

A Lean 4 / Mathlib formalization accompanying the paper **"Nested Radicals of
Ramanujan's Type with Arbitrary Coefficient Sequences"** (A. Flamandzki),
plus original extensions of the paper's own general framework to a case the
paper itself does not establish.

Builds cleanly against `lake build`, zero `sorry`.

The paper itself has been revised to a second version incorporating what this
formalization effort found (see "Errors this formalization caught" below).
It is published on Zenodo: <https://zenodo.org/records/18071173>
(DOI: 10.5281/zenodo.18071173), and that version's own new "Formal
Verification" section points back to this repository.

## What this repository formally verifies

The paper studies the recursion

```
R_k = √(1 + a_k · R_{k+1})
```

for an arbitrary coefficient sequence `(a_k)`. The classical Ramanujan
radical is the instance `a_k = k+1` (equivalently `N = 3` of the family
below), converging to `3`; the related sequence `a_k = k` is a *different*
instance (`N = 2`) converging to `2`, not to the classical value — see the
next section.

**Faithful to the paper (Section 4.1, Lemma 1, Appendix A):**

- **Boundedness and monotonicity** (`Bounds.lean`, `Monotone.lean`): if
  `a_k ≤ A` for a fixed ceiling `A`, every truncation of the radical lies in
  `[0, r*]` where `r* = (A+√(A²+4))/2`; if additionally `a_k ≥ 0`, the
  truncated sequence is monotone increasing in depth.
- **Convergence** (`Convergence.lean`): combining the two above, the
  truncated radical has a finite limit as depth `→ ∞` — the paper's actual
  stated conclusion for its main sufficient condition.
- **Lemma 1 — controlled negative coefficients** (`ControlledNegative.lean`):
  coefficients may dip negative (down to `-A₋`, `A₋ ≤ 1/r*`) and the radicand
  at every step is guaranteed nonnegative — made precise against Lean's
  `Real.sqrt`, which is total and would otherwise silently mask a
  well-definedness failure.
- **Algorithm 3, the closed-form identity chain** (`IdentityChain.lean`):
  `R_k = N+k-1` satisfies the recursion exactly, for any target `N ≥ 2`.
- **Algorithm 4, the general inverse construction** (`Reconstruction.lean`):
  for *any* target profile `R`, the coefficient `(R_k²-1)/R_{k+1}` makes `R`
  satisfy the recursion; Algorithm 3 is recovered as the special case
  `R_k = N+k-1`.
- **The oscillatory coefficient family** (`Oscillatory.lean`,
  `a_k = 1 + α sin k`, Appendix A.2): the paper's informal "provided α
  satisfies the admissibility constraints of Lemma 1" is made an explicit,
  checkable inequality (`α ≤ 1/r*(1+α)`) and discharged concretely at
  `α = 1/10`.

## Errors this formalization caught (now fixed in v2 of the paper)

Trying to state the paper's claims precisely enough to formalize them
surfaced two genuine issues in the original text — not literature-based
concerns, but concrete, checkable mistakes:

1. **A false attribution in Section 5.1.** The paper claimed the classical
   Ramanujan radical converges "by the general boundedness results
   established in Section 4.1." That theorem requires a fixed ceiling
   `a_k ≤ A`; the classical coefficients `a_k = k+1` have no such ceiling, so
   the attribution does not literally hold. Formalizing Section 4.1's actual
   hypothesis (`Bounds.lean`) is what exposed this — the gap was invisible
   until someone had to write down exactly what "the boundedness results"
   require. `UnboundedChain.lean` and `HerschfeldClosure.lean` (below) supply
   the missing proof instead of just flagging the hole.

2. **An indexing error in the paper's own displayed formula.** The
   introduction's headline equation,
   `R = √(1 + √(1 + 2√(1 + 3√(1 + ⋯))))`, has one extra layer relative to the
   well-known Ramanujan identity `3 = √(1+2√(1+3√(1+4√(1+⋯))))` — the paper's
   version wraps an additional `√(1+1·(⋯))` around the genuine classical
   radical. Since the inner expression already equals `3`, the paper's own
   formula evaluates to `√(1+3) = 2`, not `3`. This surfaced while integrating
   the Lean results back into the paper text (Section 5.1 stated
   `a_k = k`, which is consistent with the miscounted formula but not with
   the classical value) — checked by direct computation against the standard
   identity, not from secondary literature. Both the formula and the
   `a_k = k` attribution are corrected in v2.

## The unbounded-coefficient gap, and what this repository does about it

- **`TargetRadical.lean`** — sidesteps the gap rather than closing it. A
  *constant* coefficient `a = t - 1/t` is shown to make the radical converge
  to the target `t` exactly, with an explicit geometric error bound, using
  only the already-proven bounded-coefficient machinery. A different,
  structurally simpler, faster-converging construction reaching the same
  targets — not a fix for the classical radical itself.
- **`UnboundedChain.lean`** — extends Section 4.1 to the specific unbounded
  family `a_k = N+k-2` (the classical radical is `N=3`; `a_k=k` is `N=2`). A
  *moving-ceiling* induction (the bound at depth `d` is `N` itself, not a
  fixed constant) proves the truncated radical has a finite limit `L ≤ N`.
- **`HerschfeldClosure.lean`** — closes the gap for this family. Deriving a
  functional equation `L(N) = √(1+(N-1)·L(N+1))` from the recursion in the
  limit, then a deficit recursion and a global multiplicative growth bound
  (`δ(N+1) ≥ δ(N)·(N+1)/(N-1)`, valid everywhere, no arbitrary cutoff), the
  deficit `δ(N) = N - L(N)` is shown to grow quadratically in the step count
  against a merely linear ceiling — forcing `δ ≡ 0`. **`limitVal_eq_self`
  proves `L(N) = N` exactly** for this family: a genuine (if not previously
  published, to the author's knowledge) convergence theorem in the spirit of
  Herschfeld's classical result on infinite nested radicals, proved from
  scratch rather than cited.

The sequence `a_k = k` is already covered directly, with no reindexing
needed: it is exactly the `N = 2` instance of `a_k = N+k-2`, so
`HerschfeldClosure.lean`'s `limitVal_eq_self` applied at `N = 2` gives
`a_k = k` converging to `2`.

- **`PrimeChain.lean`** — an existence-only answer for the prime-coefficient
  example (`a_k = p_k`, Appendix A.2), the one case with a genuinely
  different, non-linear growth shape that the `N+k-2` family's technique
  doesn't reach (primes have no algebraic self-similarity under shifting).
  A general lemma, `rollUp_geomBounded`, shows that ANY coefficient sequence
  growing at most geometrically (`a_k ≤ r^k` for some fixed `r > 1`) already
  has a genuine, depth-independent ceiling, via a moving bound `A·r^i` that
  closes to a fixed constant at the top level. Primes satisfy `p_k ≤ 4^k`
  (`nth_prime_le_four_pow`), itself proved from Bertrand's postulate
  (Mathlib's `Nat.bertrand`). Result: **`primeRadical_converges`** — the
  truncated radical for `a_k = p_k` has SOME finite limit. Unlike
  `HerschfeldClosure.lean`, this does not pin down the exact value — existence
  is a substantially lower bar, and it's the bar the paper itself leaves open
  for this case.

With `PrimeChain.lean`, every coefficient family the paper mentions by name
now has at least an existence-of-convergence result; only the *exact value*
for `a_k = p_k` remains open, as it does in the paper itself.

**Not attempted:** the higher-order-root variants (Section 5.2) and the
complex-valued extension mentioned in the paper's conclusion.

## Repository structure

```
RamanujanNested.lean              -- root import + full status summary
RamanujanNested/
  Defs.lean                       -- the recursion, truncRadical, r*
  Bounds.lean                     -- Section 4.1, boundedness
  Monotone.lean                   -- Section 4.1, monotonicity
  Convergence.lean                -- Section 4.1, convergence
  ControlledNegative.lean         -- Lemma 1
  IdentityChain.lean               -- Appendix A.1, Algorithm 3
  Reconstruction.lean              -- Appendix A.1, Algorithm 4
  Oscillatory.lean                 -- Appendix A.2
  TargetRadical.lean                -- constant-coefficient exact-target radical
  UnboundedChain.lean                -- moving-ceiling existence for a_k = N+k-2
  HerschfeldClosure.lean              -- exact-value closure, L(N) = N
  PrimeChain.lean                     -- existence of a limit for a_k = p_k
```

## Building

```sh
lake exe cache get
lake build
```

Pinned toolchain: `leanprover/lean4:v4.14.0`; Mathlib at `v4.14.0`.
