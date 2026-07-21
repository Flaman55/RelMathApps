# StructuralGoldbach — Lean 4 formalization

Machine-checked formalization of the **additive** instance of the structural window
mechanism — the same object that closes Bertrand's postulate (`StructuralBertrand`,
sibling project), transported from multiplication to addition.

**Status: reduction chain fully verified — zero `sorry`, no extra axioms beyond
Mathlib — down to two named, computationally measured, unproved estimates.**
Every logical step from the window construction to `Goldbach` is machine-checked;
what remains open is isolated into exactly two propositions (`WitnessStepBound`,
`AnchorDoublingRate`), stated precisely enough to be attacked, cited, or refuted on
their own.

## Why Goldbach resists the classical toolbox

Stated plainly, without hedging: the binary Goldbach conjecture has no accepted
structural theory. Sieve methods bound the counting function
`r(n) = #{(p,q) : p, q prime, p+q=n}` from above and below, but the lower bound one
can prove unconditionally (Chen's theorem gives `p + P₂`, a prime plus a product of
at most two primes, not `p+q`) never reaches positivity for `r(n)` itself — this is
the parity problem (Selberg): elementary and analytic sieves of Eratosthenes type
are structurally blind to the difference between `n` having an odd or even number of
prime factors, and closing that blindness is exactly what a proof of Goldbach would
need to do. Absent a structural account of *why* a window must contain a
representation — as opposed to *how many* it is expected to contain on average — the
problem is verified by direct combinatorial search (computer verification up to
`4 × 10^18`, Oliveira e Silva et al.) and otherwise open. There is, to date, no
accepted assumption-free reduction of the general statement to a single finite
estimate.

## The shared mechanism: a structural window

This project is one instance of a single mechanism used across a family of
problems (`StructuralBertrand`, `StructuralGoldbach`, and, in the underlying window
construction, `StructuralLegendre`):

* **Base.** A complete, deterministically known finite object — the primes `≤ P_max`.
* **Window.** The maximal territory over which the base's reach is *provably*
  deterministic: `(P_max, 2·P_max]` in the multiplicative case (composites in
  the window are fully built from the base, because their smallest prime factor is
  `≤ √(2·P_max) < P_max` once the window is entered), and the analogous additive
  range in the Goldbach case (`Determinism.lean`, `void_isPrime`).
* **Self-containment.** A position in the window that the base cannot build is
  forced to be a new generator — a prime, in the multiplicative case
  (`window_composite_smooth` in `StructuralBertrand`); a genuine new even number with
  no counterexample status yet decided, in the additive case.
* **Cascade.** The window's newly certified content becomes part of the base for
  the next window, `P_max → 2·P_max → 4·P_max → …`, propagating the mechanism to
  infinity.

The mechanism itself is elementary and, once stated, almost mechanical to apply —
the difficulty in every instance is entirely in **closing the single quantitative
atom** the mechanism reduces the problem to. `StructuralBertrand` closes its atom
unconditionally, on the central binomial coefficient (see that project's README).
This project isolates the Goldbach atom as sharply as the mechanism allows and
records exactly what closing it would require; it does **not** claim to have closed
it. The same window idea, applied to the growth rate of the base itself
(`AnchorDoublingRate` below), touches the territory of unconditional prime-gap
theorems (Baker–Harman–Pintz-type bounds on the largest prime below `2x`) without
using or reproving them — see *Open estimates*.

## What is proved, and by what means

**1. Constructibility, not counting (`Constructive.lean`).**
The classical framing asks "how many representations does `n` have" (`repCount`,
`Basic.lean`/`Bridge.lean` — kept for comparison, not the active line of proof). The
structural framing asks a different, prior question: what can be *built* from an
already-established, finite, concrete base — before any new prime supplied by the
current window is even needed. Verified computationally without exception
(Python cascade, `N = 3 000 000`) and used as the definition of
`CascadeOldBaseSufficiency`: every even number in a cascade segment
`(top k, top (k+1)]` is a sum of two primes with the smaller one drawn from the
*old* base `≤ top k`. `nextAnchor_gt`, `anchor_lt_succ`, `exists_step_containing`
(monotonicity and unboundedness of the cascade) are proved unconditionally from
Bertrand's postulate alone — zero `sorry`.

**2. The reduction chain (`SmallWitness.lean`, `MovingCeiling.lean`).**
```
Goldbach  ←  SmallWitness  ←  WitnessStepBound  ∧  AnchorDoublingRate
```
`SmallWitness` sharpens constructibility further: a witness prime bounded not by the
old base (order `n`) but by a polylogarithmic quantity, `p ≤ C·(log n)^k` —
the additive analogue of the unconditional multiplicative fact "every composite has
a prime factor `≤ √n`". Proving `SmallWitness` directly, by bounding the
analytic "leak" of semiprimes with a Brun–Titchmarsh-type sieve, was attempted and
found to fail exactly at the parity problem: an unconditional lower sieve of
dimension 2 needs a threshold `z = n^(1/s)` with `s > ~4.8`, while a
controllable leak needs `s < ~2.1` — the two thresholds do not meet (computed,
`n = 10^6`; see project history). `SmallWitness` is therefore **not** attacked
directly; it is derived, instead, from two independent and individually sharper
estimates via `smallWitness_of_stepBound_and_doublingRate` (`MovingCeiling.lean`,
fully proved, zero `sorry`) — a moving-ceiling argument adapted from the
convergence technique in the sibling `RamanujanNested/PrimeChain.lean` project
(fixed ceilings fail for unbounded sequences; a ceiling that moves with the
recursion's own depth, anchored by Bertrand's postulate, closes where a flat bound
cannot).

## Open estimates

Both are measured, precisely stated, and unproved. Neither is a restatement of
Goldbach itself — each is strictly narrower in scope than `r(n) > 0`.

**`WitnessStepBound`.** The worst-case witness in cascade step `k` is bounded by a
polynomial in `k`, not in the size of the base. Measured (Python,
`witness_scan.py`, cascade up to base `~ 81.6 × 10^6`, step `k ≤ 26`,
no exception): degree `~ 2`, constant `~ 3`. This is the sharper,
harder half — structurally analogous to the (also open) least-Goldbach-witness
conjecture in the analytic literature.

**`AnchorDoublingRate`.** The cascade's own anchors grow geometrically,
`anchor(k) ≥ c·2^k`. Bertrand's postulate gives only the matching *upper*
bound (`anchor(k+1) ≤ 2·anchor(k)`) — the wrong direction for converting a
step-indexed bound into a size-indexed one; a genuine lower bound is a separate,
classical fact about the largest prime below `2x` being asymptotically close to
`2x`, i.e. about prime gaps being `o(x)` — a consequence of the Prime Number
Theorem, and far short of what Baker–Harman–Pintz-strength results would give.
Measured: the ratio `anchor(k+1)/anchor(k)` converges to exactly `2.000` from
`k ~ 16` onward. This half looks tractable from existing unconditional
gap theorems; it has not been formalized here.

Closing either estimate — or replacing it with a weaker sufficient one — plugs
directly into `smallWitness_of_stepBound_and_doublingRate` without touching
anything else in the chain.

**Partial progress on `AnchorDoublingRate` (`AnchorGrowth.lean`).** Mathlib
`v4.14.0` has neither the Prime Number Theorem nor a prime-gap bound to cite for
the geometric lower bound above, so this file builds an unconditional, elementary
substitute from what Mathlib does have: Bertrand's postulate and Erdős's proof
that `∑ 1/p` diverges (`not_summable_one_div_on_primes`,
`Mathlib.NumberTheory.SumPrimeReciprocals`). A growing squarefree modulus
`modulus m = ∏_{p<m} p` has totient density `φ(modulus m)/modulus m =
∏_{p<m}(1-1/p) → 0` (`tendsto_density_zero`, via `1-x ≤ exp(-x)` and the
divergence of `∑1/p`); feeding this density bound into Mathlib's unconditional
Legendre-sieve estimate `Nat.primeCounting'_add_le` yields
`anchorSuperlinear : Tendsto (fun k ↦ (anchor k : ℝ) / k) atTop atTop` — the
cascade's anchors grow strictly faster than linearly in the step count `k`,
proved outright, zero `sorry`. This is **weaker** than `AnchorDoublingRate`:
it is qualitative (a `Tendsto`, no explicit rate or exponent), whereas the
polynomial degree (`~2`) measured in `WitnessStepBound` needs an *explicit*
growth rate to compose into `smallWitness_of_stepBound_and_doublingRate`.
`anchorSuperlinear` therefore stands on its own for now — a genuine, proved
fact about the cascade that is not yet wired into the reduction chain above.
Strengthening it to an explicit rate (or finding a different composition route)
remains open.

## Trust base

`native_decide` (compiled evaluation) discharges the finite cascade checks
(`anchor 0..4`, `buildableFromBaseDec` instances in `Constructive.lean`,
`noVoidUpTo`/`windowCoveredDec` in `Basic.lean`/`Structural.lean`) — bounded,
externally re-checkable computations. `AnchorGrowth.lean` uses no `native_decide`
at all — it is ordinary `Prop`-level analysis built on Bertrand's postulate and
Mathlib's `not_summable_one_div_on_primes`. No axiom beyond Mathlib and
`native_decide` is used anywhere in the chain.

```sh
grep -rn "sorry" StructuralGoldbach     # no matches
```

## Exact versions (required for reproduction)

| Component | Pin |
|---|---|
| Lean toolchain | `leanprover/lean4:v4.14.0` (file `lean-toolchain`) |
| Mathlib | tag `v4.14.0`, commit `4bbdccd9c5f862bf90ff12f0a9e2c8be032b9a84` |

Transitive dependencies (from `lake-manifest.json`, manifest format `1.1.0`):

| Package | Commit |
|---|---|
| batteries | `8d6c853f11a5172efa0e96b9f2be1a83d861cdd9` |
| aesop | `5a0ec8588855265ade536f35bcdcf0fb24fd6030` |
| proofwidgets | `68280daef58803f68368eb2e53046dabcd270c9d` |
| Qq | `303b23fbcea94ac4f96e590c1cad6618fd4f5f41` |
| importGraph | `519e509a28864af5bed98033dd33b95cf08e9aa7` |
| LeanSearchClient | `d7caecce0d0f003fd5e9cce9a61f1dd6ba83142b` |
| plausible | `42dc02bdbc5d0c2f395718462a76c3d87318f7fa` |
| Cli | `726b3c9ad13acca724d4651f14afc4804a7b0e4d` |

## Build

```sh
lake exe cache get      # download prebuilt Mathlib oleans for the pinned commit
lake build
```

A successful `lake build` reports **no errors, no `sorry`, and no warnings in
project files** (doc-string lint notices replayed from Mathlib's own files are
expected and harmless).

## File map

| File | Content |
|---|---|
| `StructuralGoldbach/Basic.lean` | `hasGoldbachRep`, the counting margin `repCount`, `isAdditiveVoid`, finite self-containment `noVoidUpTo` (kept for comparison; the counting framing, not the active line of proof) |
| `StructuralGoldbach/Bridge.lean` | `Goldbach ← PositiveMargin ← HL_Floor` — the classical (counting) reduction, superseded below but kept as the baseline it improves on |
| `StructuralGoldbach/Structural.lean` | Deterministic window `(P_max, 2P_max]`; `Goldbach ⟺` every window covered (`goldbach_iff_all_windows`) |
| `StructuralGoldbach/Determinism.lean` | `void_isPrime` — additive analogue of self-containment: an uncovered window position with no base factor is forced prime, range `2P_max < P_max^2` |
| `StructuralGoldbach/Constructive.lean` | Constructibility, not counting: `buildableFromBase`, the cascade `anchor`/`top`, `CascadeOldBaseSufficiency`; monotonicity/unboundedness of the cascade (`nextAnchor_gt`, `anchor_lt_succ`, `exists_step_containing`), proved from Bertrand alone |
| `StructuralGoldbach/SmallWitness.lean` | `SmallWitness` (polylogarithmic witness) and `goldbach_of_smallWitness` — the sharpest single-estimate reduction |
| `StructuralGoldbach/MovingCeiling.lean` | The two open estimates (`WitnessStepBound`, `AnchorDoublingRate`) and the fully proved bridge `smallWitness_of_stepBound_and_doublingRate`, adapting the moving-ceiling technique of `RamanujanNested/PrimeChain.lean` |
| `StructuralGoldbach/AnchorGrowth.lean` | `anchorSuperlinear` — unconditional proof that `anchor(k)/k → ∞`, built from Bertrand's postulate and Erdős's `∑1/p` divergence via a growing squarefree modulus and Mathlib's Legendre-sieve bound; qualitative progress on `AnchorDoublingRate`, not yet composed into the chain |

## Provenance

The moving-ceiling closure technique is adapted, not original to this project: it
is the same device that closes existence (not the exact value) for the
prime-coefficient nested radical in the sibling `RamanujanNested/PrimeChain.lean`
project — a fixed ceiling fails for an unbounded sequence, and a ceiling that moves
with recursion depth, anchored by Bertrand's postulate, closes where the fixed one
cannot. `StructuralGoldbach` transports the same shape from a continuous convergence
argument to a discrete existence argument.

## License / citation

Cite alongside the accompanying Bertrand and Legendre structural papers. The
formalization makes the logical status of the Goldbach attempt unambiguous: the
window mechanism and the full reduction chain down to `WitnessStepBound ∧
AnchorDoublingRate` are machine-verified; no claim of a proof of Goldbach's
conjecture is made or implied anywhere in this repository.
