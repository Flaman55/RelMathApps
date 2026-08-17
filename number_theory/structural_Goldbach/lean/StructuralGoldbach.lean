import StructuralGoldbach.Basic
import StructuralGoldbach.Bridge
import StructuralGoldbach.Structural
import StructuralGoldbach.Determinism
import StructuralGoldbach.Constructive
import StructuralGoldbach.SelfContainment
import StructuralGoldbach.SmallWitness
import StructuralGoldbach.MovingCeiling
import StructuralGoldbach.AnchorGrowth

/-!
# StructuralGoldbach — the additive structural mechanism

Additive counterpart of `structural_Bertrand` / `structural_Legendre`. The multiplicative
development asks "is there a **prime** in the window" and reduces it, via base self-containment
(`void ⟺ prime`), to a covering estimate. Here the same shape is transported from multiplication
to addition:

* **Multiplicative void** (Bertrand): a number not built from the base by a *multiple* = prime.
  Provable self-containment, because "composite ⟹ factor ≤ √n" is a guaranteed small witness.
* **Additive void** (Goldbach): an even number not built from the base by a *sum of two primes*
  = a Goldbach counterexample. Addition has **no** guaranteed small witness — which is precisely
  where the difficulty lives.

## Modules

* `Basic`  — `hasGoldbachRep`, the margin `repCount`, `isAdditiveVoid`, and the decidable
             finite self-containment `noVoidUpTo` (verified for a concrete range by evaluation).
* `Bridge` — the reduction: `Goldbach ← PositiveMargin` (margin `> 0` everywhere), mirroring the
             Bertrand bridge. No proof of Goldbach is asserted; the open content is the jump from
             a *finite* verified range to *all* `N`.
* `Constructive` — the corrected object of proof: not *counting* (`repCount`, `PositiveMargin`)
             but *constructibility* — what CAN be built from the already-established old base,
             before any new prime from the current window is needed. `CascadeOldBaseSufficiency`
             is the additive analogue of `void_isPrime`: the reach of what a finite base can
             build, not a density estimate of how many ways it can be built.
* `SelfContainment` — the necessity side of additive self-containment, proved unconditionally
             (zero `native_decide`): if a Goldbach representation of `n` exists and `n ≤ B + 2`,
             it is forced into the base `≤ B` on *both* sides (`additiveSelfContained_of_hasGoldbachRep`).
             This complements, not replaces, `windowCovered`'s existence claim on `[4, 2·Pmax]`
             — the two are different theorems (necessity vs. existence), and `B + 2` is shown
             sharp by an explicit example.
* `SmallWitness` — the sharpest reduction so far: computation shows the worst-case witness in
             the old-base cascade grows polylogarithmically (`p ≈ C·(log n)^k`, k≈2.3–2.7,
             not yet pinned down asymptotically), not linearly in `n`. `SmallWitness` states
             exactly this as the single missing estimate; `goldbach_of_smallWitness` shows it
             suffices. Unlike `void_isPrime`'s `minFac ≤ √n`, this bound is not yet an
             elementary arithmetic fact — it is the open content, isolated and named.

The Python tool `structural_goldbach_cascade.py` (parent folder) verifies `noVoidUpTo` and plots the
margin `min repCount` on the working window (empirically `~ n / ln² n`), i.e. the quantity that
`PositiveMargin` must keep off zero.
-/
