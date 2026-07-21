import StructuralLegendre.Basic
import StructuralLegendre.Reframing
import StructuralLegendre.Covering
import StructuralLegendre.Counting
import StructuralLegendre.Forcing
import StructuralLegendre.CoveredRun
import StructuralLegendre.Jacobsthal
import StructuralLegendre.SmallAnchors
import StructuralLegendre.Determinism
import StructuralLegendre.Unification
import StructuralLegendre.WidthLaw
import StructuralLegendre.Legendre
import StructuralLegendre.GeneralLaw
import StructuralLegendre.Certificate
import StructuralLegendre.Bridge

/-!
# StructuralLegendre — the coupled-window mechanism

Companion development to `structural_bertrand`. The aim is NOT to prove Legendre's conjecture
(open), but to formalize the *generalized* structural mechanism behind "there is a prime in
`(A, A+W]`", and to make the coupling between the window's **position/speed** and its **width**
explicit. Bertrand (`A=k`, `W=k`, `(n,2n]`) and Legendre (`A=k²`, `W=2k+1`, `(n²,(n+1)²]`) are
two settings of these coupled sliders.

## Two determinisms

* **Base determinism (self-containment):** every composite in the window is built entirely from
  the base; reach `2·Pmax`. Marks the window.
* **Generative determinism (void ⟺ prime):** the sieve decides primality; reach the square
  scale `(Pmax, Pmax²)`. Inside it, a void is prime.

## Modules

* `Basic`      — anchor-agnostic core: `coupledWindow`, `activeBase` (primes `≤ √top`), `isVoid`,
                 `windowHasVoid`; the `bertrandWindow` / `legendreWindow` instances.
* `Reframing`  — Legendre as Bertrand narrowed from the left: `legendreWindow_narrowed`,
                 `legendreWindow_subset_doubling` (Legendre ⊆ same-top doubling window).
* `Covering`   — the covering / void duality (`windowHasVoid ↔ ¬ windowCovered`), decidable, so
                 concrete windows are settled by evaluation.
* `Counting`   — the atom in counting form: `windowHasVoid ↔ coveredCount < W`.
* `Forcing`    — voids are coprimes to the ring product: `isVoid ↔ Coprime (activeBaseProd) n`,
                 hence `windowHasVoid ↔ ∃ coprime in window` — the input to the Jacobsthal bound.
* `CoveredRun` — the *local* forcing quantity: longest covered run inside the window; stays small
                 while the width grows (the coupled window loosens). Corrects the global-`g` picture.
* `Jacobsthal` — the structural floor `g(M)` (computable); small active-ring values `g(6)=4`,
                 `g(30)=6`, `g(210)=10`, `g(2310)=14`, matching `structural_bertrand`.
* `SmallAnchors` — the anchor experiment closed: every window of width `g(M)` contains an
                 `M`-coprime, for anchors `3,5,7,11` (decidable core + periodic lift).
* `Determinism` — generative determinism `void ⟹ prime` (`prime_of_isVoid`), the
                 least-prime-factor argument.
* `Unification` — one anchor `A`, base `≤ √(2A)`, any width `W ≤ A` in the reach: survivors are
                 new primes. Bertrand (`W=A`) and Legendre (`W=2⌊√A⌋`) as two widths of one object.
* `WidthLaw`   — the family by width law `W : ℕ → ℕ`; `GapCertificate W` (forces a prime at every
                 anchor). Bertrand's law closed to infinity (via Mathlib); Legendre's law is open.
* `GeneralLaw` — the target: `GeneralLaw` (every width from Legendre to Bertrand, at every anchor).
                 From it, `legendreConjecture_of_generalLaw`, `bertrand_of_generalLaw`, and a prime
                 in any window follow — the general law gives everything.
* `Legendre`   — the instances: `LegendreVoid n`, `LegendreConjecture` (target, open),
                 `exists_prime_between_squares` (void ⟹ prime between squares), and the concrete
                 windows including the crossover `n = 42`.
* `Certificate` — the generalized forcing `WindowForcing A W` (free position and width) with
                 Bertrand and Legendre as two evaluations; Legendre is a by-product, not the aim.
* `Bridge`     — the existential entry point: `prime ⟹ void` and `generalLaw_of_shortInterval`.
                 Plug in any short-interval prime-existence result and the whole mechanism closes.

## Plan (development)

1. **Structural forcing (Jacobsthal floor).** `W > g(M)` for `M = ∏(active rings ≤ √top)`
   forces a void — via CRT, no analytic input.
2. **Small active-ring sets** by `native_decide` (anchor `3,5,7` → `g = 4,6,10`): the pattern
   `windowHasVoid ⟺ W > g(active primorial)` (the same `g(30),g(210),g(2310)` as Bertrand).
3. **Instances and the crossover.** Bertrand forced at all scales; Legendre forced for `n ≤ 41`,
   first failure `n = 42`, window `(1764, 1849]`, where `g(M)` overtakes the width `2n+1`.
4. **The certificate.** The swappable inequality `g(∏ p≤√T) < 2√T` for all `T` — OPEN, since the
   Jacobsthal floor outgrows the width; this is the frontier the mechanism localizes.
-/
