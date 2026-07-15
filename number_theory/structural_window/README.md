# The coupled-window mechanism — Bertrand, Legendre, and everything between

## What this is

A companion to the `structural_bertrand` development. The goal here is **not** to prove
Legendre's conjecture (it is open — one of Landau's four problems). The goal is to
**generalize the structural mechanism** behind "there is a prime in a moving window" and to
derive the relation that couples two quantities: the **speed** at which the window slides
along ℕ and the **width** of the window. Legendre's conjecture is then read off as one
**special case** of that relation — a by-product, not the target.

## The two-slider model

Every statement of the form "each window `(A_k, A_k + W_k]` contains a prime" is governed by
two coupled sliders:

- **Slider 1 — position / speed.** How fast the left endpoint `A_k` (the anchor) advances
  with `k`.
- **Slider 2 — width.** The window width `W_k`.

They are coupled by a trade-off:

> Move the window to the right faster → the width may be made smaller.
> Slow the slide down → the width must be made larger.

for a prime to be forced in *every* window. The two classical theorems are two settings of
these sliders:

| Statement | Anchor `A_k` | Width `W_k` | Window | Slider reading |
|-----------|--------------|-------------|--------|----------------|
| Bertrand  | `k`          | `k`         | `(n, 2n]`       | slow slide (linear), wide window (constant fraction) |
| Legendre  | `k²`         | `2k+1`      | `(n², (n+1)²]`  | fast slide (quadratic), narrow window (~`√`anchor)   |

Bertrand and Legendre are therefore the **same object** — a coupled pair of sliders — read at
two different positions. The difference between them is not a difference of kind, only of
where the two sliders are set.

## Legendre as Bertrand, narrowed from the left

The relationship is sharper than "two settings": fix the **top** `T` (hence the base `≤ √T`).
Then Bertrand and Legendre are two windows with the *same top and the same sieving base*,
differing only in the left edge:

- **Bertrand:** `(T/2, T]` — width `T/2`;
- **Legendre:** `(T − 2√T, T]` — width `2√T`.

Legendre is Bertrand's window with the left edge pushed right, from `T/2` to `T − 2√T`; the right
end and the base are unchanged. For `T > 16`, `Legendre ⊂ Bertrand` — Legendre is the narrow right
sliver of Bertrand's window.

In Bertrand's own frame `(n, 2n]` (so `T = 2n`), Legendre reads

```
    ( 2n − 2√(2n) + 1 ,  2n ]        with width  2√(2n) − 1,
```

i.e. the left edge moves from `n` to `n + (n − 2√(2n) + 1)`. At a square top `2n = (N+1)²` this is
exactly `(N², (N+1)²]`. (Check: `n = 98`, top `196` → `(169, 196]`, the `N = 13` Legendre window.)

**What this is, and is not.** A *structural characterization*, not a new or easier problem: at
square tops it is exactly Legendre, so the reframed statement is equivalent (a short-interval
statement of the same `θ = 1/2` difficulty). What the reframing buys is a precisely named missing
step — **localization**. Bertrand guarantees a prime *somewhere* in `(T/2, T]`; Legendre needs it
in the right sliver `(T − 2√T, T]`, and the prime could sit in the left part Bertrand's proof does
not localize. That single localization is the whole gap, open for everyone: the best proven
short-interval exponent is `0.525` (Baker–Harman–Pintz), and Legendre's `1/2` sits just below.

The interval identities of this reframing are machine-checked (`Reframing.lean`:
`legendreWindow_narrowed`, and `legendreWindow_subset_doubling` — Legendre's window is contained in
the same-top doubling window). Only the localization is left open, as it must be.

## The general principle: one deterministic reach, two halves

Fix a complete base of primes `B(P) = { primes ≤ P }` — no prime skipped. By the sieve of
Eratosthenes it deterministically decides primality across its whole **deterministic reach**,
the range up to `nextprime(P)² ≈ P²`: every position in that range coprime to `B(P)` (a
*void*) is prime, and the first composite void is exactly `nextprime(P)²`. This reach is not a
single window — one fixed base governs a whole block of consecutive windows, and the base
grows only when the scale crosses a prime.

The mechanism then splits into two halves that behave completely differently:

- **Generative determinism (void ⟹ prime) — universal and free.** It holds across the *entire*
  generative reach (up to `nextprime(P)²`), for Bertrand's window, Legendre's window, and every
  window in between, with room to spare. It is settled by the least-prime-factor argument alone
  and never distinguishes the cases. (This is distinct from *base self-containment* — every
  composite built entirely from the base — which reaches only `2P` and is not what decides
  primality here.)
- **Existence (a void exists) — governed only by position and width.** Whether a window
  `(a, a+w]` inside the reach contains a void depends *solely* on its position `a` and width
  `w`, through the **participating rings**: the primes `p ≤ √(a+w)` and their arithmetic
  coverage of the window. By the least-prime-factor partition `coveredCount = Σ_p |fiber_p|`
  (each covered position counted once, under its least prime factor), the whole question is:
  **can the participating rings, at this position and width, cover the window with no gap?**

Bertrand and Legendre are the two ends of this single question inside one reach:

- **Bertrand — the upper, provable end.** Window `(P, 2P]` at the near edge; width equal to the
  anchor. Participating rings `p ≤ √(2P)` — about `√(2P)/ln` of them, *sparse* against the
  width `P`. Too few rings to cover: a void is forced, and this is provable (Chebyshev-strength).
- **Legendre — the far, open end.** Window `(P², (P+1)²]` at the far edge; width `~2√anchor`.
  Participating rings `p ≤ P` — about `P/ln P` of them, *dense* against the width `2P`. Their
  combined strength saturates at `1 − ∏_{p≤√T}(1−1/p) ≈ 1 − e^{-γ}/ln P` of the window
  (Mertens), leaving a positive void fraction `≈ e^{-γ}/ln P` *on average* — yet proving `≥ 1`
  void in *every* single narrow window is beyond current sieve methods.

This is the general principle. **Determinism is the ceiling Bertrand and Legendre share**;
everything below Bertrand — narrower or deeper windows, down to Legendre and beyond — sits
inside the same deterministic reach and is decided *purely* by the density of the participating
rings, i.e. by the window's position and width. Nothing else enters.

## The quantity we want to derive

Write the width as a power of the anchor, `W(A) ~ A^θ`. The exponent `θ` **is** the
speed-to-width ratio in the cleanest form: large `θ` = wide/slow, small `θ` = narrow/fast.
In ring terms it measures the density of participating rings against the width — Bertrand
`~1/√A` (sparse), Legendre `~1/ln A` (dense) — so `θ` is exactly the dial of the ring balance
above. The object we are after is the map

```
θ  ↦  { the window is forced to contain a prime }  ∈  { proven, conditional, open, false }
```

Current placement of that map (honest state of the art):

- **θ = 1** (constant fraction — Bertrand, and any `(n, cn]`): **proven**, elementarily,
  by a Chebyshev-strength certificate. This is exactly what `structural_bertrand` formalizes.
- **0.525 < θ < 1**: **proven** by prime-gap results (Baker–Harman–Pintz: primes in
  `(x, x + x^0.525]`).
- **θ = 1/2** (Legendre): **open**. Not implied even by the Riemann Hypothesis (RH gives gaps
  of size `~√x·log x`, which exceeds the Legendre width `2√x`).
- **θ → 0** (width below `~(log A)²`): **false** for some windows (prime gaps outrun the
  width — Cramér).

So the mechanism does not "prove Legendre". What it does is place Bertrand (solved), Legendre
(open) and the whole family on one axis, and make the dividing line between them a single,
explicit quantity — the exponent `θ`.

## The covered run in the coupled window

The forcing quantity is the longest run of consecutive **covered** positions *inside the window*.
If it is shorter than the width, a void — a prime, by determinism — is forced:

```
    (longest covered run in the window)  <  W   ⟹   the window contains a void.
```

A tempting bound is the **Jacobsthal function** `g(M)` of the ring product `M = ∏(p ≤ √T)`: by CRT
the rings can cover a run of length up to `g(M)` *somewhere*. But `g(M)` is the worst case
**anywhere**, and in the coupled setting the window is not anywhere — its position is pinned by the
ring count to `≈ p_k²` (just above the largest ring). The Jacobsthal worst case sits far beyond
that: for `M = 2·3·5·7·11·13` the maximal run `g = 22` is at `9440–9460`, while the coupled window
is at `≈ 169`. So `g(M)` badly **overestimates** what happens in the window — this is the correction
that the coupling forces.

Measured where it belongs — inside the window — the covered run stays small and the margin *grows*:

| window `(P², (P+1)²]` | width `2P+1` | longest covered run **in window** | voids | margin |
|----:|---:|---:|---:|---:|
| P = 13  | 27  | 9  | 5  | 3.0× |
| P = 42  | 85  | 15 | 10 | 5.7× |
| P = 97  | 195 | 35 | 22 | 5.6× |
| P = 200 | 401 | 53 | 33 | 7.6× |

The coupled window becomes *relatively looser*, not tighter: the in-window run grows like the local
prime gap (`~log²`), the width like `2√T`, so `width / run → ∞`. Bertrand and Legendre are alike in
this — both forced locally, with a widening margin. (There is no finite "crossover"; that was an
artefact of using the global `g(M)` in place of the in-window run.)

### The inequality to infinity

The real certificate is therefore analytic and **local** — a short-interval prime-gap bound:

```
    (largest prime gap near x)   <   width  =  x^θ          for all x,
```

with `x` the position and `θ` the width exponent (Bertrand `θ = 1`, Legendre `θ = 1/2`). The
provable frontier is that exponent: `θ = 1` by Chebyshev; `θ` down to `0.525` by Baker–Harman–Pintz
(a prime in `(x, x + x^{0.525}]`). Legendre asks for `θ = 1/2`, just below the proven `0.525`: the
actual gaps are far smaller (`~log² x`), so the void is present — but the *provable* gap bound
`x^{0.525}` exceeds the Legendre width `2√x = x^{0.5}` for large `x`. That single unproven step, from
`0.525` down to `0.5`, is the whole of Legendre; the mechanism isolates it as the one inequality
above.

## How we approach it

Reuse the structural layer from `structural_bertrand`, rewritten to be **anchor-agnostic**:

1. **Window and base from the anchor.** For a window with top `T = A + W`, the
   *active-covering base* is the set of primes `p` with `p² ≤ T` (a composite `≤ T` has a
   least prime factor `≤ √T`). The active base is taken at the **window top** `√(A+W)` — the
   Bertrand-specific `√(2·Pmax)` is just the special case `A = W = Pmax`.
2. **The atom (anchor-agnostic).** "The window contains a prime" reduces to "the window
   contains an integer coprime to the active base" — a *void* — i.e. "the base does not cover
   the whole window". This is the identical atom shape used for Bertrand, now stated over a
   general anchor.
3. **The ring balance at the atom.** Existence of a void is decided by the least-prime-factor
   partition `coveredCount = Σ_p |fiber_p|` over the participating rings `p ≤ √T` (transferred
   from `structural_bertrand`'s `coveredCount_eq_sum_minFac_fiber`, `coverFiber_eq_scaled`,
   `coveredCount_split_two`). For every concrete scale this is decidable (`native_decide`); the
   uniform `∀`-statement needs a bound on the ring coverage.
4. **A swappable certificate.** That bound is a module (as in `structural_bertrand`'s
   `WindowCertificate`) whose required strength moves with `θ`: Chebyshev-strength closes
   `θ = 1`; the frontier demands more as `θ` decreases; at `θ = 1/2` no certificate is known.

**Legendre as a by-product** means exactly this: the mechanism produces the Legendre statement
as the `θ = 1/2` instance of the general relation and localizes its difficulty precisely at
the atom's certificate — it exhibits *where* the hardness lives, without claiming to remove it.

## The general law — one target, everything a corollary

The formal target is not Legendre but a single **general law** (`GeneralLaw`): at every anchor
`A`, every window `(A, A+W]` whose width lies between the Legendre width `2⌊√A⌋+1` and the
Bertrand width `A` contains a new prime. From this one law the named statements are *extracted*
unconditionally:

* `bertrand_of_generalLaw` — Bertrand (width `W = A`);
* `legendreConjecture_of_generalLaw` — Legendre (anchor `n²`, width `2n+1`);
* `exists_prime_of_generalLaw` — a prime in *any* window in the range.

The unification the coupled table makes visible: at anchor `A`, the base `≤ √(2A)` has **one**
deterministic reach `≈ (A, 2A]`, and every width from `2√A` (Legendre, the bottom) up to `A`
(Bertrand, filling the reach) sits inside it — the same object at different widths, survivors =
new primes. The **Bertrand end is closed to infinity in-project** (`gapCertificate_bertrandLaw`,
via Mathlib's Bertrand): every `(A, 2A]` provably has a new prime.

The **general law itself is open**, because it contains its narrowest member, Legendre at
`W = 2√A`. Its closure to infinity is precisely the analytic frontier — the width exponent proven
down to `0.525` (Baker–Harman–Pintz), with Legendre's `1/2` the single gap below. The mechanism
does not remove that gap; it isolates it as the one inequality and proves everything around it.

## Honest scope

- This is a **mechanism-generalization + formalization** project, not a claimed resolution of
  Legendre.
- The deliverable is the anchor-agnostic reduction (window → active base → void atom →
  swappable certificate) and the explicit speed/width relation `θ`, with Bertrand as the
  closed endpoint and Legendre as the open one.
- Nothing here shortcuts an open problem. If the atom's certificate at `θ = 1/2` is ever
  supplied, Legendre follows through this mechanism; until then, the mechanism's value is the
  clean placement of the difficulty.

## Layout

```
structural_window/                       ← Lean 4 / Mathlib project (builds clean, no `sorry`)
├── README.md · LICENSE · .gitignore
├── lean-toolchain · lakefile.toml · lake-manifest.json
├── StructuralWindow.lean                ← aggregator + module map
└── StructuralWindow/
        ├── Basic.lean        — anchor-agnostic core (window, active base, void)
        ├── Reframing.lean    — Legendre = Bertrand narrowed from the left (interval identities)
        ├── Covering.lean     — covering / void duality
        ├── Counting.lean     — the atom: windowHasVoid ↔ coveredCount < W
        ├── Forcing.lean      — voids are coprimes to the ring product
        ├── CoveredRun.lean   — the local forcing quantity (in-window run; corrects global g)
        ├── Jacobsthal.lean   — the floor g(M) (computable); g(6,30,210,2310)
        ├── SmallAnchors.lean — anchors 3,5,7,11 forced (decidable core + periodic lift)
        ├── Determinism.lean  — generative determinism: void ⟹ prime
        ├── Unification.lean  — one anchor, base ≤ √(2A), any width: survivors = new primes
        ├── WidthLaw.lean     — the family by width law; Bertrand's law closed to infinity
        ├── GeneralLaw.lean   — the target GeneralLaw; Bertrand & Legendre as its corollaries
        ├── Legendre.lean     — LegendreVoid, prime-between-squares, the instances
        ├── Certificate.lean  — generalized WindowForcing; Bertrand & Legendre as evaluations
        └── Bridge.lean       — existential entry point: generalLaw_of_shortInterval (plug-in)
```

The development is a **generalization of the coupled-window mechanism**, not an attempt on
Legendre. The target is one general law; Bertrand, Legendre and every window in the deterministic
range are its corollaries. Everything through the structural forcing, the small anchors, the
unification and the Bertrand end (proven to infinity) is proved/decidable, `sorry`-free; the full
general law contains Legendre and is the isolated open frontier. Toolchain and Mathlib pin match
`structural_bertrand` (Lean 4, `v4.14.0`).

## License

This subproject is licensed under the **Apache License, Version 2.0** — see [`LICENSE`](LICENSE).
This overrides the repository-root license for this directory: the project depends on and imports
Mathlib (Apache-2.0), so its licensing must be Apache-2.0-compatible. All files are original to
this development and depend on Mathlib only as a library.