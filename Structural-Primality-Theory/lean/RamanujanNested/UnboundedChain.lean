import RamanujanNested.Bounds
import RamanujanNested.Monotone
import RamanujanNested.IdentityChain
import Mathlib

/-!
# UnboundedChain.lean — existence of a limit for the classical-type family

Section 5.1's actual gap (documented in `RamanujanNested.lean`) is that the
paper attributes convergence of `a_k = k`-type radicals to Section 4.1's
boundedness theorem, but that theorem needs a FIXED ceiling `A` with
`a_k ≤ A` for all `k`, which no unbounded sequence satisfies. This file closes
part of that gap for the specific linearly-growing family already central to
the paper (`a_k = N+k-2`, `IdentityChain.lean`'s Algorithm 3 coefficients,
the same shape as the classical `a_k = k` up to a shift): instead of a FIXED
ceiling, it uses a *moving* ceiling that grows in step with the coefficients
themselves.

## What's proven here

`rollUp_classicalCoeff_bounded`: for any target `N ≥ 1` and seed `T ∈ [0,N]`,
every truncation of the constant-seed-`T` radical with coefficients
`a_k = N+k-2` lies in `[0, N]` — not because the coefficients are bounded (
they aren't), but because at each recursive layer the bound `N` for the
outer family becomes exactly the bound `N+1` for the once-shifted family,
and `IdentityChain.lean`'s own identity `(N-1)(N+1)+1 = N²` makes the
induction close. Combined with `Monotone.lean` (which never needed an upper
bound on `a_k` in the first place), this gives `classicalRadical_converges`:
**the truncated radical genuinely has a finite limit `L ≤ N`** — a real
existence-of-limit result for an unbounded coefficient family, which
Section 4.1 as stated does not supply.

## What's still open: pinning down `L = N` exactly

The above gives `L ≤ N`, not `L = N`. A natural next attempt is to bound the
gap between the forward evaluation (seed `T=0`) and the "rolling" evaluation
(seed `T=N+d`, which by `IdentityChain.lean` hits `N` exactly at every finite
depth) using the same conjugate-multiplication contraction used in
`TargetRadical.lean`. Carried out here (on paper, not committed as a Lean
theorem because it does not actually work — recorded for honesty rather than
silently discarded):

Let `Δ_k` be the gap between the two seeds' values at layer `k`. The
per-layer contraction is `Δ_k ≤ (N+k-2)/(N+k-1) · Δ_{k+1}` (using only that
the rolling path equals `N+k-1` exactly and the forward path is `≥ 0`no
lower bound on the forward path is needed, unlike the failed uniform-ratio
attempt below). Telescoping from `k=1` to `k=d`:

`∏_{k=1}^{d} (N+k-2)/(N+k-1) = (N-1)/(N+d-1)`  (exact telescoping cancellation)

and the boundary gap is `Δ_{d+1} = (N+d) - 0 = N+d`. So

`Δ_1 ≤ (N+d) · (N-1)/(N+d-1) → N-1`  as `d → ∞`,

**not → 0.** The shrinking telescoped product and the growing boundary gap
almost exactly cancel, leaving a constant-order bound — this estimate is too
lossy to conclude `L = N`. (An earlier, cruder attempt — bounding each
`Δ_k`'s denominator uniformly using `V_k(T=0) ≥ c·k` — fails even worse:
numerically, `V_k` at seed `T=0` stays near `1` for `k` close to the
truncation depth `d` and only grows roughly linearly for `k` well inside the
depth, so no single constant `c` bounds `V_k/k` uniformly across `k`.) This
mirrors why Herschfeld's classical convergence criterion for infinite nested
radicals is a genuine theorem and not a two-line estimate — closing `L = N`
here needs a sharper argument than a direct tail-sensitivity bound, and is
left open rather than forced.
-/

namespace RamanujanNested

/-- The paper's own Algorithm-3 coefficient family, `a_k = N+k-2`, viewed as
a function of a real (not just natural) target `N` — the same shape as the
classical Ramanujan `a_k = k` up to the shift `N-2`, and hence just as
unbounded as `k → ∞`. -/
noncomputable def classicalCoeff (N : ℝ) (k : ℕ) : ℝ := N + (k : ℝ) - 2

/-- **Moving-ceiling boundedness.** Unlike `Bounds.lean`, no fixed `A` bounds
`classicalCoeff N`. Instead, the bound *moves*: at depth `d`, the truncation
is bounded by `N` itself, because peeling one layer trades `N` for `N+1` on
a family with one fewer layer — proven by induction on `d`, quantifying `N`
inside the induction (same pattern as `Bounds.lean`/`Monotone.lean`, for the
same reason: the inductive step needs the claim for the *shifted* family). -/
theorem rollUp_classicalCoeff_bounded :
    ∀ (d : ℕ) (N T : ℝ), 1 ≤ N → 0 ≤ T → T ≤ N →
      0 ≤ rollUp (classicalCoeff N) T d ∧ rollUp (classicalCoeff N) T d ≤ N := by
  intro d
  induction d with
  | zero =>
    intro N T _ hT0 hTN
    exact ⟨hT0, hTN⟩
  | succ n ih =>
    intro N T hN hT0 hTN
    have hN1 : 1 ≤ N + 1 := by linarith
    have hTN1 : T ≤ N + 1 := by linarith
    obtain ⟨_, hhi⟩ := ih (N + 1) T hN1 hT0 hTN1
    have hshift : (fun k => classicalCoeff N (k + 1)) = classicalCoeff (N + 1) := by
      funext k
      unfold classicalCoeff
      push_cast
      ring
    have ha1 : classicalCoeff N 1 = N - 1 := by
      unfold classicalCoeff
      push_cast
      ring
    have ha1_nonneg : 0 ≤ classicalCoeff N 1 := by rw [ha1]; linarith
    rw [rollUp_succ, hshift]
    have hradicand_le :
        1 + classicalCoeff N 1 * rollUp (classicalCoeff (N + 1)) T n ≤ N ^ 2 := by
      rw [ha1]
      have hmul : (N - 1) * rollUp (classicalCoeff (N + 1)) T n ≤ (N - 1) * (N + 1) :=
        mul_le_mul_of_nonneg_left hhi (by linarith)
      nlinarith [hmul]
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    calc Real.sqrt (1 + classicalCoeff N 1 * rollUp (classicalCoeff (N + 1)) T n)
        ≤ Real.sqrt (N ^ 2) := Real.sqrt_le_sqrt hradicand_le
      _ = N := Real.sqrt_sq (by linarith)

/-- Specialized to the canonical seed `T = 1` (matching `truncRadical`). -/
theorem classicalCoeff_bounded {N : ℝ} (hN : 1 ≤ N) (d : ℕ) :
    0 ≤ truncRadical (classicalCoeff N) d ∧ truncRadical (classicalCoeff N) d ≤ N :=
  rollUp_classicalCoeff_bounded d N 1 hN (by norm_num) hN

open Filter Topology

/-- **The existence-of-limit result.** For target `N ≥ 2` (matching
`IdentityChain.lean`'s own hypothesis), the classical-type radical
`truncRadical (classicalCoeff N)` — an UNBOUNDED coefficient family, outside
`Bounds.lean`'s reach — converges to a finite limit `L`, and `L ≤ N`. This is
new: Section 4.1 as stated does not cover this family at all. Whether
`L = N` exactly remains open (see the file docstring). -/
theorem classicalRadical_converges {N : ℝ} (hN : 2 ≤ N) :
    ∃ L : ℝ, Tendsto (truncRadical (classicalCoeff N)) atTop (𝓝 L) ∧ L ≤ N := by
  have hnonneg : ∀ k, 0 ≤ classicalCoeff N k := fun k => by
    unfold classicalCoeff
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hmono : Monotone (truncRadical (classicalCoeff N)) :=
    truncRadical_monotone (classicalCoeff N) hnonneg
  have hbdd : BddAbove (Set.range (truncRadical (classicalCoeff N))) := by
    refine ⟨N, ?_⟩
    rintro x ⟨d, rfl⟩
    exact (classicalCoeff_bounded (by linarith) d).2
  refine ⟨⨆ i, truncRadical (classicalCoeff N) i, tendsto_atTop_ciSup hmono hbdd, ?_⟩
  apply ciSup_le
  intro d
  exact (classicalCoeff_bounded (by linarith) d).2

end RamanujanNested
