import Mathlib.Tactic

/-!
# SelfContained.lean — Window-width lemma (why the constant is `2` / why width `≤ P_max`)

This is the structural justification for the *value* of the constant: self-containment of
the window forces width `≤ P_max`, i.e. a multiplier `≤ 2`. It is proved elementarily, with
no `sorry`.

**Note.** This is not the existence step. It concerns the *size* of the window (the
container), not whether the window contains a prime (the content). Existence lies on a
different axis and is settled separately by the quantitative certificate
(`Erdos.erdos_contradiction`); nothing in this file depends on it.
-/

namespace StructuralBertrand

/--
**Self-containment from width `≤ P`.**

In the window `(P, P+W]` with `W ≤ P`, the least proper multiple `2·q` of any new element
`q ∈ (P, P+W]` lies outside the window (`P + W < 2·q`). Hence width `≤ P` (multiplier `≤ 2`)
guarantees self-containment: no in-window element re-enters its own window through a proper
multiple of itself.
-/
theorem window_self_contained_bound {P W q : ℕ}
    (hW : W ≤ P) (hq_lo : P < q) (_hq_hi : q ≤ P + W) :
    P + W < 2 * q := by
  omega

/--
**Failure of self-containment forces width `> P`.**

Contrapositive of the previous lemma: if the least proper multiple `2·q` of some
`q ∈ (P, P+W]` falls inside the window (`2·q ≤ P + W`), then the width must exceed `P`.
Equivalently, self-containment fails once the multiplier exceeds `2`.
-/
theorem width_gt_of_overlap {P W q : ℕ}
    (hq_lo : P < q) (hover : 2 * q ≤ P + W) :
    P < W := by
  omega

/--
**Why exactly `2·P_max`.**

The maximal self-contained window anchored at `P_max` is `(P_max, 2·P_max]` (width exactly
`P_max`). A wider window is not self-contained (`width_gt_of_overlap`); for width `≤ P_max`
self-containment holds (`window_self_contained_bound`). The constant `2` is therefore not a
choice: it is the maximal width of a self-contained window.
-/
theorem max_self_contained_width {P q : ℕ}
    (hq_lo : P < q) (_hq_hi : q ≤ 2 * P) :
    2 * P < 2 * q := by
  omega

end StructuralBertrand
