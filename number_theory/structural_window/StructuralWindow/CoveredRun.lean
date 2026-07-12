import StructuralWindow.Forcing

/-!
# StructuralWindow.CoveredRun — the local forcing quantity

The quantity that governs the coupled window is the longest run of consecutive **covered**
positions *inside the window*, not the global Jacobsthal `g(M)` (whose worst-case run sits far
outside the coupled window — for `M = 2·3·5·7·11·13` at `9440`, while the window is at `≈ 169`).

Measured in the window, the run stays small while the width grows, so `run < W` with a widening
margin: the coupled window loosens, not tightens. Bertrand `(P, 2P]` and Legendre
`(P², (P+1)²]` obey the *same* inequality `run < width` — Legendre is its `θ = 1/2` evaluation.
-/

namespace StructuralWindow

/-- Longest run of consecutive covered positions inside `(A, A+W]`. `run < W` ⟺ a void exists. -/
def coveredRun (A W : ℕ) : ℕ :=
  let M := activeBaseProd (A + W)
  (List.range W).foldl
    (fun (st : ℕ × ℕ) (i : ℕ) =>
      if Nat.gcd M (A + 1 + i) == 1 then (0, st.2)
      else (st.1 + 1, max st.2 (st.1 + 1)))
    (0, 0) |>.2

-- The in-window run (corrected data): small, and growing far slower than the width.
example : coveredRun (13 ^ 2) (2 * 13 + 1) = 9 := by native_decide
example : coveredRun (42 ^ 2) (2 * 42 + 1) = 15 := by native_decide
example : coveredRun (97 ^ 2) (2 * 97 + 1) = 35 := by native_decide

-- Both ends of the mechanism obey the same inequality `run < width`.
example : coveredRun 97 97 < 97 := by native_decide                        -- Bertrand, θ = 1
example : coveredRun (97 ^ 2) (2 * 97 + 1) < 2 * 97 + 1 := by native_decide  -- Legendre, θ = 1/2

end StructuralWindow
