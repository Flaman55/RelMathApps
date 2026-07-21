import StructuralGoldbach.Bridge

/-!
# StructuralGoldbach — Structural (okno deterministyczne)

Właściwe zdanie sita strukturalnego, w analogii do rozwoju multiplikatywnego:

* Kotwica `Pmax`. Okno deterministyczne `(Pmax, 2·Pmax]` dostarcza nowych pierwszych.
* Pokrycie sum żyje na przedziale parzystych `[2·Pmin, 2·Pmax] = [4, 2·Pmax]` (bo `Pmin = 2`).
* `windowCovered Pmax` : każda parzysta w `[4, 2·Pmax]` jest sumą dwóch pierwszych.

`Goldbach` to dokładnie „każde okno kotwicy jest pokryte" — kaskada do nieskończoności
`Pmax → 2·Pmax → 4·Pmax → …`.
-/

namespace StructuralGoldbach

open Finset

/-- Okno deterministyczne kotwicy `Pmax`: każda parzysta `n ∈ [2·Pmin, 2·Pmax] = [4, 2·Pmax]`
    jest sumą dwóch pierwszych (`Pmin = 2`, więc `2·Pmin = 4`). -/
def windowCovered (Pmax : ℕ) : Prop :=
  ∀ n, 4 ≤ n → n ≤ 2 * Pmax → Even n → hasGoldbachRep n

/-- Rozstrzygalna forma skończona: brak addytywnego voidu w oknie `[4, 2·Pmax]`. -/
abbrev windowCoveredDec (Pmax : ℕ) : Prop :=
  ∀ n < 2 * Pmax + 1, ¬ (4 ≤ n ∧ n % 2 = 0 ∧ repCount n = 0)

/-- Żywa weryfikacja jednego konkretnego okna (rozszerz `Pmax` przez `native_decide`). -/
example : windowCoveredDec 100 := by native_decide

/-- **Teoria, zapisana:** Goldbach ⟺ każde okno deterministyczne kotwicy jest pokryte.
    Kaskada `Pmax → 2·Pmax → …` przemiata wszystkie parzyste; odwrotnie każda parzysta `n`
    leży w oknie kotwicy `Pmax = n`. -/
theorem goldbach_iff_all_windows : Goldbach ↔ ∀ Pmax, windowCovered Pmax := by
  constructor
  · intro h Pmax n hn _ he
    exact h n hn he
  · intro h n hn he
    exact h n n hn (by omega) he

end StructuralGoldbach
