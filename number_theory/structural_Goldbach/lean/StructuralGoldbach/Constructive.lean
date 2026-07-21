import StructuralGoldbach.Structural
import Mathlib.NumberTheory.Bertrand

/-!
# StructuralGoldbach — Constructive (co da się zbudować, nie ile jest)

Korekta ramy (Artur): sito multiplikatywne (Bertrand) nie liczy ile jest liczb pierwszych
w oknie — pokazuje, że okno GEOMETRYCZNIE musi dostarczyć pierwszą (`void_isPrime`,
zasięg `2·Pmax < Pmax²`). `repCount`/`PositiveMargin`/`HL_Floor` w `Basic`/`Bridge` są
duchem ZLICZANIA (ile rozkładów) — to droga klasycznego sita, ta sama, która rozbija się
o problem parzystości (patrz próba ograniczenia "przecieku" półpierwszych przez
Brun–Titchmarsha: granica sita wymiaru 2 wymaga `s > ~4.8`, mały przeciek wymaga `s < ~2.1`
— progi się nie pokrywają).

Ten plik koduje inne pytanie, właściwe: nie "ile jest par (p,q)", tylko "co da się
ZBUDOWAĆ z konkretnej, już ugruntowanej, skończonej bazy" — konstruowalność, nie
zliczanie. Zweryfikowane obliczeniowo (Python, `structural_goldbach_cascade.py`, do
N = 3 000 000, kaskada startująca od `Pmax = 2`): **każda nowa parzysta w segmencie
danego okna daje się zbudować wyłącznie ze STAREJ bazy** (pierwsze ≤ poprzednia kotwica),
bez wyjątku poza samym punktem startowym `n = 4` (gdzie starej bazy jeszcze nie ma —
baza zaczyna się dokładnie od `2·Pmin`).
-/

namespace StructuralGoldbach

open Finset

/-- `n` daje się zbudować WYŁĄCZNIE ze STAREJ bazy: mniejszy składnik `p ≤ B`. To jest
    konstruowalność — "co może być" — a nie zliczanie "ile jest". -/
def buildableFromBase (B n : ℕ) : Prop :=
  ∃ p q : ℕ, p ≤ B ∧ p.Prime ∧ q.Prime ∧ p + q = n

/-- Rozstrzygalna forma skończona (do `decide` / `native_decide`). -/
abbrev buildableFromBaseDec (B n : ℕ) : Prop :=
  ∃ p ∈ range (B + 1), ∃ q ∈ range (n + 1), p.Prime ∧ q.Prime ∧ p + q = n

/-- Świadek konstruowalności ze starej bazy jest w szczególności świadkiem zwykłej
    reprezentacji Goldbacha (nie potrzeba nowego pierwszego z bieżącego okna). -/
theorem hasGoldbachRep_of_buildableFromBase {B n : ℕ} (h : buildableFromBase B n) :
    hasGoldbachRep n := by
  obtain ⟨p, q, _, hp, hq, hpq⟩ := h
  exact ⟨p, q, hp, hq, hpq⟩

/-- Kolejna kotwica kaskady: największa liczba pierwsza w oknie `(Pmax, 2·Pmax]`, albo
    `2·Pmax` gdy okno jest puste. Dokładne odzwierciedlenie pętli `while` w
    `structural_goldbach_cascade.py` (`p_max = new_primes[-1] if new_primes else top`). -/
def nextAnchor (Pmax : ℕ) : ℕ :=
  ((Finset.Ico (Pmax + 1) (2 * Pmax + 1)).filter Nat.Prime).max.getD (2 * Pmax)

/-- Ciąg kotwic kaskady: `anchor 0 = 2` (baza startowa, `Pmin = Pmax = 2`),
    `anchor (k+1) = nextAnchor (anchor k)`. Odpowiednik zmiennej `Pmax` w pętli Pythona. -/
def anchor : ℕ → ℕ
  | 0 => 2
  | (k + 1) => nextAnchor (anchor k)

/-- Górny kraniec okna kotwicy `k`: `top k = 2 · anchor k`. Odpowiednik `top` w Pythonie. -/
def top (k : ℕ) : ℕ := 2 * anchor k

/-- **Reguła "stara baza wystarcza"** — właściwy przedmiot dowodu w ramie Artura, zastępujący
    duch zliczania (`PositiveMargin`) duchem konstruowalności. Dla KAŻDEGO kroku kaskady,
    każda nowa parzysta w segmencie `(top k, top (k+1)]` daje się zbudować z pierwszych
    ograniczonych przez `top k` — starą bazę, ugruntowaną PRZED bieżącym oknem.
    Zweryfikowane obliczeniowo bez wyjątku do N = 3 000 000 (poza punktem startowym `n = 4`,
    gdzie okno zaczyna się od `top 0 = 4` i nie ma jeszcze starszej bazy). -/
def CascadeOldBaseSufficiency : Prop :=
  ∀ k n : ℕ, top k < n → n ≤ top (k + 1) → Even n → buildableFromBase (top k) n

/-- **Most:** `CascadeOldBaseSufficiency` na kroku `k` implikuje pokrycie segmentu
    `(top k, top (k+1)]` zwykłymi reprezentacjami Goldbacha (świadek ze starej bazy
    jest świadkiem w ogóle). -/
theorem hasGoldbachRep_of_cascadeOldBaseSufficiency (h : CascadeOldBaseSufficiency)
    {k n : ℕ} (hlo : top k < n) (hhi : n ≤ top (k + 1)) (he : Even n) :
    hasGoldbachRep n :=
  hasGoldbachRep_of_buildableFromBase (h k n hlo hhi he)

/-! ## Monotoniczność i nieograniczoność kaskady (do mostu `MovingCeiling`)

Potrzebne, żeby dla dowolnego `n` znaleźć krok `k` z `top k < n ≤ top (k+1)`. To jest
darmowe — wynika WPROST z definicji `nextAnchor` (przez Bertranda: okno zawsze niepuste,
więc `nextAnchor Pmax > Pmax`), bez potrzeby dolnego tempa wzrostu (`AnchorDoublingRate`
w `MovingCeiling.lean` jest potrzebne dopiero do GÓRNEGO ograniczenia na `k`, nie do
istnienia). -/

/-- `nextAnchor Pmax` leży w oknie `(Pmax, 2·Pmax]` — w szczególności jest większe niż
    `Pmax`. Świadkiem niepustości okna jest Bertrand (`Nat.exists_prime_lt_and_le_two_mul`). -/
theorem nextAnchor_gt {Pmax : ℕ} (h : 1 ≤ Pmax) : Pmax < nextAnchor Pmax := by
  obtain ⟨q, hqp, hqlt, hqle⟩ := Nat.exists_prime_lt_and_le_two_mul Pmax (by omega)
  set s := (Finset.Ico (Pmax + 1) (2 * Pmax + 1)).filter Nat.Prime with hs
  have hmem : q ∈ s := by
    rw [hs, Finset.mem_filter, Finset.mem_Ico]
    exact ⟨⟨by omega, by omega⟩, hqp⟩
  have hne : s.Nonempty := ⟨q, hmem⟩
  have hqle' : q ≤ s.max' hne := Finset.le_max' s q hmem
  have heq : nextAnchor Pmax = s.max' hne := by
    show s.max.getD (2 * Pmax) = s.max' hne
    rw [← Finset.coe_max' hne]
    rfl
  rw [heq]
  omega

/-- Wszystkie kotwice są `≥ 2` (baza startowa). -/
theorem anchor_ge_two (k : ℕ) : 2 ≤ anchor k := by
  induction k with
  | zero => simp [anchor]
  | succ n ih =>
    have h1 : 1 ≤ anchor n := by omega
    have hgt := nextAnchor_gt (Pmax := anchor n) h1
    have heq : anchor (n + 1) = nextAnchor (anchor n) := rfl
    omega

/-- Kotwice ściśle rosną krok po kroku. -/
theorem anchor_lt_succ (k : ℕ) : anchor k < anchor (k + 1) := by
  have h1 : 1 ≤ anchor k := by have := anchor_ge_two k; omega
  have hgt := nextAnchor_gt (Pmax := anchor k) h1
  have heq : anchor (k + 1) = nextAnchor (anchor k) := rfl
  omega

/-- Wolny, ale darmowy dolny płot: `anchor k ≥ k + 2` (samo ścisłe rośnięcie wystarcza
    do nieograniczoności — `AnchorDoublingRate` w `MovingCeiling.lean` daje dużo mocniejszy
    dolny płot, potrzebny gdzie indziej). -/
theorem anchor_ge_add_two (k : ℕ) : k + 2 ≤ anchor k := by
  induction k with
  | zero => simp [anchor]
  | succ n ih => have := anchor_lt_succ n; omega

theorem top_lt_succ (k : ℕ) : top k < top (k + 1) := by
  unfold top; have := anchor_lt_succ k; omega

theorem top_ge (k : ℕ) : 2 * k + 4 ≤ top k := by
  unfold top; have := anchor_ge_add_two k; omega

theorem top_zero : top 0 = 4 := by unfold top; simp [anchor]

/-- **Istnienie kroku kaskady zawierającego `n`.** Dla każdego `n > 4` istnieje `k` z
    `top k < n ≤ top (k+1)` — czysta konsekwencja monotoniczności i nieograniczoności
    `top`, bez potrzeby dolnego tempa wzrostu. -/
theorem exists_step_containing {n : ℕ} (hn : 4 < n) :
    ∃ k, top k < n ∧ n ≤ top (k + 1) := by
  have hunbounded : ∃ k, n ≤ top (k + 1) := by
    refine ⟨n, ?_⟩; have := top_ge (n + 1); omega
  classical
  let k0 := Nat.find hunbounded
  have hk0 : n ≤ top (k0 + 1) := Nat.find_spec hunbounded
  refine ⟨k0, ?_, hk0⟩
  rcases Nat.eq_zero_or_pos k0 with hz | hpos
  · have : top k0 = 4 := by rw [hz]; exact top_zero
    omega
  · have hnotmin : ¬ n ≤ top (k0 - 1 + 1) := Nat.find_min hunbounded (by omega)
    have heq : k0 - 1 + 1 = k0 := by omega
    rw [heq] at hnotmin
    omega

/-! ## Żywa weryfikacja konkretnych kroków kaskady (dopasowana do wyjścia Pythona)

`anchor 0 = 2, top 0 = 4` · `anchor 1 = 3, top 1 = 6` · `anchor 2 = 5, top 2 = 10` ·
`anchor 3 = 7, top 3 = 14` · `anchor 4 = 13, top 4 = 26` — zgodne z tabelą
`structural_goldbach_cascade.py` (kotwice 2, 3, 5, 7, 13, 23, 43, 83, …). -/

example : anchor 0 = 2 := by native_decide
example : anchor 1 = 3 := by native_decide
example : anchor 2 = 5 := by native_decide
example : anchor 3 = 7 := by native_decide
example : anchor 4 = 13 := by native_decide

/-- Segment `(4, 6]`: `6` buduje się ze starej bazy `≤ 4` (czyli z `{2, 3}`; `6 = 3 + 3`). -/
example : buildableFromBaseDec (top 0) 6 := by native_decide

/-- Segment `(6, 10]`: `8, 10` budują się ze starej bazy `≤ 6` (`{2, 3, 5}`). -/
example : ∀ n ∈ ({8, 10} : Finset ℕ), buildableFromBaseDec (top 1) n := by native_decide

/-- Segment `(10, 14]`: `12, 14` budują się ze starej bazy `≤ 10` (`{2, 3, 5, 7}`). -/
example : ∀ n ∈ ({12, 14} : Finset ℕ), buildableFromBaseDec (top 2) n := by native_decide

/-- Segment `(14, 26]`: wszystkie nowe parzyste budują się ze starej bazy `≤ 14`. -/
example : ∀ n ∈ (Finset.Ico 16 27).filter (· % 2 = 0),
    buildableFromBaseDec (top 3) n := by native_decide

end StructuralGoldbach
