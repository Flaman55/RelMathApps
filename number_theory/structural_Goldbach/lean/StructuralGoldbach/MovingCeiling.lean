import StructuralGoldbach.SmallWitness

/-!
# StructuralGoldbach — MovingCeiling (technika z `RamanujanNested/PrimeChain.lean`)

Korekta ramy (Artur, po pokazaniu `PrimeChain.lean` z projektu Ramanujan): `SmallWitness`
próbowało jednego GLOBALNEGO `(C, k)` dla wszystkich `n` naraz — to jest dokładnie ten sam
błąd co `Bounds.lean`'s STAŁY sufit `A` miał dla nieograniczonego ciągu współczynników.
`PrimeChain.lean` naprawił to, zamieniając stały sufit na sufit KROCZĄCY `A·rⁱ`, zależny od
głębokości rekursji `i`, i domykający się do stałej dopiero na szczycie (`i = 0`).

Ten plik robi to samo dla świadka Goldbacha, rozbijając `SmallWitness` na dwa niezależne,
osobno mierzalne kawałki — dokładnie tak jak `PrimeChain.lean` (Krok 1: wzrost bazowy przez
Bertrand; Krok 3–4: sufit kroczący zamykający rekurencję):

1. `WitnessStepBound` — sufit kroczący po NUMERZE KROKU KASKADY `k` (nie po `n` wprost):
   świadek w segmencie okna `k` jest ograniczony wielomianowo w `k`. Zmierzone (Python,
   `witness_scan.py`): stopień ~2, stała `D ≈ 3`, bez wyjątku do `k = 26` (baza ≈ 81 600 000).

2. `AnchorDoublingRate` — dolne ograniczenie tempa wzrostu kotwic: `anchor(k) ≥ c·2^k`.
   Bertrand daje tylko GÓRNE ograniczenie (`anchor(k+1) ≤ 2·anchor(k)`) — działa w ZŁĄ stronę
   dla przełożenia „krok k" → „log n". Potrzeba dolnego. Zmierzone: stosunek
   `anchor(k+1)/anchor(k)` zbiega DOKŁADNIE do `2.000` (nie do `1`) od k≈16 wzwyż — silny
   sygnał `anchor(k) ~ c·2^k`. To jest fakt o przerwach między pierwszymi (największa
   pierwsza w `(x, 2x]` jest asymptotycznie blisko `2x`, bo przerwy są `o(x)`) — konsekwencja
   Twierdzenia o Liczbach Pierwszych, NIE samego Bertranda. Dużo słabsze i bardziej
   standardowe narzędzie niż oryginalny problem gęstości Goldbacha — nie trzeba nawet
   wyników rzędu Baker–Harman–Pintz, wystarczy klasyczne `o(x)`.

**Kierunek przełożenia (ważne, bo łatwo pomylić):** z `top k < n` (dolne ograniczenie na `n`
z bycia w segmencie) i `AnchorDoublingRate` zastosowanego przy INDEKSIE `k` (nie `k+1`)
dostajemy `n > 2·anchor(k) ≥ 2c·2^k`, czyli `2^k < n/(2c)`, czyli **górne** ograniczenie na
`k` w terminach `log n`. To odwrotny kierunek niż górne ograniczenie Bertranda daje — dlatego
potrzeba osobnego, DOLNEGO ograniczenia wzrostu kotwic.

## Status

`WitnessStepBound` i `AnchorDoublingRate` są zmierzone obliczeniowo, NIE udowodnione — to są
dokładnie nazwane, zawężone treści zastępujące mgławicowe `SmallWitness`. Most
(`smallWitness_of_stepBound_and_doublingRate`) MA pełną próbę dowodu (nie `sorry`) — czysta
real-analiza: `exists_step_containing` (w `Constructive.lean`, dowiedzione bez `sorry` wprost
z definicji `nextAnchor` przez Bertranda) daje krok `k` zawierający `n`; potem `n > top k` i
`AnchorDoublingRate` przy indeksie `k` dają `2^(k+1) < n/c`, logarytm zamienia to na górne
ograniczenie `k+1 < C₃·log n`, i podniesienie do potęgi `d` domyka `SmallWitness`.

**Uczciwie o pewności:** to jedyny plik w projekcie pisany BEZ dostępu do kompilatora Lean w
tej sesji (brak `lake` w sandboksie Cowork) — w przeciwieństwie do `Constructive.lean` i
`SmallWitness.lean` (proste definicje, zbudowane czysto za pierwszym razem), to jest
wielokrokowa real-analiza (`Real.log`, `Real.rpow`, `Finset.max'`/`WithBot`) z realnym
ryzykiem drobnych niezgodności nazw lematów Mathlib. Uruchom `lake build` i wklej PEŁNY
błąd, jeśli coś nie przejdzie — poprawię precyzyjnie, nie na ślepo.
-/

namespace StructuralGoldbach

/-- **Krok 1 (sufit kroczący po numerze kroku kaskady).** Świadek w segmencie okna `k`
    ograniczony wielomianowo w `k` — zmierzone: stopień `d ≈ 2`, stała `D ≈ 3`, bez wyjątku
    do `k = 26`. Analogon `rollUp_geomBounded`'s moving ceiling `A·rⁱ`, tu z wielomianem
    zamiast wykładnika (bo to dyskretny problem istnienia, nie ciągła rekurencja analityczna). -/
def WitnessStepBound : Prop :=
  ∃ D d : ℝ, 0 < D ∧ 0 < d ∧ ∀ k n : ℕ, top k < n → n ≤ top (k + 1) → Even n →
    ∃ p q : ℕ, (p : ℝ) ≤ D * ((k : ℝ) + 1) ^ d ∧ p.Prime ∧ q.Prime ∧ p + q = n

/-- **Krok 2 (dolne tempo podwajania kotwic).** `anchor(k) ≥ c·2^k` — dolne ograniczenie,
    analogon `nth_prime_le_four_pow` ale w PRZECIWNYM kierunku (tu potrzeba dolnego, nie
    górnego). Zmierzone: stosunek kolejnych kotwic zbiega do dokładnie `2.000`. Fakt o
    przerwach między pierwszymi (konsekwencja PNT), NIE samego Bertranda. -/
def AnchorDoublingRate : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, c * 2 ^ k ≤ (anchor k : ℝ)

/-- **Most (do domknięcia).** Oba kroki razem zamieniają „sufit po głębokości kaskady" w
    „sufit po log wielkości liczby" — dokładnie ten sam manewr co w `PrimeChain.lean`,
    tylko tam wynik dotyczył zbieżności ciągu, tu istnienia świadka. Szkic: dla danego `n`
    znajdź krok `k` z `top k < n ≤ top (k+1)` (istnieje, bo `top` nieograniczone —
    z `AnchorDoublingRate`); z `top k < n` i `AnchorDoublingRate` przy indeksie `k` dostań
    `k < log₂(n) + O(1)`; podstaw do `WitnessStepBound`. -/
theorem smallWitness_of_stepBound_and_doublingRate
    (hstep : WitnessStepBound) (hdouble : AnchorDoublingRate) : SmallWitness := by
  obtain ⟨D, d, hD, hd, hw⟩ := hstep
  obtain ⟨c, hc, hlb⟩ := hdouble
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog6 : (0 : ℝ) < Real.log 6 := Real.log_pos (by norm_num)
  set K : ℝ := -Real.log c / Real.log 2 with hK
  set C3 : ℝ := 1 / Real.log 2 + max K 0 / Real.log 6 with hC3
  have hC3pos : 0 < C3 := by
    rw [hC3]
    have h1 : 0 < 1 / Real.log 2 := div_pos one_pos hlog2
    have h2 : 0 ≤ max K 0 / Real.log 6 := div_nonneg (le_max_right _ _) (le_of_lt hlog6)
    linarith
  set C : ℝ := max (D * C3 ^ d) (2 / (Real.log 4) ^ d) with hC
  have hlog4 : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  have hCpos : 0 < C := by
    have h1 : 0 < D * C3 ^ d := mul_pos hD (Real.rpow_pos_of_pos hC3pos d)
    exact lt_max_of_lt_left h1
  refine ⟨C, d, hCpos, hd, ?_⟩
  intro n hn4 hne
  rcases eq_or_lt_of_le hn4 with heq | hgt
  · -- n = 4 : świadek 2 + 2, pokryty przez drugi człon maksimum w C
    refine ⟨2, 2, ?_, Nat.prime_two, Nat.prime_two, by omega⟩
    have hCge : 2 / (Real.log 4) ^ d ≤ C := le_max_right _ _
    have h4 : (n : ℝ) = 4 := by exact_mod_cast heq.symm
    rw [h4]
    have hlog4d : 0 < (Real.log 4) ^ d := Real.rpow_pos_of_pos hlog4 d
    calc (2 : ℝ) = (2 / (Real.log 4) ^ d) * (Real.log 4) ^ d := by field_simp
      _ ≤ C * (Real.log 4) ^ d := by
          apply mul_le_mul_of_nonneg_right hCge (le_of_lt hlog4d)
  · -- n > 4 : krok kaskady + konwersja log
    obtain ⟨k, hlo, hhi⟩ := exists_step_containing hgt
    obtain ⟨p, q, hple, hp, hq, hpq⟩ := hw k n hlo hhi hne
    have hn6 : (6 : ℕ) ≤ n := by
      have hmod := Nat.even_iff.mp hne
      omega
    -- Krok A: n > 2·c·2^k, czyli 2^(k+1) < n / c
    have htopk : (top k : ℝ) < (n : ℝ) := by exact_mod_cast hlo
    have htopeq : (top k : ℝ) = 2 * (anchor k : ℝ) := by
      unfold top; push_cast; ring
    have hlbk := hlb k
    have hstep1 : c * 2 ^ (k + 1) < (n : ℝ) := by
      have : c * 2 ^ (k + 1) = 2 * (c * 2 ^ k) := by ring
      rw [this]
      calc 2 * (c * 2 ^ k) ≤ 2 * (anchor k : ℝ) := by linarith [hlbk]
        _ = (top k : ℝ) := htopeq.symm
        _ < (n : ℝ) := htopk
    have hcpow_pos : (0:ℝ) < c * 2 ^ (k+1) := by positivity
    have hn_pos : (0:ℝ) < (n:ℝ) := by
      have : (0:ℕ) < n := by omega
      exact_mod_cast this
    -- Krok B: przejście do logarytmów
    have hlogstep : Real.log (c * 2 ^ (k + 1)) < Real.log n :=
      Real.log_lt_log hcpow_pos hstep1
    have hlogexpand : Real.log (c * 2 ^ (k + 1)) = Real.log c + (k + 1) * Real.log 2 := by
      rw [Real.log_mul (ne_of_gt hc) (by positivity), Real.log_pow]
      push_cast; ring
    have hkbound : ((k : ℝ) + 1) * Real.log 2 < Real.log n - Real.log c := by
      rw [hlogexpand] at hlogstep; linarith
    have hkbound' : (k : ℝ) + 1 < Real.log n / Real.log 2 + K := by
      have heq : Real.log n / Real.log 2 + K = (Real.log n - Real.log c) / Real.log 2 := by
        rw [hK]; ring
      rw [heq, lt_div_iff₀ hlog2]
      linarith [hkbound]
    -- Krok C: log n / log 2 + K ≤ C3 * log n dla n ≥ 6
    have hlogn6 : Real.log 6 ≤ Real.log n := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hn6
    have hlognpos : 0 < Real.log n := lt_of_lt_of_le hlog6 hlogn6
    have hKterm : K ≤ (max K 0 / Real.log 6) * Real.log n := by
      rcases le_or_lt K 0 with hK0 | hK0
      · have h1 : (0:ℝ) ≤ (max K 0 / Real.log 6) * Real.log n := by positivity
        linarith
      · have hmaxK : max K 0 = K := max_eq_left (le_of_lt hK0)
        rw [hmaxK]
        rw [div_mul_eq_mul_div, le_div_iff₀ hlog6]
        nlinarith [hlogn6]
    have hC3bound : Real.log n / Real.log 2 + K ≤ C3 * Real.log n := by
      have hexpand : C3 * Real.log n
          = Real.log n / Real.log 2 + (max K 0 / Real.log 6) * Real.log n := by
        rw [hC3]; ring
      rw [hexpand]
      linarith [hKterm]
    have hkfinal : (k : ℝ) + 1 < C3 * Real.log n := lt_of_lt_of_le hkbound' hC3bound
    have hkfinal' : (k : ℝ) + 1 ≤ C3 * Real.log n := le_of_lt hkfinal
    -- Krok D: podnieś do potęgi d i wróć do świadka
    have hCln_nonneg : 0 ≤ C3 * Real.log n := by positivity
    have hpowbound : ((k : ℝ) + 1) ^ d ≤ (C3 * Real.log n) ^ d :=
      Real.rpow_le_rpow (by positivity) hkfinal' (le_of_lt hd)
    have hmulrpow : (C3 * Real.log n) ^ d = C3 ^ d * (Real.log n) ^ d :=
      Real.mul_rpow (le_of_lt hC3pos) (le_of_lt hlognpos)
    have hCbound : D * C3 ^ d ≤ C := le_max_left _ _
    refine ⟨p, q, ?_, hp, hq, hpq⟩
    calc (p : ℝ) ≤ D * ((k : ℝ) + 1) ^ d := hple
      _ ≤ D * (C3 * Real.log n) ^ d := by
          apply mul_le_mul_of_nonneg_left hpowbound (le_of_lt hD)
      _ = D * C3 ^ d * (Real.log n) ^ d := by rw [hmulrpow]; ring
      _ ≤ C * (Real.log n) ^ d := by
          apply mul_le_mul_of_nonneg_right hCbound
          positivity

end StructuralGoldbach
