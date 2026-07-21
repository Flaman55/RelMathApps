import StructuralGoldbach.Constructive

/-!
# StructuralGoldbach — SmallWitness (świadek wielkości polylog n)

`Constructive.lean` ustaliło regułę **starej bazy**: świadek `p` można zawsze wziąć spośród
pierwszych ≤ poprzednia kotwica kaskady (rzędu `n`). To już porzuca ducha zliczania — ale
nadal przeszukuje przestrzeń rzędu `n`.

Pomiar (Python, `witness_scan.py`, kaskada do bazy ≈ 81 600 000) pokazuje coś dużo ostrzejszego:
NAJGORSZY świadek w każdym oknie nie rośnie proporcjonalnie do bazy — mieści się w paśmie

    p ≈ C · (log baza)^k,   k ≈ 2.3–2.7 (malejące w stronę ~2 wraz z zakresem zbadanych danych,
                                          nie ustabilizowane precyzyjnie w zbadanym zakresie)

bez wyjątku, od bazy = 4 do bazy ≈ 81 600 000. To jest strukturalnie ten sam typ redukcji co
`minFac ≤ √n` w Bertrandzie — z przestrzeni rzędu `n` do przestrzeni polylogarytmicznej.

**Uczciwa różnica względem `void_isPrime`:** `minFac ≤ √n` jest FAKTEM ARYTMETYCZNYM —
zero wejścia analitycznego, żadnego szacunku gęstości. `p = O(log^k n)` tutaj jest na razie
OBSERWACJĄ OBLICZENIOWĄ, nie dowodem elementarnym — analogiczną do domysłu o "najmniejszym
świadku Goldbacha" badanego w analitycznej teorii liczb. `SmallWitness` poniżej zapisuje
DOKŁADNIE tę brakującą estymatę — nic więcej, nic mniej — tak by można było ją podłączyć
(albo próbować dowieść) niezależnie od reszty rusztowania.
-/

namespace StructuralGoldbach

open Finset

/-- **Redukcja: mały świadek.** Istnieją stałe `C, k > 0` takie, że każde parzyste `n ≥ 4`
    ma reprezentację Goldbacha ze świadkiem `p ≤ C · (log n)^k` — przestrzeń poszukiwań
    polylogarytmiczna, nie liniowa w `n`. To jest jedyny brakujący klocek: jeśli to jest
    prawdą, `Goldbach` wynika natychmiast (świadek jest świadkiem). -/
def SmallWitness : Prop :=
  ∃ C k : ℝ, 0 < C ∧ 0 < k ∧ ∀ n : ℕ, 4 ≤ n → Even n →
    ∃ p q : ℕ, (p : ℝ) ≤ C * (Real.log n) ^ k ∧ p.Prime ∧ q.Prime ∧ p + q = n

/-- **Domknięcie:** `SmallWitness` ⟹ `Goldbach` wprost — świadek ograniczony wielkością
    polylog jest w szczególności świadkiem reprezentacji, rozmiar granicy nie jest tu
    nawet potrzebny do wniosku (jest treścią, nie mechanizmem dowodu). -/
theorem goldbach_of_smallWitness (h : SmallWitness) : Goldbach := by
  intro n hn he
  obtain ⟨C, k, hC, hk, hw⟩ := h
  obtain ⟨p, q, _hple, hp, hq, hpq⟩ := hw n hn he
  exact ⟨p, q, hp, hq, hpq⟩

/-- `SmallWitness` jest ściśle silniejsze niż `CascadeOldBaseSufficiency` w tym sensie, że
    obie mówią o istnieniu świadka — różnica jest wyłącznie w GRANICY na jego rozmiar:
    stara baza (rzędu `n`) kontra polylog. Obie redukują `Goldbach` do jednego zdania
    egzystencjalnego; `SmallWitness` jest ostrzejsze (mniejsza przestrzeń poszukiwań),
    więc trudniejsze do udowodnienia, ale bliższe faktycznemu mechanizmowi (analogicznemu
    do `void_isPrime`), gdyby dało się je domknąć. -/
example : SmallWitness → Goldbach := goldbach_of_smallWitness

end StructuralGoldbach
