import StructuralGoldbach.Constructive

/-!
# StructuralGoldbach — SelfContainment (konieczność, nie istnienie)

Addytywny odpowiednik multiplikatywnej samozwartości bazy. Tam: `𝒫 = {2,…,Pmax}` buduje
KAŻDĄ liczbę złożoną `≤ 2·Pmax` wyłącznie z siebie, bo dowolny czynnik `q > Pmax` wymusza
`n = q·m ≥ 2q > 2·Pmax` (`m ≥ 2`, bo `n` złożone) — to jest zdanie o ISTNIENIU
(jednoznaczna faktoryzacja zawsze istnieje), więc dowodzi pełnego pokrycia za darmo.

Dodawanie nie ma odpowiednika jednoznacznej faktoryzacji: istnienie rozkładu `p+q=n` NIE
jest gwarantowane bezwarunkowo (to jest samo sedno hipotezy Goldbacha — patrz `Structural.lean`'s
`windowCovered`, sprawdzane `native_decide`-em, nie dowodzone wprost). Jest natomiast dokładny
odpowiednik strony KONIECZNOŚCI, tym samym mechanizmem co w mnożeniu (najmniejszy możliwy
"dopełniacz" wymusza zasięg): jeżeli rozkład `p+q=n` istnieje i `n` jest dostatecznie małe
względem `B`, to ten KONKRETNY rozkład musi mieścić się w bazie `≤ B` po obu stronach — bo
`p, q ≥ 2` (najmniejsza liczba pierwsza), więc `n = p+q ≥ p+2`, skąd `p ≤ n-2 ≤ B` gdy
`n ≤ B+2` (symetrycznie dla `q`).

To DOPEŁNIA, nie zastępuje, `windowCovered`: `windowCovered` to zdanie o istnieniu na całym
`[4, 2·Pmax]` (empirycznie pokryte w ~87–99% ponad `B+2`, sprawdzone dla kilku `Pmax` w
analizie towarzyszącej), podczas gdy ten plik dowodzi bezwarunkowo — bez żadnego
`native_decide` — dużo węższego, ale zupełnie pewnego faktu o wymuszeniu.
-/

namespace StructuralGoldbach

/-- **Obie strony rozkładu w bazie `≤ B`.** Addytywny odpowiednik "wszystkie czynniki są
    `≤ B`" z multiplikatywnej samozwartości. W przeciwieństwie do `buildableFromBase`
    (`Constructive.lean`, które ogranicza tylko mniejszy składnik `p`), tutaj ograniczamy
    OBA składniki — to jest właściwy odpowiednik pełnej faktoryzacji w bazie. -/
def additiveSelfContained (B n : ℕ) : Prop :=
  ∃ p q : ℕ, p ≤ B ∧ q ≤ B ∧ p.Prime ∧ q.Prime ∧ p + q = n

/-- **Główne twierdzenie: konieczność, nie istnienie.** Jeśli rozkład Goldbacha liczby `n`
    istnieje i `n ≤ B + 2`, to jest on wymuszony do bazy `≤ B` po obu stronach. Dowód
    lustrzany do multiplikatywnego (`n = q·m`, `m ≥ 2` ⟹ `n ≥ 2q`), tylko na dodawaniu:
    `p, q ≥ 2` (Mathlib: `Nat.Prime.two_le`) i `p+q=n≤B+2` dają `p≤B` oraz `q≤B` wprost
    z arytmetyki. Bezwarunkowe, zero `native_decide`. -/
theorem additiveSelfContained_of_hasGoldbachRep {B n : ℕ} (hn : n ≤ B + 2)
    (h : hasGoldbachRep n) : additiveSelfContained B n := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h
  have hp2 : 2 ≤ p := hp.two_le
  have hq2 : 2 ≤ q := hq.two_le
  exact ⟨p, q, by omega, by omega, hp, hq, hpq⟩

/-- Świadek `additiveSelfContained` jest w szczególności świadkiem `buildableFromBase`
    (odrzucamy więzy na `q`) — łączy ten plik z konstruowalnością kaskady już opisaną
    w `Constructive.lean`. -/
theorem buildableFromBase_of_additiveSelfContained {B n : ℕ} (h : additiveSelfContained B n) :
    buildableFromBase B n := by
  obtain ⟨p, q, hp, _, hpp, hqp, hpq⟩ := h
  exact ⟨p, q, hp, hpp, hqp, hpq⟩

/-! ## Ostrość granicy `B + 2`

Poniższy przykład pokazuje, że `B + 2` nie da się bezwarunkowo wydłużyć: dla `B = 3`
(baza `{2, 3}`, maksymalna osiągalna suma z obu stron `≤ 3` to `3+3=6`), liczba `n = 8`
ma reprezentację Goldbacha (`3 + 5`), ale ŻADNA jej reprezentacja nie mieści się w bazie
`≤ 3` po obu stronach — a `8 > B + 2 = 5`, dokładnie tam, gdzie gwarancja się kończy.
Obie części poniżej domykają się bez `native_decide` (czysta arytmetyka/`norm_num`). -/

example : hasGoldbachRep 8 := ⟨3, 5, by norm_num, by norm_num, by norm_num⟩

example : ¬ additiveSelfContained 3 8 := by
  rintro ⟨p, q, hp, hq, _, _, hpq⟩
  omega

end StructuralGoldbach
