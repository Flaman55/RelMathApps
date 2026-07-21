import StructuralGoldbach.Structural

/-!
# StructuralGoldbach — Determinism (samozawieranie generatywne)

Addytywny odpowiednik `op_modulo = 0` z Bertranda. Okno kotwicy `(Pmax, 2·Pmax]` samo
DOSTARCZA nowych pierwszych: liczba w tym oknie względnie pierwsza z bazą (pierwsze `≤ Pmax`)
jest **na pewno pierwsza**, bo `2·Pmax < Pmax²` (parabola zasięgu). To gwarantuje, że kaskada
karmi się prawdziwymi pierwszymi, a nie pseudo-voidami.

Kluczowa lokalność (rama Artura): pytanie o parzystą `n = p+q` redukuje się z pełnej
kombinatoryki wszystkich par do **bieżącego okna i zasięgu bieżącej bazy** — w oknie znajdujesz
nowe pierwsze (sito) i nowe parzyste (suma).
-/

namespace StructuralGoldbach

/-- **Void okna = pierwsza.** Jeśli `Pmax < n ≤ 2·Pmax` i `n` nie ma czynnika pierwszego
    `≤ Pmax` (jest voidem bazy `≤ Pmax`), to `n` jest pierwsza. Zasięg: `2·Pmax < Pmax²`. -/
theorem void_isPrime {Pmax n : ℕ} (hP : 2 ≤ Pmax) (hn : Pmax < n) (hhi : n ≤ 2 * Pmax)
    (hbase : ∀ p : ℕ, p.Prime → p ∣ n → Pmax < p) : n.Prime := by
  have hn1 : n ≠ 1 := by omega
  have hmfp : (n.minFac).Prime := Nat.minFac_prime hn1
  have hmfd : n.minFac ∣ n := Nat.minFac_dvd n
  have hmfgt : Pmax < n.minFac := hbase _ hmfp hmfd
  obtain ⟨d, hd⟩ := hmfd                      -- hd : n = n.minFac * d
  have hd1 : d ≤ 1 := by
    by_contra h
    have h2 : 2 ≤ d := by omega
    have hmul : (Pmax + 1) * 2 ≤ n.minFac * d := Nat.mul_le_mul (by omega) h2
    rw [← hd] at hmul
    omega
  have hd_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.mul_zero] at hd; omega
    · exact h
  have hd_eq : d = 1 := by omega
  subst hd_eq
  rw [Nat.mul_one] at hd
  rw [hd]
  exact hmfp

end StructuralGoldbach
