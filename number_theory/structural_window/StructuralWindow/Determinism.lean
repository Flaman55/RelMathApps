import StructuralWindow.Basic

/-!
# StructuralWindow.Determinism — generative determinism: void ⟹ prime

Inside the window a void is prime. If `n ∈ (A, A+W]` is not divisible by any active-covering
prime (`p² ≤ A+W`), then it has no prime factor `≤ √(A+W) ≥ √n`, so a composite would expose one
— hence `n` is prime. This is the least-prime-factor argument; it is what makes `windowHasVoid`
mean "a prime is present".
-/

namespace StructuralWindow

/-- A void in the window is prime (the generative determinism `void ⟹ prime`). -/
theorem prime_of_isVoid {A W n : ℕ} (hn : n ∈ coupledWindow A W) (h1 : 1 < n)
    (hv : isVoid A W n) : n.Prime := by
  rw [coupledWindow, Finset.mem_Ioc] at hn
  by_contra hnp
  have hpp : (n.minFac).Prime := Nat.minFac_prime (by omega)
  have hpd : n.minFac ∣ n := Nat.minFac_dvd n
  obtain ⟨k, hk⟩ := hpd
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, Nat.mul_zero] at hk; omega
    · exact h
  have hk1 : k ≠ 1 := by
    intro h; rw [h, Nat.mul_one] at hk; rw [← hk] at hpp; exact hnp hpp
  have hpk : n.minFac ≤ k := by
    have hkn : k ∣ n := hk.symm ▸ dvd_mul_left k n.minFac
    have hkm : k.minFac ∣ n := dvd_trans (Nat.minFac_dvd k) hkn
    have h1' : n.minFac ≤ k.minFac := Nat.minFac_le_of_dvd (Nat.minFac_prime hk1).two_le hkm
    have h2' : k.minFac ≤ k := Nat.minFac_le hkpos
    omega
  have hsq : n.minFac ^ 2 ≤ n := by
    have h := mul_le_mul_left' hpk n.minFac
    rw [← hk] at h
    rw [pow_two]; exact h
  have hpn : n.minFac ≤ n := Nat.le_of_dvd (by omega) (Nat.minFac_dvd n)
  have hmem : n.minFac ∈ activeBase (A + W) := by
    unfold activeBase
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpp, by omega⟩
  exact hv n.minFac hmem (Nat.minFac_dvd n)

end StructuralWindow
