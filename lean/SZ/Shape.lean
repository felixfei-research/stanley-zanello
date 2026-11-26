import SZ.Statement

namespace SZ
open Polynomial

def delta (P : ℤ[X]) (z : ℤ) : ℤ := atZ P z - atZ P (z-1)

theorem delta_shift_sub (k ell t s : ℕ) (z : ℤ) :
    delta (difference k ell t s) z =
      delta (gaussian k ell) z - delta (gaussian (k-2) t) (z-s) := by
  simp only [delta, difference, atZ_sub, atZ_shift]
  rw [show z-1-s=z-s-1 by ring]
  ring

theorem diff_symm_nat {k ell t s : ℕ} (ha : Aligned k ell t s) {i : ℕ} (hi : i ≤ k*ell) :
    (difference k ell t s).coeff i = (difference k ell t s).coeff (k*ell-i) := by
  simpa only [← Nat.cast_mul, ← Nat.cast_sub hi, atZ_nat] using difference_reflect ha (i:ℤ)

theorem exception_not_unimodal {k ell t : ℕ} (hk : 5 ≤ k) (ha : Aligned k ell t 1) :
    ¬ Unimodal (k*ell) (difference k ell t 1) := by
  have he : 0 < ell := by
    by_contra! h
    have : ell = 0 := by omega
    simp [Aligned, this] at ha
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
  let P := difference (a+1) (b+1) t 1
  have h0 : P.coeff 0 = 1 := by simp [P, difference, gaussian_const]
  have h1 : P.coeff 1 = 0 := by
    unfold P difference
    rw [coeff_sub, gaussian_linear, coeff_X_pow_mul']
    simp [gaussian_const]
  have hN : 1 ≤ (a+1)*(b+1) := Nat.mul_pos (by omega) (by omega)
  have htop := diff_symm_nat ha (i:=0) (Nat.zero_le _)
  simp only [Nat.sub_zero] at htop
  change P.coeff 0 = P.coeff ((a+1)*(b+1)) at htop
  rintro ⟨p,hp,up,down⟩
  by_cases h : 1 ≤ p
  · have hh := up (a:=0) (b:=1) ⟨by omega, by omega⟩ ⟨by omega, h⟩ (by omega)
    change P.coeff 0 ≤ P.coeff 1 at hh
    omega
  · have hh := down (a:=1) (b:=((a+1)*(b+1))) ⟨by omega,hN⟩ ⟨hp,le_rfl⟩ hN
    change P.coeff ((a+1)*(b+1)) ≤ P.coeff 1 at hh
    rw [← htop, h0, h1] at hh
    omega

/-- First differences on the closed left half suffice, including both central parities. -/
theorem good_of_left {P : ℤ[X]} {N : ℕ}
    (hs : ∀ i ≤ N, P.coeff i = P.coeff (N-i))
    (hd : ∀ i ≤ N/2, 0 ≤ delta P i) : Good N P := by
  have up : ∀ i j : ℕ, i ≤ j → j ≤ N/2 → P.coeff i ≤ P.coeff j := by
    intro i j hij
    induction j, hij using Nat.le_induction with
    | base => simp
    | succ j hij ih =>
      intro hj
      have h := hd (j+1) hj
      rw [delta, atZ_nat, show ((j+1 : ℕ):ℤ)-1 = (j:ℤ) by simp, atZ_nat] at h
      exact (ih (by omega)).trans (by omega)
  have h0 := hd 0 (Nat.zero_le _)
  simp [delta, atZ] at h0
  have nonneg : ∀ i ≤ N, 0 ≤ P.coeff i := by
    intro i hi
    by_cases hl : i ≤ N/2
    · exact h0.trans (up 0 i (Nat.zero_le _) hl)
    · rw [hs i hi]
      exact h0.trans (up 0 _ (Nat.zero_le _) (by omega))
  refine ⟨nonneg, N/2, by omega, ?_, ?_⟩
  · intro i hi j hj hij
    exact up _ _ hij hj.2
  · intro i hi j hj hij
    obtain ⟨hi1,hi2⟩ := hi
    obtain ⟨hj1,hj2⟩ := hj
    by_cases h : i = N/2
    · rw [hs j hj2, h]
      by_cases he : j = N/2
      · rw [← hs j hj2, he]
      · exact up _ _ (by omega) (by omega)
    · rw [hs i hi2, hs j hj2]
      exact up _ _ (by omega) (by omega)

end SZ
