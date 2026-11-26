import SZ.Shape
import SZ.Series

namespace SZ
namespace Series
open PowerSeries

theorem nonneg_add {A B} (ha : Nonneg A) (hb : Nonneg B) : Nonneg (A+B) := by
  intro n; rw [map_add]; exact add_nonneg (ha _) (hb _)

theorem nonneg_X_pow (s : ℕ) : Nonneg (X^s) := by
  intro n; rw [coeff_X_pow]; split <;> decide

theorem parts_grow (r n) : coeff n (parts r) ≤ coeff n (parts (r+1)) := by
  have h : Nonneg (coin (r+2)-1) := by
    intro m
    simp only [map_sub, coeff_coin, coeff_one]
    split_ifs <;> simp_all
  have h' := nonneg_mul (nonneg_parts r) h n
  rwa [mul_sub, mul_one, ← parts_succ, map_sub, sub_nonneg] at h'

theorem step_small (r j : ℕ) (hj : j=2 ∨ j=3) :
    Nonneg ((1-X^j)*parts (r+2)) := by
  induction r with
  | zero =>
    change Nonneg ((1-X^j)*parts 2)
    rw [parts_succ 1, parts_succ 0, parts_zero, one_mul]
    rcases hj with rfl | rfl
    · rw [← mul_assoc, cancel_coin (by decide), one_mul]
      exact nonneg_coin _
    · rw [mul_comm (coin (0+2)), ← mul_assoc, cancel_coin (by decide), one_mul]
      exact nonneg_coin _
  | succ r ih =>
    rw [show r+1+2 = (r+2)+1 by omega, parts_succ (r+2), ← mul_assoc]
    exact nonneg_mul ih (nonneg_coin _)

theorem step_admissible (r s : ℕ) (hs : s ≠ 1) : Nonneg ((1-X^s)*parts (r+2)) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    by_cases h0 : s=0
    · subst s; intro n; simp
    by_cases hj : s=2 ∨ s=3
    · exact step_small _ _ hj
    obtain ⟨a,ha⟩ : ∃ a, s=a+2 := ⟨s-2,by omega⟩
    rw [ha, pow_add]
    rw [show (1-X^a*X^2)*parts (r+2) =
       (1-X^a)*parts (r+2) + X^a*((1-X^2)*parts (r+2)) by ring]
    exact nonneg_add (ih a (by omega) (by omega))
      (nonneg_mul (nonneg_X_pow a) (step_small _ _ (Or.inl rfl)))

end Series

open Polynomial
open Series

theorem delta_series (P : ℤ[X]) (n : ℕ) :
    delta P n = PowerSeries.coeff n ((1-PowerSeries.X)*(P : PowerSeries ℤ)) := by
  rw [sub_mul, one_mul, map_sub, ← Polynomial.coe_X, ← Polynomial.coe_mul,
    Polynomial.coeff_coe, Polynomial.coeff_coe]
  cases n with
  | zero => simp [delta, atZ]
  | succ n => simp [delta, atZ]; omega

theorem delta_edge (r w n : ℕ) (hn : n ≤ w) :
    delta (gaussian (r+1) w) n = PowerSeries.coeff n (parts r) := by
  rw [delta_series, difference_series, edge_coeff _ _ _ hn]

theorem delta_negative (P : ℤ[X]) {z : ℤ} (hz : z < 0) : delta P z = 0 := by
  unfold delta atZ
  rw [if_neg (by omega), if_neg (by omega), sub_self]

/-- Full edge lemma, uniform in all four parameters. -/
theorem edge {k ell t s n : ℕ} (hk : 5 ≤ k) (ha : Aligned k ell t s)
    (hs : s ≠ 1) (hn : n ≤ ell) : 0 ≤ delta (difference k ell t s) n := by
  obtain ⟨r,hr⟩ : ∃ r, k=r+5 := ⟨k-5,by omega⟩
  subst k
  rw [delta_shift_sub, delta_edge (r+4) ell n hn]
  by_cases hsn : n < s
  · rw [delta_negative _ (by omega), sub_zero]
    exact nonneg_parts _ _
  have hne : s ≤ ell := by omega
  have ht : ell ≤ t := by
    unfold Aligned at ha
    simp only [show r+5-2=r+3 by omega] at ha
    by_contra! h
    have h' := Nat.mul_lt_mul_of_pos_left h (by omega : 0 < r+3)
    nlinarith
  rw [show r+5-2 = (r+2)+1 by omega, ← Nat.cast_sub (by omega : s ≤ n),
    delta_edge (r+2) t (n-s) (by omega)]
  have h := step_admissible r s hs n
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', if_pos (by omega)] at h
  have h1 := parts_grow (r+2) n
  have h2 := parts_grow (r+3) n
  exact sub_nonneg.mpr ((sub_nonneg.mp h).trans (h1.trans h2))

/-- A uniform bound on every first difference, with an explicit constant. -/
theorem small_bound (r w n : ℕ) :
    |delta (gaussian (r+2) w) n| ≤ (2:ℤ)^(r+2)*((n:ℤ)+1)^r := by
  rw [delta_series, difference_series (r+1)]
  apply numerator_bound
  intro i hi
  rw [abs_of_nonneg (nonneg_parts _ _)]
  exact (parts_bound r i).trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hi) _)

end SZ
