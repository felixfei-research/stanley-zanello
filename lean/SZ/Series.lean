import SZ.Gaussian
import Mathlib.RingTheory.PowerSeries.Basic

namespace SZ
namespace Series
open PowerSeries

/-- Geometric series counting copies of a part of size j. -/
noncomputable def coin (j : ℕ) : PowerSeries ℤ := mk fun n => if j ∣ n then 1 else 0

@[simp] theorem coeff_coin (j n : ℕ) :
    coeff n (coin j) = if j ∣ n then 1 else 0 := coeff_mk _ _

/-- Product for allowed part sizes 2,...,r+1, the empty product at r=0. -/
noncomputable def parts (r : ℕ) : PowerSeries ℤ := ∏ j ∈ Finset.range r, coin (j+2)

theorem parts_succ (r) : parts (r+1) = parts r * coin (r+2) := Finset.prod_range_succ _ _
@[simp] theorem parts_zero : parts 0 = 1 := by simp [parts]

theorem cancel_coin {j : ℕ} (hj : 0 < j) : (1-X^j)*coin j = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul']
  simp only [coeff_coin, coeff_one]
  by_cases h : j ≤ n
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le h
    simp [hj.ne']
  · by_cases hn : n=0
    · simp [hn, hj.ne']
    · have hnd : ¬ j ∣ n := fun hd => h (Nat.le_of_dvd (by omega) hd)
      simp [hn,h,hnd]

def Nonneg (A : PowerSeries ℤ) : Prop := ∀ n, 0 ≤ coeff n A

theorem nonneg_mul {A B} (ha : Nonneg A) (hb : Nonneg B) : Nonneg (A*B) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun p _ => mul_nonneg (ha _) (hb _)

theorem nonneg_coin (j) : Nonneg (coin j) := by intro n; simp; split <;> decide

theorem nonneg_parts (r) : Nonneg (parts r) := by
  induction r with
  | zero => intro n; simp [coeff_one]; split <;> decide
  | succ r ih => rw [parts_succ]; exact nonneg_mul ih (nonneg_coin _)

theorem cancel_den (r) : (factors (r+1) 0 : PowerSeries ℤ) * parts r = 1-X := by
  induction r with
  | zero => simp [factors_last]
  | succ r ih =>
    rw [factors_last, parts_succ, Polynomial.coe_mul, Polynomial.coe_sub,
      Polynomial.coe_one, Polynomial.coe_pow, Polynomial.coe_X, zero_add]
    calc
      _ = ((factors (r+1) 0 : PowerSeries ℤ) * parts r) * ((1-X^(r+2))*coin (r+2)) := by ring
      _ = _ := by rw [ih, cancel_coin (by omega), mul_one]

theorem difference_series (r w) :
    (1-X)*(gaussian (r+1) w : PowerSeries ℤ) = (factors (r+1) w : PowerSeries ℤ)*parts r := by
  rw [← gaussian_product, Polynomial.coe_mul, mul_assoc, cancel_den, mul_comm]

theorem edge_coeff (r w n) (hn : n ≤ w) (A : PowerSeries ℤ) :
    coeff n ((factors r w : PowerSeries ℤ)*A) = coeff n A := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [factors_last, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_pow, Polynomial.coe_X]
    rw [show (factors r w : PowerSeries ℤ)*(1-X^(w+r+1))*A =
        (factors r w : PowerSeries ℤ)*A - X^(w+r+1)*((factors r w : PowerSeries ℤ)*A) by ring,
      map_sub, coeff_X_pow_mul', if_neg (by omega), sub_zero, ih]

theorem parts_bound (r n : ℕ) : coeff n (parts (r+1)) ≤ ((n:ℤ)+1)^r := by
  induction r generalizing n with
  | zero =>
    rw [parts_succ, parts_zero, one_mul, coeff_coin, pow_zero]
    split <;> decide
  | succ r ih =>
    rw [parts_succ, coeff_mul]
    calc
      _ ≤ ∑ _p ∈ Finset.antidiagonal n, ((n:ℤ)+1)^r := by
        apply Finset.sum_le_sum
        intro p hp
        have hn := Finset.mem_antidiagonal.mp hp
        rw [coeff_coin]
        split
        · rw [mul_one]
          exact (ih p.1).trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast (by omega : p.1+1 ≤ n+1)) _)
        · simp; positivity
      _ = _ := by simp [pow_succ]; ring

theorem numerator_bound (r w n : ℕ) (A : PowerSeries ℤ) (B : ℤ)
    (hb : ∀ i ≤ n, |coeff i A| ≤ B) :
    |coeff n ((factors r w : PowerSeries ℤ)*A)| ≤ 2^r*B := by
  induction r generalizing n with
  | zero => simpa using hb n le_rfl
  | succ r ih =>
    rw [factors_last, Polynomial.coe_mul, Polynomial.coe_sub, Polynomial.coe_one,
      Polynomial.coe_pow, Polynomial.coe_X]
    rw [show (factors r w : PowerSeries ℤ)*(1-X^(w+r+1))*A =
        (factors r w : PowerSeries ℤ)*A - X^(w+r+1)*((factors r w : PowerSeries ℤ)*A) by ring,
      map_sub, coeff_X_pow_mul']
    have h1 := ih n hb
    have h2 := ih (n-(w+r+1)) (fun i hi => hb i (by omega))
    have hp := (abs_nonneg _).trans h1
    have htri := abs_sub (coeff n ((factors r w : PowerSeries ℤ)*A)) (if w+r+1 ≤ n then coeff (n-(w+r+1)) ((factors r w : PowerSeries ℤ)*A) else 0)
    rw [pow_succ]
    split_ifs at * <;> (try simp only [abs_zero, sub_zero, add_zero] at *) <;> linarith

end Series
end SZ
