import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Tactic

namespace SZ
open Polynomial

/-- The Gaussian rectangle polynomial by the q-Pascal recurrence. -/
noncomputable def gaussian : ℕ → ℕ → ℤ[X]
  | 0, _ => 1
  | _ + 1, 0 => 1
  | r + 1, w + 1 => gaussian (r+1) w + X^(w+1) * gaussian r (w+1)

@[simp] theorem gaussian_zero_left (w) : gaussian 0 w = 1 := by rw [gaussian]
@[simp] theorem gaussian_zero_right (r) : gaussian r 0 = 1 := by cases r <;> rw [gaussian]

noncomputable def factors (r w : ℕ) : ℤ[X] :=
  ∏ i ∈ Finset.range r, (1 - X^(w+i+1))

@[simp] theorem factors_zero (w) : factors 0 w = 1 := by simp [factors]

theorem factors_last (r w) :
    factors (r+1) w = factors r w * (1-X^(w+r+1)) := Finset.prod_range_succ _ _

theorem factors_first (r w) :
    factors (r+1) w = factors r (w+1) * (1-X^(w+1)) := by
  unfold factors
  rw [Finset.prod_range_succ']
  simp [Nat.add_comm, Nat.add_left_comm]

theorem factors_ne_zero (r w) : factors r w ≠ 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [factors_last]
    apply mul_ne_zero ih
    intro h
    have eq := congrArg (fun p : ℤ[X] => p.coeff 0) h
    simp [coeff_X_pow] at eq

/-- The division-free product formula fixes the Gaussian polynomial uniquely. -/
theorem gaussian_product (r w) :
    gaussian r w * factors r 0 = factors r w := by
  induction r generalizing w with
  | zero => simp
  | succ r ih =>
    induction w with
    | zero => simp
    | succ w hw =>
      rw [gaussian, add_mul, hw, factors_first r w, factors_last r (w+1),
        factors_last r 0]
      rw [show X^(w+1) * gaussian r (w+1) * (factors r 0 * (1-X^(0+r+1))) =
          X^(w+1) * (gaussian r (w+1) * factors r 0) * (1-X^(0+r+1)) by ring, ih]
      simp only [zero_add, show w+1+r+1 = (w+1)+(r+1) by omega, pow_add]
      ring

theorem gaussian_pascal_alt (r w) :
    gaussian (r+1) (w+1) = X^(r+1) * gaussian (r+1) w + gaussian r (w+1) := by
  apply mul_right_cancel₀ (factors_ne_zero (r+1) 0)
  rw [gaussian_product, add_mul, mul_assoc, gaussian_product, factors_first r w,
    factors_last r (w+1), factors_last r 0, ← mul_assoc (gaussian r (w+1)), gaussian_product]
  simp only [zero_add, show w+1+r+1 = (w+1)+(r+1) by omega, pow_add]
  ring

/-- Extend a coefficient by zero to negative indices. -/
def atZ (P : ℤ[X]) (z : ℤ) : ℤ := if 0 ≤ z then P.coeff z.toNat else 0

@[simp] theorem atZ_nat (P : ℤ[X]) (n : ℕ) : atZ P n = P.coeff n := by simp [atZ]
@[simp] theorem atZ_add (P Q : ℤ[X]) (z) :
    atZ (P+Q) z = atZ P z + atZ Q z := by simp [atZ]; split <;> simp_all
@[simp] theorem atZ_sub (P Q : ℤ[X]) (z) :
    atZ (P-Q) z = atZ P z - atZ Q z := by simp [atZ]; split <;> simp_all

theorem atZ_shift (P : ℤ[X]) (a : ℕ) (z : ℤ) :
    atZ (X^a*P) z = atZ P (z-a) := by
  unfold atZ
  rw [coeff_X_pow_mul']
  split_ifs <;> first | rfl | omega | (congr 1; omega)

theorem atZ_one (z : ℤ) : atZ 1 z = if z = 0 then 1 else 0 := by
  simp only [atZ, coeff_one]
  split_ifs <;> omega

/-- Padded symmetry, including indices outside the support. -/
theorem gaussian_reflect (r w : ℕ) (z : ℤ) :
    atZ (gaussian r w) z = atZ (gaussian r w) ((r:ℤ)*w-z) := by
  induction r generalizing w z with
  | zero => simp [atZ_one]
  | succ r ih =>
    induction w generalizing z with
    | zero => simp [atZ_one]
    | succ w hw =>
      conv_lhs => rw [gaussian]
      conv_rhs => rw [gaussian_pascal_alt]
      simp only [atZ_add, atZ_shift, Nat.cast_succ]
      rw [hw z, ih (w+1) (z-(w+1))]
      push_cast
      congr 2 <;> ring

theorem gaussian_const (r w) : (gaussian r w).coeff 0 = 1 := by
  induction r generalizing w with
  | zero => simp
  | succ r _ =>
    induction w with
    | zero => simp
    | succ w hw => rw [gaussian, coeff_add, coeff_X_pow_mul']; simp [hw]

theorem gaussian_linear (r w : ℕ) :
    (gaussian (r+1) (w+1)).coeff 1 = 1 := by
  induction w with
  | zero =>
    rw [gaussian, coeff_add, gaussian_zero_right, coeff_X_pow_mul']
    simp [gaussian_const, coeff_one]
  | succ w hw => rw [gaussian, coeff_add, coeff_X_pow_mul']; simp [hw]

end SZ
