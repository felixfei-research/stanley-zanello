import SZ.Comparison
import SZ.Averaging

noncomputable section
namespace SZ
open PowerSeries

def restricted (r : ℕ) (z : ℤ) : ℤ :=
  if 0 ≤ z then coeff z.toNat (Series.parts (r-1)) else 0

def weight {k : ℕ} (ell : ℕ) (J : Finset (Fin k)) := ∑ i ∈ J, (ell+i.val+1)

theorem exact_expansion (r ell n : ℕ) :
    delta (gaussian (r+1) ell) n = ∑ J : Finset (Fin (r+1)), (-1:ℤ)^J.card*
      restricted (r+1) ((n:ℤ)-weight ell J) := by
  classical
  let k := r+1
  let A := Series.parts r
  have hprod : (factors k ell : PowerSeries ℤ) =
      ∏ i : Fin k, (1-X^(ell+i.val+1)) := by
    unfold factors
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod, Fin.prod_univ_eq_prod_range (fun j => (1-X^(ell+j+1) : PowerSeries ℤ)) k]
    simp
  rw [delta_series, Series.difference_series]
  change coeff n ((factors k ell : PowerSeries ℤ)*A) = _
  rw [hprod, Finset.prod_sub (fun _ : Fin k => 1) (fun i => X^(ell+i.val+1)), Finset.sum_mul, map_sum]
  simp only [Finset.powerset_univ, Finset.prod_const_one, mul_one]
  apply Finset.sum_congr rfl
  intro J _
  rw [Finset.prod_pow_eq_pow_sum, show ((-1:PowerSeries ℤ)^J.card) = C ((-1:ℤ)^J.card) by simp,
    mul_assoc, coeff_C_mul, coeff_X_pow_mul']
  let a := weight ell J
  change (-1:ℤ)^J.card*(if a ≤ n then coeff (n-a) A else 0) =
    (-1:ℤ)^J.card*(if 0 ≤ (n:ℤ)-a then coeff ((n:ℤ)-a).toNat A else 0)
  by_cases ha : a ≤ n
  · rw [if_pos ha, if_pos (by omega), ← Nat.cast_sub ha, Int.toNat_natCast]
  · rw [if_neg ha, if_neg (by omega)]

def widthScale (k ell : ℕ) : ℝ := ell+((k:ℝ)+1)/2
def halfSum (k : ℕ) : ℝ := ((k:ℝ)*(k+1)-2)/4
def location (k ell n : ℕ) : ℝ := ((n:ℝ)+halfSum k)/widthScale k ell
def normalizer (k : ℕ) : ℝ := k.factorial * ((k-2).factorial:ℕ)

theorem widthScale_one_le {k : ℕ} (hk : 1 ≤ k) (ell : ℕ) : 1 ≤ widthScale k ell := by
  unfold widthScale
  have h : (1:ℝ) ≤ k := by exact_mod_cast hk
  linarith [Nat.cast_nonneg (α:=ℝ) ell]

theorem weight_center {k : ℕ} (ell : ℕ) (J : Finset (Fin k)) :
    (weight ell J : ℝ) = J.card*widthScale k ell + Spline.eps J := by
  unfold weight Spline.eps Spline.offset
  push_cast
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp [widthScale, Finset.sum_add_distrib]
  ring

theorem scale_argument {k ell n : ℕ} (hL : 0 < widthScale k ell) (J : Finset (Fin k)) :
    (n:ℝ)-weight ell J+halfSum k =
    widthScale k ell * (location k ell n-J.card-(widthScale k ell)⁻¹*Spline.eps J) := by
  rw [weight_center]; unfold location
  field_simp; ring

theorem center_distance {k ell n : ℕ} (hL : 0 < widthScale k ell) :
    widthScale k ell*((k:ℝ)/2-location k ell n) = ((k:ℝ)*ell+1)/2-n := by
  unfold location
  field_simp
  unfold halfSum widthScale
  ring

theorem location_bounds {k ell n : ℕ} (hk : 5 ≤ k) (hn : n ≤ k*ell/2) :
    location k ell n ∈ Set.Icc (0:ℝ) (k/2) := by
  have hk' : (5:ℝ) ≤ k := by exact_mod_cast hk
  have hL := lt_of_lt_of_le zero_lt_one (widthScale_one_le (k:=k) (by omega) ell)
  have hn' : (2:ℝ)*n ≤ k*ell := by exact_mod_cast (by omega : 2*n ≤ k*ell)
  constructor
  · apply div_nonneg _ hL.le
    unfold halfSum
    nlinarith [Nat.cast_nonneg (α:=ℝ) n, sq_nonneg (k:ℝ)]
  · have h := center_distance (n:=n) hL
    by_contra! hlt
    nlinarith [mul_neg_of_pos_of_neg hL (sub_neg.mpr hlt)]

/-- Lemma 2.1 in scaled form, with all integer arguments including negative ones. -/
def RestrictedEstimate : Prop :=
  ∀ p : ℕ, let k := p+5
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℤ,
      |normalizer k*(restricted k v:ℝ) - Spline.cut (p+3) ((v:ℝ)+halfSum k)| ≤
        C*(1+max (v:ℝ) 0)^(p+1)

/-- Proposition 3.1. The error constant is independent of the moving index. -/
def UniformEstimate : Prop :=
  ∀ p : ℕ, let k := p+5
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ell n : ℕ, n ≤ k*ell/2 →
      |normalizer k*(delta (gaussian k ell) n : ℝ) -
        (widthScale k ell)^(p+3)*Spline.velocity (p+2) (location k ell n)| ≤
        C*(widthScale k ell)^(p+1)

end SZ
