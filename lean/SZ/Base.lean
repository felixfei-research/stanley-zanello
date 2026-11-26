import SZ.Expansion
import Mathlib.Algebra.Polynomial.Inductions

noncomputable section
namespace SZ.Base
open PowerSeries SZ.Series

private def den {R : Type*} [CommRing R] (x : R) := (1-x^2)*(1-x^3)*(1-x^4)*(1-x^5)
private def numerator {R : Type*} [CommRing R] (x : R) := 343-860*x+739*x^2-216*x^3

/-- Integer quotient after clearing the four coin denominators and the cubic denominator. -/
private def correction {R : Type*} [CommRing R] (x : R) :=
  (1+x^12+x^24+x^36+x^48)*(1+x^10+x^20+x^30+x^40+x^50) *
  (1-x+x^2)*(1-x^2+x^4)*(1-x+x^2-x^3+x^4) *
  (377 + 242*x - 279*x^2 - 945*x^3 - 1358*x^4 - 1258*x^5 - 638*x^6
    + 99*x^7 + 621*x^8 + 746*x^9 + 557*x^10 + 216*x^11)

set_option maxHeartbeats 4000000 in
private theorem certificate {R : Type*} [CommRing R] (x : R) :
    (1-x^60)^2*(720*(1-x)^4-numerator x*den x) = correction x*den x*(1-x)^4 := by
  unfold correction numerator den
  ring

private def cube : PowerSeries ℤ := mk fun n => ((n:ℤ)+7)^3

private theorem oneSub_zero (A : PowerSeries ℤ) : coeff 0 ((1-X)*A) = coeff 0 A := by
  simp [sub_mul]
private theorem oneSub_succ (A : PowerSeries ℤ) (n : ℕ) :
    coeff (n+1) ((1-X)*A) = coeff (n+1) A-coeff n A := by simp [sub_mul]

private theorem cube_eq : (1-X)^4*cube = numerator X := by
  have hn : numerator (X : PowerSeries ℤ) =
      C (343:ℤ) - C (860:ℤ)*X^1 + C (739:ℤ)*X^2 - C (216:ℤ)*X^3 := by simp [numerator]
  rw [hn, show (1-X)^4*cube=(1-X)*((1-X)*((1-X)*((1-X)*cube))) by ring]
  ext n
  rcases n with _|_|_|_|n
  all_goals simp only [oneSub_zero, oneSub_succ, cube, coeff_mk, map_sub, map_add, coeff_C_mul,
    coeff_X_pow, coeff_C, Nat.cast_succ, Nat.cast_zero]
  all_goals (try norm_num)
  all_goals (split_ifs <;> first | omega | ring)

private theorem den_cancel : den X*parts 4 = 1 := by
  unfold den
  rw [parts_succ 3,parts_succ 2,parts_succ 1,parts_succ 0,parts_zero,one_mul]
  calc
    _ = ((1-X^2)*coin 2)*((1-X^3)*coin 3)*((1-X^4)*coin 4)*((1-X^5)*coin 5) := by ring
    _ = _ := by simp [cancel_coin (j:=2) (by decide),cancel_coin (j:=3) (by decide),
      cancel_coin (j:=4) (by decide),cancel_coin (j:=5) (by decide)]

private theorem generating_identity :
    (720:PowerSeries ℤ)*parts 4 - cube = correction X*(coin 60)^2 := by
  let x : PowerSeries ℤ := X
  let A := (1-x^60)^2
  let B := (1-x)^4
  let D := den x
  let R := 720*parts 4 - cube
  have hD : D*parts 4=1 := den_cancel
  have hB : B*(coin 1)^4=1 := by
    have h : (1-x)*coin 1=1 := by simpa [x] using cancel_coin (j:=1) (by decide)
    dsimp [B]; rw [← mul_pow,h,one_pow]
  have hP : B*cube=numerator x := cube_eq
  have h1 : A*R*(D*B)=correction x*D*B := by
    calc
      _ = A*(720*(D*parts 4)*B-(B*cube)*D) := by dsimp [R]; ring
      _ = _ := by rw [hD,hP,mul_one]; exact certificate x
  have h2 : A*R=correction x := by
    calc
      _ = (A*R*(D*B))*(parts 4*coin 1^4) := by
        rw [show A*R*(D*B)*(parts 4*coin 1^4)=A*R*((D*parts 4)*(B*coin 1^4)) by ring,hD,hB]; simp
      _ = _ := by rw [h1]; calc
        _ = correction x*((D*parts 4)*(B*coin 1^4)) := by ring
        _ = _ := by rw [hD,hB]; simp
  have h60 : A*coin 60^2=1 := by
    dsimp [A,x]; rw [← mul_pow,cancel_coin (by decide),one_pow]
  change R = correction x*coin 60^2
  rw [← h2, mul_right_comm, h60, one_mul]

private theorem double_coin_bound (n : ℕ) : |coeff n (coin 60^2)| ≤ (n:ℤ)+1 := by
  rw [pow_two,abs_of_nonneg (nonneg_mul (nonneg_coin _) (nonneg_coin _) n),coeff_mul]
  calc
    _ ≤ ∑ _p ∈ Finset.antidiagonal n, (1:ℤ) := by
      apply Finset.sum_le_sum
      intro p _; simp only [coeff_coin]; split_ifs <;> decide
    _ = _ := by simp

private theorem polynomial_bound (P : Polynomial ℤ) :
    ∃ C : ℤ, 0 ≤ C ∧ ∀ n : ℕ, |coeff n ((P : PowerSeries ℤ)*coin 60^2)| ≤ C*((n:ℤ)+1) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨A,hA,ha⟩ := hp
    obtain ⟨B,hB,hb⟩ := hq
    refine ⟨A+B,by omega,?_⟩
    intro n; rw [Polynomial.coe_add, add_mul, map_add, add_mul]
    exact (abs_add_le _ _).trans (add_le_add (ha n) (hb n))
  | monomial i c =>
    refine ⟨|c|,abs_nonneg _,?_⟩
    intro n
    rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_mul, Polynomial.coe_C,
      Polynomial.coe_pow, Polynomial.coe_X, mul_assoc, coeff_C_mul, coeff_X_pow_mul', abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    split_ifs
    · exact (double_coin_bound _).trans (by exact_mod_cast Nat.succ_le_succ (Nat.sub_le n i))
    · simp; positivity

private theorem map_correction {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : R) :
    f (correction x)=correction (f x) := by
  simp only [correction, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]

theorem base_estimate : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    |720*(restricted 5 n:ℝ)-((n:ℝ)+7)^3| ≤ C*((n:ℝ)+1) := by
  obtain ⟨B,hB,hb⟩ := polynomial_bound (correction Polynomial.X)
  have hcoe : ((correction (Polynomial.X : Polynomial ℤ) : Polynomial ℤ) : PowerSeries ℤ) =
      correction X := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_correction, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
  rw [hcoe, ← generating_identity] at hb
  have h720 : (720 : PowerSeries ℤ) = C (720:ℤ) := by norm_num
  refine ⟨B,by exact_mod_cast hB,?_⟩
  intro n
  have h := hb n
  rw [h720,map_sub,coeff_C_mul,cube,coeff_mk] at h
  simp only [restricted, Int.natCast_nonneg, if_true, Int.toNat_natCast]
  exact_mod_cast h

end SZ.Base
