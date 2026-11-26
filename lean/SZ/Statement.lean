import SZ.Gaussian

namespace SZ
open Polynomial

noncomputable def difference (k ell t s : ℕ) : ℤ[X] :=
  gaussian k ell - X^s * gaussian (k-2) t

def Aligned (k ell t s : ℕ) : Prop := (k-2)*t+2*s=k*ell

/-- An arbitrary peak is allowed. End zeros up to the nominal rectangle degree are kept. -/
def Unimodal (N : ℕ) (P : ℤ[X]) : Prop :=
  ∃ p ≤ N, MonotoneOn P.coeff (Set.Icc 0 p) ∧ AntitoneOn P.coeff (Set.Icc p N)

def Good (N : ℕ) (P : ℤ[X]) : Prop :=
  (∀ n ≤ N, 0 ≤ P.coeff n) ∧ Unimodal N P

/-- Integer inequalities obtained by clearing the positive denominator k-2. -/
def Admissible (k : ℕ) (m b : ℤ) : Prop :=
  k ≤ m ∧ (k:ℤ)-2 ≤ b ∧ ((k:ℤ)-2)*b ≤ k*m-4*k+4 ∧ 2 ∣ (k:ℤ)*(m-b)

def exponent (k : ℕ) (m b : ℤ) : ℤ := (k:ℤ)*(m-b)/2+b-2*k+2

noncomputable def originalPolynomial (k : ℕ) (m b : ℤ) : ℤ[X] :=
  gaussian k (m-k).toNat - X^(exponent k m b).toNat * gaussian (k-2) (b-((k:ℤ)-2)).toNat

/-- The full assertion in the original variables, including the exceptional direction. -/
def Conjecture11iv : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ M : ℕ, ∀ m b : ℤ, (M:ℤ) ≤ m → Admissible k m b →
    (Good (k*(m-k).toNat) (originalPolynomial k m b) ↔ ((k:ℤ)-2)*b ≠ k*m-4*k+2)

def RectangleAssertion : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ W : ℕ, ∀ ell t s : ℕ, W ≤ ell → Aligned k ell t s →
    (Good (k*ell) (difference k ell t s) ↔ s ≠ 1)

theorem exponent_twice {k : ℕ} {m b : ℤ} (hp : 2 ∣ (k:ℤ)*(m-b)) :
    2*exponent k m b = k*m-4*k+4-((k:ℤ)-2)*b := by
  obtain ⟨z,hz⟩ := hp
  unfold exponent
  rw [hz, Int.mul_ediv_cancel_left _ (by decide : (2:ℤ) ≠ 0)]
  linarith only [show (k:ℤ)*m-k*b=2*z by linear_combination hz]

theorem original_to_rectangle {k : ℕ} (hk : 5 ≤ k) {m b : ℤ} (h : Admissible k m b) :
    let ell := (m-k).toNat
    let t := (b-((k:ℤ)-2)).toNat
    let s := (exponent k m b).toNat
    Aligned k ell t s ∧ (s = 1 ↔ ((k:ℤ)-2)*b = k*m-4*k+2) := by
  obtain ⟨hm,hb,hu,hp⟩ := h
  have h2 := exponent_twice hp
  have hs : 0 ≤ exponent k m b := by omega
  dsimp
  constructor
  · unfold Aligned
    zify [show 2 ≤ k by omega]
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ m-k), Int.toNat_of_nonneg (by omega : 0 ≤ b-((k:ℤ)-2)),
      Int.toNat_of_nonneg hs]
    linarith only [h2]
  · omega

theorem rectangle_to_original {k ell t s : ℕ} (hk : 5 ≤ k) (h : Aligned k ell t s) :
    let m := (k:ℤ)+ell
    let b := (k:ℤ)-2+t
    Admissible k m b ∧ exponent k m b = s := by
  dsimp
  unfold Aligned at h
  zify [show 2 ≤ k by omega] at h
  have hp : (k:ℤ)*((k+ell)-(k-2+t)) = 2*((s:ℤ)-(k-2+t)+2*k-2) := by
    linear_combination -h
  have he : exponent k ((k:ℤ)+ell) ((k:ℤ)-2+t) = s := by
    unfold exponent
    rw [hp, Int.mul_ediv_cancel_left _ (by decide : (2:ℤ) ≠ 0)]
    ring
  refine ⟨⟨by omega, by omega, ?_, ⟨_,hp⟩⟩, he⟩
  have := exponent_twice (dvd_of_mul_right_eq _ hp.symm)
  -- The upper bound is exactly twice the nonnegative shift.
  rw [he] at this
  linarith

theorem formulations_equivalent : Conjecture11iv ↔ RectangleAssertion := by
  constructor
  · intro hyp k hk
    obtain ⟨M,hM⟩ := hyp k hk
    refine ⟨M, ?_⟩
    intro ell t s hw ha
    obtain ⟨had, he⟩ := rectangle_to_original hk ha
    have h := hM ((k:ℤ)+ell) ((k:ℤ)-2+t) (by omega) had
    have h2 := exponent_twice had.2.2.2
    rw [he] at h2
    simp only [originalPolynomial, he, add_sub_cancel_left, Int.toNat_natCast] at h
    change Good _ _ ↔ _ at h
    change Good _ _ ↔ _
    exact h.trans (by omega)
  · intro hyp k hk
    obtain ⟨W,hW⟩ := hyp k hk
    refine ⟨k+W, ?_⟩
    intro m b hm ha
    obtain ⟨hal,he⟩ := original_to_rectangle hk ha
    have hg := hW _ _ _ (by omega) hal
    exact hg.trans (not_congr he)

theorem difference_reflect {k ell t s : ℕ} (ha : Aligned k ell t s) (z : ℤ) :
    atZ (difference k ell t s) z = atZ (difference k ell t s) ((k:ℤ)*ell-z) := by
  unfold difference
  rw [atZ_sub, atZ_sub, atZ_shift, atZ_shift, gaussian_reflect k ell z,
    gaussian_reflect (k-2) t (z-s)]
  unfold Aligned at ha
  have ha' := congrArg (fun n : ℕ => (n : ℤ)) ha
  push_cast only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at ha'
  congr 2
  linarith

end SZ
