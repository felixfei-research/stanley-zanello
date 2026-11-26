import SZ.Expansion
import SZ.Reduction

noncomputable section
namespace SZ
open Spline

private theorem size_bound {k ell n : ℕ} (hk : 5 ≤ k) (hn : n ≤ k*ell/2) :
    (n:ℝ)+1 ≤ ((k:ℝ)+1)*widthScale k ell := by
  have h1 := widthScale_one_le (k:=k) (by omega) ell
  have hn' : (n:ℝ) ≤ k*ell := by exact_mod_cast (by omega : n ≤ k*ell)
  have hel : (ell:ℝ) ≤ widthScale k ell := by
    unfold widthScale; linarith [Nat.cast_nonneg (α:=ℝ) k]
  nlinarith [mul_le_mul_of_nonneg_left hel (Nat.cast_nonneg (α:=ℝ) k)]

/-- The scale-normalized quadratic path error supplies the two missing orders of L. -/
theorem uniform_of_restricted (hr : RestrictedEstimate) : UniformEstimate := by
  intro p
  let k := p+5
  obtain ⟨C,hC,hr'⟩ := hr p
  obtain ⟨B,hB,hpath⟩ := path_quadratic k p
  let M := C*((k:ℝ)+1)^(p+1)
  let T := (Fintype.card (Finset (Fin k)) : ℝ)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨T*M+B, by dsimp [T]; positivity, ?_⟩
  intro ell n hn
  let L := widthScale k ell
  let x := location k ell n
  let u := L⁻¹
  have hL1 : 1 ≤ L := widthScale_one_le (k:=k) (by dsimp [k]; omega) ell
  have hL : 0 < L := by linarith
  have hz (J : Finset (Fin k)) : 1+max ((n:ℝ)-weight ell J) 0 ≤ ((k:ℝ)+1)*L := by
    have h := size_bound (k:=k) (by dsimp [k]; omega) hn
    have hn0 := Nat.cast_nonneg (α:=ℝ) n
    have hw := Nat.cast_nonneg (α:=ℝ) (weight ell J)
    linarith [max_le (show (n:ℝ)-weight ell J ≤ n by linarith) hn0]
  let R := fun J : Finset (Fin k) => normalizer k*(restricted k ((n:ℤ)-weight ell J):ℝ) -
    L^(p+3)*cut (p+3) (x-J.card-u*eps J)
  have hR (J : Finset (Fin k)) : |R J| ≤ M*L^(p+1) := by
    have h := hr' ((n:ℤ)-weight ell J)
    push_cast at h
    have harg := scale_argument (k:=k) (ell:=ell) (n:=n) hL J
    change (n:ℝ)-weight ell J+halfSum k = L*(x-J.card-u*eps J) at harg
    have hcut : cut (p+3) ((n:ℝ)-weight ell J+halfSum k) =
        L^(p+3)*cut (p+3) (x-J.card-u*eps J) := by
      rw [harg]; unfold cut
      rw [← mul_zero L, ← mul_max_of_nonneg _ _ hL.le, mul_pow, mul_zero]
    change |normalizer k*_ - cut (p+3) ((n:ℝ)-weight ell J+halfSum k)| ≤ _ at h
    rw [hcut] at h
    apply le_trans h
    calc
      _ ≤ C*(((k:ℝ)+1)*L)^(p+1) := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (hz J) _) hC
      _ = _ := by rw [mul_pow]; ring
  have hsum : |normalizer k*(delta (gaussian k ell) n : ℝ) - L^(p+3)*path k (p+3) x u| ≤
      T*M*L^(p+1) := by
    have hdelta := exact_expansion (p+4) ell n
    have hd : (delta (gaussian k ell) n : ℝ) = ∑ J : Finset (Fin k), (-1:ℝ)^J.card*
        (restricted k ((n:ℤ)-weight ell J):ℝ) := by exact_mod_cast hdelta
    rw [hd]
    have hh : normalizer k*(∑ J : Finset (Fin k), (-1:ℝ)^J.card*
          (restricted k ((n:ℤ)-weight ell J):ℝ)) - L^(p+3)*path k (p+3) x u =
        ∑ J : Finset (Fin k), (-1:ℝ)^J.card*R J := by
      unfold path
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro J _; dsimp [R]; ring
    rw [hh]
    calc
      _ ≤ ∑ J : Finset (Fin k), |(-1:ℝ)^J.card*R J| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _J : Finset (Fin k), M*L^(p+1) := Finset.sum_le_sum fun J _ => by simpa [abs_mul,abs_pow] using hR J
      _ = _ := by simp [T]; ring
  have hx := location_bounds (k:=k) (by dsimp [k]; omega) hn
  have hp := hpath x ⟨hx.1,by linarith [hx.2, Nat.cast_nonneg (α:=ℝ) k]⟩ u
    ⟨inv_nonneg.mpr hL.le, inv_le_one_of_one_le₀ hL1⟩
  have hscaled := mul_le_mul_of_nonneg_left hp (pow_nonneg hL.le (p+3))
  have cancel : L^(p+3)*(B*u^2)=B*L^(p+1) := by
    dsimp [u]; rw [show p+3=(p+1)+2 by omega, pow_add]; field_simp
  rw [cancel] at hscaled
  change |normalizer k*_ - L^(p+3)*diff k (cut (p+3)) x| ≤ (T*M+B)*L^(p+1)
  have tri := abs_sub_le (normalizer k*(delta (gaussian k ell) n : ℝ))
    (L^(p+3)*path k (p+3) x u) (L^(p+3)*diff k (cut (p+3)) x)
  rw [← mul_sub, abs_mul, abs_of_nonneg (pow_nonneg hL.le _)] at tri
  linarith

/-- Corollary 3.3, stated separately with the positive constant uniform in the index. -/
theorem bulk_lower_of_uniform (hu : UniformEstimate) (p : ℕ) :
    let k := p+5
    ∃ γ : ℝ, 0 < γ ∧ ∃ W : ℕ, ∀ ell n : ℕ, W ≤ ell → ell ≤ n → n ≤ k*ell/2 →
      γ*(widthScale k ell)^(p+2) ≤ (delta (gaussian k ell) n : ℝ) := by
  let k := p+5
  let K := normalizer k
  have hK : 0 < K := by dsimp [K,normalizer]; positivity
  obtain ⟨C,hC,hU⟩ := hu p
  obtain ⟨a,ha,hcurve⟩ := Spline.curvature (p+1)
  obtain ⟨W,hW⟩ := exists_nat_ge (4*C/a)
  refine ⟨(a/4)/K, by positivity, W,?_⟩
  intro ell n hw he hn
  change n ≤ k*ell/2 at hn
  let L := widthScale k ell
  let x := location k ell n
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (widthScale_one_le (k:=k) (by dsimp [k];omega) ell)
  have hk : (5:ℝ) ≤ k := by dsimp [k]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p]
  have hxc : (1/2:ℝ) ≤ x := by
    apply (le_div_iff₀ hL).mpr
    unfold L widthScale halfSum
    have he' : (ell:ℝ) ≤ n := by exact_mod_cast he
    nlinarith [sq_nonneg ((k:ℝ)-3),Nat.cast_nonneg (α:=ℝ) ell]
  have hspan : Spline.span (p+1+2)/2 = (k:ℝ)/2 := by simp [k,Spline.span]; ring
  have hcur := hcurve x ⟨hxc,hspan ▸ (location_bounds (k:=k) (by dsimp [k]; omega) hn).2⟩
  rw [hspan] at hcur
  have hd := center_distance (n:=n) hL
  change L*((k:ℝ)/2-x) = _ at hd
  have hn' : (2:ℝ)*n ≤ k*ell := by exact_mod_cast (by omega : 2*n ≤ k*ell)
  have hmain : a/2 ≤ L*Spline.velocity (p+2) x := by
    nlinarith [mul_le_mul_of_nonneg_left hcur hL.le, mul_le_mul_of_nonneg_left
      (show 1/2 ≤ L*((k:ℝ)/2-x) by linarith) ha.le]
  have hWL : (W:ℝ) ≤ L := by
    have wh : (W:ℝ) ≤ ell := by exact_mod_cast hw
    dsimp [L,widthScale]; linarith
  have hdom : C ≤ (a/4)*L := by
    nlinarith [(div_le_iff₀ ha).mp hW, mul_le_mul_of_nonneg_left hWL ha.le]
  have hU' := (abs_le.mp (hU ell n hn)).1
  change -(C*L^(p+1)) ≤ K*(delta (gaussian k ell) n : ℝ)-L^(p+3)*Spline.velocity (p+2) x at hU'
  have h1 := mul_le_mul_of_nonneg_right hdom (pow_nonneg hL.le (p+1))
  have h2 := mul_le_mul_of_nonneg_right hmain (pow_nonneg hL.le (p+2))
  change ((a/4)/K)*L^(p+2) ≤ _
  rw [div_mul_eq_mul_div, div_le_iff₀ hK]
  rw [pow_succ L (p+2),pow_succ L (p+1)] at hU'
  rw [pow_succ L (p+1)] at h2 ⊢
  linarith

theorem bulk_of_uniform (hu : UniformEstimate) : BulkComparison := by
  intro k hk
  obtain ⟨p,rfl⟩ : ∃ p, k=p+5 := ⟨k-5,by omega⟩
  let k := p+5
  obtain ⟨γ,hγ,W,hbulk⟩ := bulk_lower_of_uniform hu p
  let D := (2:ℝ)^(k-2)*((k:ℝ)+1)^(p+1)
  obtain ⟨W',hW'⟩ := exists_nat_ge (D/γ)
  refine ⟨max W W',?_⟩
  intro ell n hw he hn
  let L := widthScale k ell
  have hL : 0 ≤ L := (zero_le_one.trans (widthScale_one_le (k:=k) (by dsimp [k];omega) ell))
  have hw' : (W':ℝ) ≤ ell := by exact_mod_cast ((le_max_right W W').trans hw)
  have hWL : (W':ℝ) ≤ L := by dsimp [L,widthScale]; linarith [Nat.cast_nonneg (α:=ℝ) k]
  have hD : D ≤ γ*L := by
    nlinarith [(div_le_iff₀ hγ).mp hW',mul_le_mul_of_nonneg_left hWL hγ.le]
  have hmain := hbulk ell n ((le_max_left W W').trans hw) he hn
  have hsize := size_bound (k:=k) (by dsimp [k];omega) hn
  have hc : (2:ℝ)^(k-2)*((n:ℝ)+1)^(p+1) ≤ D*L^(p+1) := by
    dsimp [D]
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsize _) (by positivity)
  have hd : D*L^(p+1) ≤ γ*L^(p+2) := by
    rw [pow_succ L (p+1)]
    linarith only [mul_le_mul_of_nonneg_right hD (pow_nonneg hL (p+1))]
  rw [show p+5-4=p+1 by omega]
  exact_mod_cast hc.trans (hd.trans hmain)

theorem conjecture_of_restricted (h : RestrictedEstimate) : Conjecture11iv :=
  conjecture_of_bulk (bulk_of_uniform (uniform_of_restricted h))

end SZ
