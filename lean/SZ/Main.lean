import SZ.Base
import SZ.Lift

namespace SZ

theorem rank_five : RankEstimate 0 := by
  obtain ⟨B,hB,hb⟩ := Base.base_estimate
  refine ⟨B+343,by linarith,?_⟩
  intro v
  by_cases hv : v < 0
  · have hz : (v:ℝ) < 0 := by exact_mod_cast hv
    have h := residual_negative 5 (by decide) hv
    norm_num [halfSum] at h
    simp [max_eq_right hz.le]
    linarith
  · lift v to ℕ using (by omega)
    have h := hb v
    have hfac : normalizer 5 = 720 := by norm_num [normalizer, Nat.factorial]
    have hs : halfSum 5 = 7 := by norm_num [halfSum]
    simp only [zero_add, residual, hfac, hs, Spline.cut, Int.cast_natCast,
      max_eq_left (by positivity : 0 ≤ (v:ℝ)+7), max_eq_left (Nat.cast_nonneg (α:=ℝ) v),
      pow_one]
    nlinarith [Nat.cast_nonneg (α:=ℝ) v]

theorem restricted_estimate : RestrictedEstimate := by
  intro p
  have h : RankEstimate p := by
    induction p with
    | zero => exact rank_five
    | succ p ih => exact rank_step p ih
  simpa only [RankEstimate, residual, show p+5-2=p+3 by omega] using h

/-- Stanley and Zanello, Conjecture 1.1(iv), in the original m,b variables. -/
theorem stanley_zanello : Conjecture11iv := conjecture_of_restricted restricted_estimate

end SZ
