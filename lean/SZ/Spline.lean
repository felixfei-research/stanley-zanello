import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Tactic

namespace SZ.Spline
open Set Filter
open scoped Topology

def cut (p : ℕ) (x : ℝ) := (max x 0)^p

theorem cut_deriv (p : ℕ) (x : ℝ) :
    HasDerivAt (cut (p+2)) (((p:ℝ)+2)*cut (p+1) x) x := by
  have hpow (y : ℝ) : HasDerivAt (fun t : ℝ => t^(p+2)) (((p:ℝ)+2)*y^(p+1)) y := by
    simpa using (hasDerivAt_pow (p+2) y)
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · simp only [cut, max_eq_right hx.le, zero_pow (Nat.succ_ne_zero p), mul_zero]
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with t ht using by simp [cut, max_eq_right ht.le]
  · simp only [cut, max_self, zero_pow (Nat.succ_ne_zero p), mul_zero]
    have hL : HasDerivWithinAt (fun t : ℝ => (max t 0)^(p+2)) 0 (Iic 0) 0 := by
      apply ((hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt (s:=Iic 0)).congr_of_mem _ (by simp)
      intro t ht; change t ≤ 0 at ht; simp [max_eq_right ht]
    have hR : HasDerivWithinAt (fun t : ℝ => (max t 0)^(p+2)) 0 (Ici 0) 0 := by
      have h := (hpow 0).hasDerivWithinAt (s:=Ici 0)
      simp only [zero_pow (Nat.succ_ne_zero p), mul_zero] at h
      apply h.congr_of_mem _ (by simp)
      intro t ht; change 0 ≤ t at ht; simp [max_eq_left ht]
    simpa [Iic_union_Ici] using hL.union hR
  · rw [show cut (p+1) x=x^(p+1) by simp [cut,max_eq_left hx.le]]
    apply (hpow x).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx] with t ht using by simp [cut,max_eq_left ht.le]

def diff : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f, x => f x
  | n+1, f, x => diff n f x - diff n f (x-1)

theorem diff_deriv (n : ℕ) (f g : ℝ → ℝ) (a : ℝ) (h : ∀ x, HasDerivAt f (a*g x) x) (x : ℝ) :
    HasDerivAt (diff n f) (a*diff n g x) x := by
  induction n generalizing x with
  | zero => exact h x
  | succ n ih =>
    rw [diff, mul_sub]
    exact (ih x).sub ((ih (x-1)).comp_sub_const x 1)

/-- Height r+2 cardinal spline multiplied by (r+1)!. -/
def density (r : ℕ) := diff (r+2) (cut (r+1))
def span (r : ℕ) : ℝ := (r:ℝ)+2
def velocity (r : ℕ) (x : ℝ) := density r x - density r (x-1)

theorem density_deriv (r : ℕ) (x : ℝ) :
    HasDerivAt (density (r+1)) (((r:ℝ)+2)*velocity r x) x :=
  diff_deriv (r+3) _ _ _ (cut_deriv r) x

theorem density_zero (r : ℕ) {x : ℝ} (hx : x ≤ 0) : density r x = 0 := by
  have h (n : ℕ) (t : ℝ) (ht : t ≤ 0) : diff n (cut (r+1)) t = 0 := by
    induction n generalizing t with
    | zero => simp [diff,cut,max_eq_right ht]
    | succ n ih => rw [diff, ih t ht, ih (t-1) (by linarith), sub_zero]
  exact h _ x hx

private theorem tent (x : ℝ) : density 0 x = max x 0 - 2*max (x-1) 0 + max (x-2) 0 := by
  simp [density, diff, cut, show x-1-1=x-2 by ring]
  ring

private theorem velocity_pos_of_shape (r : ℕ)
    (hs : ∀ x, density r (span r-x) = density r x)
    (hm : StrictMonoOn (density r) (Icc 0 (span r/2)))
    {x : ℝ} (hx : 0 < x) (hc : x < (span r+1)/2) : 0 < velocity r x := by
  have hw : 2 ≤ span r := by unfold span; linarith [Nat.cast_nonneg (α:=ℝ) r]
  let y := min x (span r-x)
  have hy : 0 < y := lt_min hx (by linarith)
  have hyc : y ≤ span r/2 := by dsimp [y]; rcases le_total x (span r-x) with h|h <;> simp [*] <;> linarith
  have heq : density r y = density r x := by
    dsimp [y]; rcases le_total x (span r-x) with h|h
    · rw [min_eq_left h]
    · rw [min_eq_right h, hs]
  rw [velocity, ← heq, sub_pos]
  by_cases h : x-1 ≤ 0
  · rw [density_zero _ h, ← density_zero r (le_rfl : (0:ℝ) ≤ 0)]
    exact hm ⟨le_rfl, by linarith⟩ ⟨hy.le,hyc⟩ hy
  · exact hm ⟨by linarith,by linarith⟩ ⟨hy.le,hyc⟩ (lt_min (by linarith) (by linarith))

theorem shape (r : ℕ) :
    (∀ x, density r (span r-x) = density r x) ∧ StrictMonoOn (density r) (Icc 0 (span r/2)) := by
  induction r with
  | zero =>
    constructor
    · intro x; simp only [tent, span, Nat.cast_zero, zero_add]
      grind
    · intro x hx y hy hxy
      simp only [span, Nat.cast_zero, zero_add, Set.mem_Icc] at hx hy
      simp only [tent, max_eq_left hx.1, max_eq_left hy.1,
        max_eq_right (show x-1≤0 by linarith [hx.2]), max_eq_right (show x-2≤0 by linarith [hx.2]),
        max_eq_right (show y-1≤0 by linarith [hy.2]), max_eq_right (show y-2≤0 by linarith [hy.2])]
      linarith
  | succ r ih =>
    obtain ⟨hs, hm⟩ := ih
    have hw : span (r+1) = span r+1 := by simp [span]; ring
    have antisym (x : ℝ) : velocity r (span (r+1)-x) = -velocity r x := by
      unfold velocity
      rw [hw, show span r+1-x=span r-(x-1) by ring, hs,
        show span r-(x-1)-1=span r-x by ring, hs]
      ring
    constructor
    · intro x
      let f := fun y => density (r+1) (span (r+1)-y)-density (r+1) y
      have hd (y : ℝ) : HasDerivAt f 0 y := by
        have h := ((density_deriv r (span (r+1)-y)).comp_const_sub (span (r+1)) y).sub (density_deriv r y)
        rw [antisym] at h
        convert h using 1; ring
      have hc := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x (span (r+1)/2)
      dsimp [f] at hc
      rw [show span (r+1)-span (r+1)/2=span (r+1)/2 by ring, sub_self, sub_eq_zero] at hc
      exact hc
    · apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
      · exact (continuous_iff_continuousAt.mpr fun x => (density_deriv r x).continuousAt).continuousOn
      · intro x hx
        rw [interior_Icc, Set.mem_Ioo, hw] at hx
        rw [(density_deriv r x).deriv]
        exact mul_pos (by positivity) (velocity_pos_of_shape _ hs hm hx.1 hx.2)

theorem velocity_pos (r : ℕ) {x : ℝ} (hx : 0 < x) (hc : x < span (r+1)/2) :
    0 < velocity r x := by
  apply velocity_pos_of_shape _ (shape r).1 (shape r).2 hx
  simpa [span, add_right_comm] using hc

theorem velocity_reflect (r : ℕ) (x : ℝ) :
    velocity r (span (r+1)-x) = -velocity r x := by
  have hw : span (r+1) = span r+1 := by simp [span]; ring
  unfold velocity
  rw [hw, show span r+1-x=span r-(x-1) by ring, (shape r).1,
    show span r-(x-1)-1=span r-x by ring, (shape r).1]
  ring

theorem velocity_center (r : ℕ) : velocity r (span (r+1)/2) = 0 := by
  have h := velocity_reflect r (span (r+1)/2)
  rw [show span (r+1)-span (r+1)/2=span (r+1)/2 by ring] at h
  linarith

theorem velocity_deriv (r : ℕ) (x : ℝ) :
    HasDerivAt (velocity (r+1)) (((r:ℝ)+2)*(velocity r x-velocity r (x-1))) x := by
  rw [mul_sub]
  exact (density_deriv r x).sub ((density_deriv r (x-1)).comp_sub_const x 1)

theorem negative_curvature (r : ℕ) :
    deriv (velocity (r+1)) (span (r+2)/2) < 0 := by
  let c := span (r+2)/2
  have hc : span (r+1)-(c-1)=c := by dsimp [c,span]; push_cast; ring
  have h := velocity_reflect r (c-1)
  rw [hc] at h
  have hp : 0 < velocity r (c-1) := by
    apply velocity_pos <;> dsimp [c,span] <;> push_cast <;> linarith [Nat.cast_nonneg (α:=ℝ) r]
  change deriv _ c < 0
  rw [(velocity_deriv r c).deriv, h]
  exact mul_neg_of_pos_of_neg (by positivity) (by linarith)

/-- Uniform linear lower bound for the unnormalized first-derivative profile. -/
theorem curvature (r : ℕ) : ∃ a : ℝ, 0 < a ∧ ∀ x ∈ Icc (1/2:ℝ) (span (r+2)/2),
    a*(span (r+2)/2-x) ≤ velocity (r+1) x := by
  let c := span (r+2)/2
  let v := velocity (r+1)
  let f := fun x => -dslope v c x
  have hc : 1/2 ≤ c := by dsimp [c,span]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) r]
  have hd (x : ℝ) : DifferentiableAt ℝ v x := (velocity_deriv r x).differentiableAt
  have hcont : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro x
    apply ContinuousAt.neg
    by_cases h : x=c
    · subst x; exact continuousAt_dslope_same.mpr (hd _)
    · exact (continuousAt_dslope_of_ne h).mpr (hd x).continuousAt
  have hv : v c = 0 := velocity_center _
  have heq {x : ℝ} (h : x ≠ c) : f x * (c-x) = v x := by
    dsimp [f]; rw [dslope_of_ne _ h, slope_def_field, hv]
    field_simp [sub_ne_zero.mpr h]; ring
  have hpos (x : ℝ) (hx : x ∈ Icc (1/2:ℝ) c) : 0 < f x := by
    rcases hx.2.lt_or_eq with h | rfl
    · have hvx : 0 < v x := velocity_pos _ (by linarith [hx.1]) h
      have hh := heq h.ne
      exact pos_of_mul_pos_left (hh.symm ▸ hvx) (by linarith)
    · exact neg_pos.mpr (by simpa [dslope_same] using negative_curvature r)
  obtain ⟨y,hy,hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.mpr hc) hcont.continuousOn
  refine ⟨f y,hpos y hy,?_⟩
  intro x hx
  change f y*(c-x) ≤ v x
  rcases hx.2.lt_or_eq with h | h
  · rw [← heq h.ne]
    exact mul_le_mul_of_nonneg_right (hmin hx) (sub_nonneg.mpr h.le)
  · change x=c at h; subst x; simp [hv]

end SZ.Spline
