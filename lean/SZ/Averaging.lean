import SZ.Spline
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

noncomputable section
namespace SZ.Spline
open Set
open scoped BigOperators

def offset {k : ℕ} (i : Fin k) : ℝ := (i.val:ℝ)+1-((k:ℝ)+1)/2
def eps {k : ℕ} (J : Finset (Fin k)) : ℝ := ∑ i ∈ J, offset i

theorem offset_rev {k : ℕ} (i : Fin k) : offset i.rev = -offset i := by
  unfold offset
  simp only [Fin.val_rev]
  push_cast [Nat.cast_sub (by omega : i.val+1 ≤ k)]
  ring

theorem centered_sum (k : ℕ) (f : ℕ → ℝ) :
    ∑ J : Finset (Fin k), f J.card * eps J = 0 := by
  let e := (Fin.revPerm (n:=k)).finsetCongr
  have h (J : Finset (Fin k)) : f (e J).card * eps (e J) = -(f J.card * eps J) := by
    simp [e, eps, Equiv.finsetCongr_apply, Finset.sum_map, offset_rev]
  have eq := Equiv.sum_comp e (fun J : Finset (Fin k) => f J.card * eps J)
  simp_rw [h] at eq
  rw [Finset.sum_neg_distrib] at eq
  linarith

theorem diff_subsets {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ℝ → ℝ) (x : ℝ) :
    diff s.card f x = ∑ J ∈ s.powerset, (-1:ℝ)^J.card*f (x-(J.card:ℝ)) := by
  induction s using Finset.induction generalizing x with
  | empty => simp [diff]
  | @insert i s hi ih =>
    rw [Finset.card_insert_of_notMem hi, diff, ih, ih, Finset.sum_powerset_insert hi]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro J hJ
    rw [Finset.card_insert_of_notMem (Finset.notMem_mono (Finset.mem_powerset.mp hJ) hi),
      Nat.cast_succ, pow_succ, show x-((J.card:ℝ)+1)=x-1-J.card by ring]
    ring

/-- Perturb all the arguments in a cardinality class simultaneously. -/
def path (k p : ℕ) (x u : ℝ) : ℝ :=
  ∑ J : Finset (Fin k), (-1:ℝ)^J.card * cut p (x-J.card-u*eps J)

theorem path_zero (k p : ℕ) (x : ℝ) : path k p x 0 = diff k (cut p) x := by
  simpa [path] using (diff_subsets (Finset.univ : Finset (Fin k)) (cut p) x).symm

private def pathD (k p : ℕ) (x u : ℝ) : ℝ :=
  ∑ J : Finset (Fin k), ((-1:ℝ)^J.card * (-(p:ℝ)*eps J)) * cut (p-1) (x-J.card-u*eps J)
private def pathDD (k p : ℕ) (x u : ℝ) : ℝ :=
  ∑ J : Finset (Fin k), ((-1:ℝ)^J.card * ((p:ℝ)*(p-1)*(eps J)^2)) * cut (p-2) (x-J.card-u*eps J)

private theorem deriv_arg {k : ℕ} (p : ℕ) (x u : ℝ) (J : Finset (Fin k)) :
    HasDerivAt (fun t => cut (p+2) (x-J.card-t*eps J))
      ((((p:ℝ)+2)*cut (p+1) (x-J.card-u*eps J)) * (-eps J)) u := by
  apply (cut_deriv p _).comp u
    (show HasDerivAt (fun t : ℝ => x-J.card-t*eps J) (-eps J) u by
      simpa using ((hasDerivAt_id' u).mul_const (eps J)).const_sub (x-J.card))

private theorem path_deriv (k p : ℕ) (x u : ℝ) :
    HasDerivAt (path k (p+2) x) (pathD k (p+2) x u) u := by
  apply HasDerivAt.fun_sum
  intro J _
  convert (deriv_arg p x u J).const_mul ((-1:ℝ)^J.card) using 1
  simp only [Nat.cast_add, Nat.cast_ofNat, show p+2-1=p+1 by omega]
  ring

private theorem pathD_deriv (k p : ℕ) (x u : ℝ) :
    HasDerivAt (pathD k (p+3) x) (pathDD k (p+3) x u) u := by
  apply HasDerivAt.fun_sum
  intro J _
  convert (deriv_arg p x u J).const_mul (((-1:ℝ)^J.card)*(-((p+3:ℕ):ℝ)*eps J)) using 1
  simp only [show p+3-2=p+1 by omega, Nat.cast_add, Nat.cast_ofNat]
  ring

private theorem pathD_zero (k p : ℕ) (x : ℝ) : pathD k p x 0 = 0 := by
  have h := centered_sum k (fun j => (-1:ℝ)^j * (-(p:ℝ)) * cut (p-1) (x-j))
  unfold pathD
  simpa only [zero_mul, sub_zero, mul_assoc, mul_left_comm, mul_comm] using h

set_option maxHeartbeats 1000000 in
/-- A compact set of (x,u) bounds the second derivative uniformly over moving x. -/
theorem path_quadratic (k p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0:ℝ) k, ∀ u ∈ Icc (0:ℝ) 1,
    |path k (p+3) x u - diff k (cut (p+3)) x| ≤ C*u^2 := by
  let K := (Icc (0:ℝ) k) ×ˢ (Icc (0:ℝ) 1)
  let H := fun z : ℝ × ℝ => |pathDD k (p+3) z.1 z.2|
  have hcont : Continuous H := by unfold H pathDD cut; fun_prop
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have h0 : (0,0) ∈ K := ⟨⟨le_rfl, by positivity⟩,⟨le_rfl,zero_le_one⟩⟩
  obtain ⟨z,hz,hmax⟩ := hK.exists_isMaxOn ⟨_,h0⟩ hcont.continuousOn
  have hC : 0 ≤ H z := abs_nonneg _
  refine ⟨_,hC,?_⟩
  intro x hx u hu
  have hD (v : ℝ) (hv : v ∈ Icc 0 u) : |pathD k (p+3) x v| ≤ H z*v := by
    have h := norm_image_sub_le_of_norm_deriv_le_segment' (a:=0) (b:=u) (C:=H z) (f:=pathD k (p+3) x) (f':=pathDD k (p+3) x)
      (fun t _ => (pathD_deriv k p x t).hasDerivWithinAt)
      (fun t ht => (show ‖pathDD k (p+3) x t‖ ≤ H z from by
        rw [Real.norm_eq_abs]; exact hmax (show (x,t) ∈ K from ⟨hx,ht.1,ht.2.le.trans hu.2⟩))) v hv
    simpa [Real.norm_eq_abs, pathD_zero] using h
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (a:=0) (b:=u) (C:=H z*u) (f:=path k (p+3) x) (f':=pathD k (p+3) x)
    (fun t _ => (path_deriv k (p+1) x t).hasDerivWithinAt)
    (fun t ht => (show ‖pathD k (p+3) x t‖ ≤ H z*u from by
      rw [Real.norm_eq_abs]; exact (hD t ⟨ht.1,ht.2.le⟩).trans (mul_le_mul_of_nonneg_left ht.2.le hC))) u ⟨hu.1,le_rfl⟩
  simpa [Real.norm_eq_abs, path_zero, pow_two, mul_assoc] using h

end SZ.Spline
