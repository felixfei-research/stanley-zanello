import SZ.Main
import Mathlib.Algebra.Polynomial.Degree.Lemmas

noncomputable section
namespace SZ
open Polynomial

/-- The usual upper/lower-index notation, extended by zero if the lower index is too large. -/
def qChoose (a b : ℕ) : ℤ[X] := if b ≤ a then gaussian b (a-b) else 0

theorem good_actual_degree {P : ℤ[X]} {N : ℕ} (hN : P.natDegree ≤ N) :
    Good N P ↔ (∀ i, 0 ≤ P.coeff i) ∧ Unimodal P.natDegree P := by
  constructor
  · rintro ⟨hn,p,hp,hu,hd⟩
    constructor
    · intro i
      by_cases h : i ≤ N
      · exact hn i h
      · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    · refine ⟨min p P.natDegree,min_le_right ..,?_,?_⟩
      · intro i hi j hj hij
        exact hu ⟨hi.1,hi.2.trans (min_le_left ..)⟩ ⟨hj.1,hj.2.trans (min_le_left ..)⟩ hij
      · intro i hi j hj hij
        obtain ⟨hi1,hi2⟩ := hi
        obtain ⟨hj1,hj2⟩ := hj
        by_cases h : p ≤ P.natDegree
        · rw [min_eq_left h] at hi1 hj1
          exact hd ⟨hi1,hi2.trans hN⟩ ⟨hj1,hj2.trans hN⟩ hij
        · rw [min_eq_right (by omega : P.natDegree ≤ p)] at hi1
          have : i=j := by omega
          rw [this]
  · rintro ⟨hn,p,hp,hu,hd⟩
    refine ⟨fun i _ => hn i,p,hp.trans hN,hu,?_⟩
    intro i hi j hj hij
    by_cases h : j ≤ P.natDegree
    · exact hd ⟨hi.1,hij.trans h⟩ ⟨hj.1,h⟩ hij
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact hn i

theorem actual_degree_le {k ell t s : ℕ} (ha : Aligned k ell t s) :
    (difference k ell t s).natDegree ≤ k*ell := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  have h := difference_reflect ha (i:ℤ)
  rw [atZ_nat, atZ, if_neg (by exact_mod_cast (by omega : ¬ 0 ≤ ((k*ell:ℕ):ℤ)-i))] at h
  exact h

/-- Conjecture 1.1(iv) with integer parameters, the printed exponent, every coefficient,
and unimodality through the actual degree of the difference polynomial. -/
theorem original_conjecture (k : ℤ) (hk : 5 ≤ k) :
    ∃ M : ℕ, ∀ m b : ℤ, (M:ℤ) ≤ m → k ≤ m → k-2 ≤ b →
    (k-2)*b ≤ k*m-4*k+4 → 2 ∣ k*(m-b) →
    let P := qChoose m.toNat k.toNat -
      X^(k*(m-b)/2+b-2*k+2).toNat * qChoose b.toNat (k-2).toNat
    ((∀ i, 0 ≤ P.coeff i) ∧ Unimodal P.natDegree P ↔ (k-2)*b ≠ k*m-4*k+2) := by
  lift k to ℕ using (by omega)
  have hk' : 5 ≤ k := by exact_mod_cast hk
  obtain ⟨M,hM⟩ := stanley_zanello k hk'
  refine ⟨M,?_⟩
  intro m b hw hm hb hmax hp
  have ha : Admissible k m b := ⟨hm,hb,hmax,hp⟩
  obtain ⟨hal,_⟩ := original_to_rectangle hk' ha
  have hdeg : (originalPolynomial k m b).natDegree ≤ k*(m-k).toNat := actual_degree_le hal
  have h := (good_actual_degree hdeg).symm.trans (hM m b hw ha)
  have hpoly : qChoose m.toNat (k:ℤ).toNat -
      X^((k:ℤ)*(m-b)/2+b-2*k+2).toNat * qChoose b.toNat ((k:ℤ)-2).toNat =
      originalPolynomial k m b := by
    simp only [Int.toNat_natCast, qChoose, originalPolynomial, exponent]
    rw [if_pos (by omega),if_pos (by omega)]
    rw [show m.toNat-k=(m-k).toNat by omega,
      show ((k:ℤ)-2).toNat=k-2 by omega,
      show b.toNat-(k-2)=(b-((k:ℤ)-2)).toNat by omega]
  exact hpoly ▸ h

end SZ
