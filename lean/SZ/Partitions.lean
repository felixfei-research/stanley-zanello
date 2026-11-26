import SZ.Expansion

namespace SZ
open PowerSeries

/-- Each vector gives the multiplicity of each available part 2,...,r+1. -/
def partitionVectors (r n : ℕ) : Finset (Fin r → Fin (n+1)) :=
  Finset.univ.filter fun a => ∑ i : Fin r, (i.val+2)*(a i).val = n

private noncomputable def truncatedCoin (j n : ℕ) : PowerSeries ℤ :=
  ∑ a : Fin (n+1), X^(j*a.val)

private theorem truncatedCoin_coeff (j n d : ℕ) (hj : 0<j) (hd : d≤n) :
    coeff d (truncatedCoin j n) = coeff d (Series.coin j) := by
  simp only [truncatedCoin,map_sum,coeff_X_pow,Series.coeff_coin]
  by_cases h : j ∣ d
  · obtain ⟨a,ha⟩ := h
    have hle : a≤n := by nlinarith
    let z : Fin (n+1) := ⟨a,by omega⟩
    rw [if_pos (show j ∣ d from ⟨a,ha⟩), Finset.sum_eq_single z, if_pos ha]
    · intro b _ hb
      apply if_neg
      intro he
      apply hb
      apply Fin.ext
      exact Nat.eq_of_mul_eq_mul_left hj (he.symm.trans ha)
    · simp
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a _
    exact if_neg (fun he => h ⟨_,he⟩)

private theorem same_product {ι : Type*} (S : Finset ι) (A B : ι → PowerSeries ℤ) (n : ℕ)
    (h : ∀ i ∈ S, ∀ d ≤ n, coeff d (A i) = coeff d (B i)) :
    ∀ d ≤ n, coeff d (∏ i ∈ S, A i) = coeff d (∏ i ∈ S, B i) := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | @insert i S hi ih =>
    intro d hd
    simp only [Finset.prod_insert hi,coeff_mul]
    apply Finset.sum_congr rfl
    intro t ht
    have he := Finset.mem_antidiagonal.mp ht
    rw [h i (by simp) _ (by omega), ih (fun j hj => h j (by simp [hj])) _ (by omega)]

theorem restricted_counts_vectors (r n : ℕ) :
    restricted (r+1) n = (partitionVectors r n).card := by
  classical
  simp only [restricted,Int.natCast_nonneg,if_true,Int.toNat_natCast,Nat.add_sub_cancel,Series.parts]
  rw [← Fin.prod_univ_eq_prod_range]
  rw [← same_product (Finset.univ : Finset (Fin r))
    (fun i => truncatedCoin (i.val+2) n) (fun i => Series.coin (i.val+2)) n
    (fun i _ d hd => truncatedCoin_coeff _ _ _ (by omega) hd) n le_rfl]
  unfold truncatedCoin
  rw [Fintype.prod_sum]
  simp only [map_sum, Finset.prod_pow_eq_pow_sum, coeff_X_pow]
  simp [partitionVectors,eq_comm]

end SZ
