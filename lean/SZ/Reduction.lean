import SZ.Comparison

namespace SZ

/-- A sufficient single-rectangle estimate in the bulk, independent of s and t. -/
def BulkComparison : Prop :=
  ∀ k : ℕ, 5 ≤ k → ∃ W : ℕ, ∀ ell n : ℕ, W ≤ ell → ell ≤ n → n ≤ k*ell/2 →
    (2:ℤ)^(k-2)*((n:ℤ)+1)^(k-4) ≤ delta (gaussian k ell) n

theorem conjecture_of_bulk (bulk : BulkComparison) : Conjecture11iv := by
  apply formulations_equivalent.mpr
  intro k hk
  obtain ⟨W,hW⟩ := bulk k hk
  refine ⟨W, ?_⟩
  intro ell t s hw ha
  constructor
  · rintro hg rfl
    exact exception_not_unimodal hk ha hg.2
  · intro hs
    apply good_of_left (fun i hi => diff_symm_nat ha hi)
    intro n hn
    by_cases he : n ≤ ell
    · exact edge hk ha hs he
    rw [delta_shift_sub, sub_nonneg]
    have hbig := hW ell n hw (by omega) hn
    apply le_trans _ hbig
    by_cases hsn : n < s
    · rw [delta_negative _ (by omega)]
      positivity
    rw [← Nat.cast_sub (by omega : s ≤ n)]
    have hh := small_bound (k-4) t (n-s)
    rw [show k-4+2=k-2 by omega] at hh
    exact (le_abs_self _).trans (hh.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.sub_le n s)) _)
      (by positivity)))

end SZ
