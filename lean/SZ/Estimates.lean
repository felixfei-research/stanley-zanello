import SZ.Main

namespace SZ

theorem uniform_first_differences : UniformEstimate := uniform_of_restricted restricted_estimate

/-- Corollary 3.3, stated separately with the positive constant uniform in the index. -/
theorem bulk_lower_bound (p : ℕ) :
    let k := p+5
    ∃ γ : ℝ, 0 < γ ∧ ∃ W : ℕ, ∀ ell n : ℕ, W ≤ ell → ell ≤ n → n ≤ k*ell/2 →
      γ*(widthScale k ell)^(p+2) ≤ (delta (gaussian k ell) n : ℝ) :=
  bulk_lower_of_uniform uniform_first_differences p

end SZ
