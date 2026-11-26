import SZ.Uniform

noncomputable section
namespace SZ
open PowerSeries Spline

def residual (k : ℕ) (v : ℤ) : ℝ :=
  normalizer k*(restricted k v:ℝ) - cut (k-2) ((v:ℝ)+halfSum k)

def RankEstimate (p : ℕ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ v : ℤ,
  |residual (p+5) v| ≤ C*(1+max (v:ℝ) 0)^(p+1)

theorem restricted_step (r n : ℕ) :
    restricted (r+2) n - restricted (r+2) ((n:ℤ)-(r+2:ℕ)) = restricted (r+1) n := by
  have h : (1-X^(r+2))*Series.parts (r+1) = Series.parts r := by
    rw [Series.parts_succ, mul_left_comm, Series.cancel_coin (by omega), mul_one]
  have he := congrArg (coeff (R:=ℤ) n) h
  simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul'] at he
  by_cases hn : r+2 ≤ n
  · rw [if_pos hn] at he
    rw [← Nat.cast_sub hn]
    simpa [restricted] using he
  · rw [if_neg hn] at he
    have hneg : ¬ 0 ≤ (n:ℤ)-(r+2:ℕ) := by omega
    simpa only [restricted, if_neg hneg, sub_zero, Nat.add_sub_cancel, Int.natCast_nonneg,
      if_true, Int.toNat_natCast] using he

private theorem central_power (p : ℕ) (h : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 0 ≤ z →
    |(z+h)^(p+3)-(z-h)^(p+3)-2*((p:ℝ)+3)*h*z^(p+2)| ≤ C*(1+z)^p := by
  let b := fun i : ℕ => (h^i-(-h)^i)*((p+3).choose i : ℝ)
  let C := ∑ i ∈ Finset.range (p+1), |b (3+i)|
  refine ⟨C,Finset.sum_nonneg (fun _ _ => abs_nonneg _),?_⟩
  intro z hz
  have expand : (z+h)^(p+3)-(z-h)^(p+3) =
      ∑ i ∈ Finset.range (p+3+1), b i*z^(p+3-i) := by
    rw [add_comm z h, sub_eq_add_neg z h, add_comm z (-h), add_pow, add_pow, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _; dsimp [b]; ring
  rw [expand, show p+3+1=3+(p+1) by omega, Finset.sum_range_add]
  have low : (∑ i ∈ Finset.range 3, b i*z^(p+3-i)) = 2*((p:ℝ)+3)*h*z^(p+2) := by
    simp [Finset.sum_range_succ, b, show p+3-1=p+2 by omega]
    ring_nf
    simp
  rw [low, add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ Finset.range (p+1), |b (3+i)*z^(p+3-(3+i))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (p+1), |b (3+i)| *(1+z)^p := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_pow, abs_of_nonneg hz]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ hz (show z≤1+z by linarith) _).trans
        (pow_le_pow_right₀ (by linarith) (by omega))
    _ = _ := (Finset.sum_mul ..).symm

theorem residual_negative (k : ℕ) (hk : 5 ≤ k) {v : ℤ} (hv : v < 0) :
    |residual k v| ≤ (halfSum k)^(k-2) := by
  have hk' : (5:ℝ) ≤ k := by exact_mod_cast hk
  have hc : 0 ≤ halfSum k := by unfold halfSum; nlinarith [sq_nonneg (k:ℝ)]
  have hv' : (v:ℝ) < 0 := by exact_mod_cast hv
  simp only [residual, restricted, if_neg (by omega : ¬ 0 ≤ v), Int.cast_zero, mul_zero, zero_sub,
    abs_neg, cut, abs_pow, abs_of_nonneg (le_max_right ((v:ℝ)+halfSum k) 0)]
  exact pow_le_pow_left₀ (le_max_right ((v:ℝ)+halfSum k) 0) (max_le (by linarith) hc) _

private theorem accumulate (g : ℤ → ℝ) (j d : ℕ) (hj : 0 < j) (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hneg : ∀ z < 0, |g z| ≤ B)
    (hstep : ∀ n : ℕ, |g n-g ((n:ℤ)-j)| ≤ C*(1+(n:ℝ))^d) :
    ∀ z : ℤ, |g z| ≤ (B+C)*(1+max (z:ℝ) 0)^(d+1) := by
  intro z
  by_cases h : z < 0
  · have hz : (z:ℝ) < 0 := by exact_mod_cast h
    simp [max_eq_right hz.le]; linarith [hneg z h]
  lift z to ℕ using (by omega)
  have hZ (n : ℕ) (hn : n ≤ z) : |g n| ≤ B+((n:ℝ)+1)*(C*(1+(z:ℝ))^d) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      let M := C*(1+(z:ℝ))^d
      have hp : 0 ≤ M := by dsimp [M]; positivity
      have step : |g n - g ((n:ℤ)-j)| ≤ M := (hstep n).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.add_le_add_left hn 1) _) hC)
      have prev : |g ((n:ℤ)-j)| ≤ B+(n:ℝ)*M := by
        by_cases hnj : j ≤ n
        · rw [← Nat.cast_sub hnj]
          have h' := ih (n-j) (by omega) (by omega)
          have hn' : ((n-j:ℕ):ℝ)+1 ≤ n := by exact_mod_cast (by omega : n-j+1≤n)
          exact h'.trans (by dsimp [M] at *; nlinarith [mul_le_mul_of_nonneg_right hn' hp])
        · exact (hneg _ (by omega)).trans (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hp))
      have ha := abs_add_le (g n-g ((n:ℤ)-j)) (g ((n:ℤ)-j))
      rw [sub_add_cancel] at ha
      change |g n| ≤ B+((n:ℝ)+1)*M
      linarith
  have hn := hZ z le_rfl
  simp only [Int.cast_natCast, max_eq_left (Nat.cast_nonneg (α:=ℝ) z)]
  have hb := mul_le_mul_of_nonneg_left (one_le_pow₀ (n:=d+1) (by linarith [Nat.cast_nonneg (α:=ℝ) z] : 1 ≤ 1+(z:ℝ))) hB
  rw [pow_succ] at hb ⊢
  linarith

theorem rank_step (p : ℕ) (hr : RankEstimate p) : RankEstimate (p+1) := by
  let k := p+5
  let j := p+6
  let h := (j:ℝ)/2
  let q := ((j:ℝ)*((p:ℝ)+4))
  have qpos : 0 ≤ q := by dsimp [q]; positivity
  have hk' : (5:ℝ) ≤ k := by dsimp [k]; push_cast; linarith [Nat.cast_nonneg (α:=ℝ) p]
  have hc : h ≤ halfSum k := by dsimp [h,j,halfSum,k]; push_cast; nlinarith [sq_nonneg (p:ℝ),Nat.cast_nonneg (α:=ℝ) p]
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hs : halfSum j=halfSum k+h := by dsimp [halfSum,j,k,h]; push_cast; ring
  have hK : normalizer j=q*normalizer k := by
    dsimp only [j,q,k,normalizer]
    simp only [show p+6-2=p+4 by omega,show p+5-2=p+3 by omega,
      Nat.factorial_succ (p+5),Nat.factorial_succ (p+3)]
    push_cast; ring
  obtain ⟨C,hC,hr'⟩ := hr
  obtain ⟨E,hE,hpow⟩ := central_power (p+1) h
  let B := (halfSum j)^(p+4)
  let A := q*C + E*(1+halfSum k)^(p+1)
  have hB : 0 ≤ B := by dsimp [B]; rw [hs]; exact pow_nonneg (by linarith) _
  have hA : 0 ≤ A := by dsimp [A]; exact add_nonneg (mul_nonneg qpos hC) (mul_nonneg hE (pow_nonneg (by linarith) _))
  refine ⟨B+A,add_nonneg hB hA,?_⟩
  apply accumulate (residual j) j (p+1) (by dsimp [j]; omega) B A hB hA
  · intro v hv
    simpa only [j, show p+6-2=p+4 by omega] using residual_negative j (by dsimp [j];omega) hv
  · intro n
    let z := (n:ℝ)+halfSum k
    have hn := Nat.cast_nonneg (α:=ℝ) n
    have hz : 0 ≤ z := by dsimp [z]; linarith
    have hlarge := hpow z hz
    have hu := hr' (n:ℤ)
    change |residual k n| ≤ _ at hu
    simp only [Int.cast_natCast,max_eq_left hn] at hu
    have hrec := restricted_step (p+4) n
    have hrec' : (restricted j n:ℝ)-(restricted j ((n:ℤ)-j):ℝ) = restricted k n := by exact_mod_cast hrec
    let R := (z+h)^(p+4)-(z-h)^(p+4)-q*z^(p+3)
    have hR : |R| ≤ E*(1+halfSum k)^(p+1)*(1+(n:ℝ))^(p+1) := by
      have hq : 2*((p+1:ℕ)+3:ℝ)*h=q := by dsimp [q,h]; push_cast; ring
      rw [hq] at hlarge
      apply le_trans hlarge
      rw [mul_assoc, ← mul_pow]
      apply mul_le_mul_of_nonneg_left _ hE
      apply pow_le_pow_left₀ (by linarith)
      dsimp [z]
      nlinarith [mul_nonneg hn (show 0≤halfSum k by linarith)]
    have hid : residual j n-residual j ((n:ℤ)-j) = q*residual k n-R := by
      unfold residual cut R
      rw [hs,hK]
      simp only [Int.cast_natCast, Int.cast_sub]
      rw [show (n:ℝ)+(halfSum k+h)=z+h by dsimp [z];ring,
        show (n:ℝ)-j+(halfSum k+h)=z-h by dsimp [z,h];ring]
      rw [max_eq_left (show 0≤z+h by linarith),max_eq_left (show 0≤z-h by dsimp [z];linarith),
        max_eq_left hz]
      rw [← hrec']
      simp only [show j-2=p+4 by dsimp [j];omega, show k-2=p+3 by dsimp [k];omega]
      ring
    rw [hid]
    have ht := abs_sub (q*residual k n) R
    rw [abs_mul,abs_of_nonneg qpos] at ht
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_left hu qpos]

end SZ
