import Conjectures.ManickamMiklosSinghi.SevenKMomentWeights
namespace ManickamMiklosSinghi.SevenK

theorem singleton_count {n k : ℕ} (hk : 0 < k) (hn : k ≤ n) :
    Cnt n k 1 = ((n-1).choose (k-1):ℝ) := by
  have H := Nat.choose_symm (show n-k ≤ n-1 by omega)
  rw [show n-1-(n-k)=k-1 by omega] at H
  unfold Cnt
  exact_mod_cast H.symm

/-- Conditional first-moment coefficient and domination of both coefficients
in the second moment. All inequalities also hold for k=2. -/
theorem star_weights {n k : ℕ} (hk : 2 ≤ k) (hn : 2*k ≤ n) :
    let d := Cnt n k
    let p := (k:ℝ)/n
    let v := ((n:ℝ)-k)/(n-1)
    d 1 = (n.choose k:ℝ)*p ∧ d 1-d 2 = d 1*v ∧
    d 1-2*d 2+d 3 ≤ d 1*v^2 ∧ d 2-d 3 ≤ d 1*(p*v) := by
  dsimp only
  let d := Cnt n k
  let q := ((k:ℝ)-1)/(n-1)
  let q' := ((k:ℝ)-2)/(n-2)
  let p := (k:ℝ)/n
  let v := ((n:ℝ)-k)/(n-1)
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hn' : 2*(k:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have h1 : 0 < (n:ℝ)-1 := by linarith
  have h2 : 0 < (n:ℝ)-2 := by linarith
  have hq : 0 ≤ q := div_nonneg (by linarith) h1.le
  have hq' : q' ≤ q := by
    apply (div_le_div_iff₀ h2 h1).2
    nlinarith only [hn',hk']
  have hv : 0 ≤ v := div_nonneg (by linarith) h1.le
  have hvq : 1-q = v := by unfold q v; field_simp; ring
  have hvq' : 1-q' = ((n:ℝ)-k)/(n-2) := by unfold q'; field_simp; ring
  have hqv : q*(1-q') ≤ p*v := calc
    _ = (((k:ℝ)-1)/(n-2))*v := by rw [hvq']; unfold q v; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right ((div_le_div_iff₀ h2 hn0).2 (by nlinarith only [hn'])) hv
  have hd : 0 ≤ d 1 := Nat.cast_nonneg _
  have kn : k ≤ n := by omega
  have h₁ := cnt_step (j:=0) kn (by omega)
  have h₂ := cnt_step (j:=1) kn (by omega)
  have h₃ := cnt_step (j:=2) kn (by omega)
  norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,sub_zero,Nat.reduceAdd] at h₁ h₂ h₃
  have h0 : Cnt n k 0 = (n.choose k:ℝ) := by simp [Cnt,Nat.choose_symm kn]
  rw [h0] at h₁
  have e₂ : d 2 = d 1*q := by unfold d q; rw [(eq_div_iff h1.ne').2 h₂]; ring
  have e₃ : d 3 = d 2*q' := by unfold d q'; rw [(eq_div_iff h2.ne').2 h₃]; ring
  change d 1 = _*p ∧ d 1-d 2 = d 1*v ∧ d 1-2*d 2+d 3 ≤ d 1*v^2 ∧ d 2-d 3 ≤ d 1*(p*v)
  refine ⟨?_,?_,?_,?_⟩
  · unfold p d; rw [(eq_div_iff hn0.ne').2 h₁]; ring
  · rw [e₂,← hvq]; ring
  · rw [e₃,e₂,← hvq]
    nlinarith only [mul_le_mul_of_nonneg_left hq' (mul_nonneg hd hq)]
  · rw [e₃,e₂]
    nlinarith only [mul_le_mul_of_nonneg_left hqv hd]

end ManickamMiklosSinghi.SevenK
