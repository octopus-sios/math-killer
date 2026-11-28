import Conjectures.ManickamMiklosSinghi.SevenKFullMoments
namespace ManickamMiklosSinghi.SevenK

theorem cnt_step {n k j : ℕ} (hk : k ≤ n) (hj : j < n) :
    Cnt n k (j+1)*((n:ℝ)-j) = Cnt n k j*((k:ℝ)-j) := by
  by_cases h : j ≤ k
  · have h1 : n-(j+1)+1=n-j := by omega
    have h2 : n-j-(n-k)=k-j := by omega
    have H := Nat.choose_mul_succ_eq (n-(j+1)) (n-k)
    rw [h1,h2] at H
    have H' : (((n-(j+1)).choose (n-k) : ℕ) : ℝ) * ((n-j : ℕ):ℝ) =
        (((n-j).choose (n-k) : ℕ):ℝ)*((k-j : ℕ):ℝ) := by exact_mod_cast H
    simpa only [Cnt,Nat.cast_sub hj.le,Nat.cast_sub h] using H'
  · have ha : n-(j+1) < n-k := by omega
    have hb : n-j < n-k := by omega
    simp [Cnt,Nat.choose_eq_zero_of_lt ha,Nat.choose_eq_zero_of_lt hb]

theorem moment_weights {n k : ℕ} (hk : k ≤ n) (hn : 4 ≤ n) :
    let d := Cnt n k
    let p := (k:ℝ)/n
    let v := ((n:ℝ)-k)/(n-1)
    let g := ((n:ℝ)-2*k)/(n-2)
    let w := ((k:ℝ)-1)*((n:ℝ)-k-1)/(((n:ℝ)-2)*(n-3))
    d 1-d 2 = d 0*p*v ∧ d 1-3*d 2+2*d 3=d 0*p*v*g ∧
    d 2-2*d 3+d 4=d 0*p*v*w ∧ d 1-7*d 2+12*d 3-6*d 4=d 0*p*v*(1-6*w) := by
  dsimp only
  have hn' : (4:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  have hn2 : (n:ℝ)-2 ≠ 0 := by linarith
  have hn3 : (n:ℝ)-3 ≠ 0 := by linarith
  have h₁ := cnt_step (j:=0) hk (by omega)
  have h₂ := cnt_step (j:=1) hk (by omega)
  have h₃ := cnt_step (j:=2) hk (by omega)
  have h₄ := cnt_step (j:=3) hk (by omega)
  norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,sub_zero,Nat.reduceAdd] at h₁ h₂ h₃ h₄
  have e₁ := (eq_div_iff hn0).2 h₁
  have e₂ := (eq_div_iff hn1).2 h₂
  have e₃ := (eq_div_iff hn2).2 h₃
  have e₄ := (eq_div_iff hn3).2 h₄
  rw [e₄,e₃,e₂,e₁]
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp [hn0,hn1,hn2,hn3] <;> ring

end ManickamMiklosSinghi.SevenK
