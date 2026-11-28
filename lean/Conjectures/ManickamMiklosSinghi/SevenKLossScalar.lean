import Conjectures.ManickamMiklosSinghi.SevenKMomentWeights
namespace ManickamMiklosSinghi.SevenK
/-- The two counts in one reveal, including the boundary b=m-1. -/
theorem loss_counts (m b : ℕ) (hb : 0 < b) (hm : b < m) :
    let D : ℝ := m.choose b
    let L : ℝ := (m-1).choose b
    let C := Cnt m b 1 - Cnt m b 2
    L*(m:ℝ)=D*((m:ℝ)-b) ∧ C*((m:ℝ)-1)=L*b := by
  dsimp only
  have hm' : (0:ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hp := Nat.choose_mul_succ_eq (m-1) b
  rw [Nat.sub_add_cancel (show 1 ≤ m by omega)] at hp
  have hL : (((m-1).choose b : ℕ):ℝ)*m = (m.choose b:ℝ)*((m:ℝ)-b) := by
    rw [← Nat.cast_sub hm.le]
    exact_mod_cast hp
  have h₁ := cnt_step (j:=0) hm.le (by omega)
  have h₂ := cnt_step (j:=1) hm.le (by omega)
  norm_num only [Nat.cast_zero,Nat.cast_one,Nat.reduceAdd,sub_zero] at h₁ h₂
  have h0 : Cnt m b 0 = (m.choose b:ℝ) := by simp [Cnt,Nat.choose_symm hm.le]
  rw [h0] at h₁
  refine ⟨hL,?_⟩
  calc
    _ = Cnt m b 1 * ((m:ℝ)-b) := by linarith only [h₂]
    _ = _ := by
      apply mul_right_cancel₀ hm'.ne'
      linear_combination ((m:ℝ)-b)*h₁ - (b:ℝ)*hL

theorem excluded_mean_scalar (m b D L C Q V : ℝ)
    (hm : 1 < m) (hb : b < m) (hL : 0 < L) (hc : L*m = D*(m-b))
    (hd : C*(m-1)=L*b) (H : Q ≤ (V*D)*C) :
    (m*(m-b-1)/((m-1)*(m-b)))*V ≤ V-Q/L^2/m := by
  have h1 : 0 < m-1 := by linarith
  have h2 : 0 < m-b := by linarith
  have hm' : 0 < m := by linarith
  have he : Q/L^2/m ≤ ((V*D)*C)/L^2/m :=
    div_le_div_of_nonneg_right (div_le_div_of_nonneg_right H (sq_nonneg L)) hm'.le
  apply le_trans _ (sub_le_sub_left he V)
  apply le_of_eq
  rw [(eq_div_iff h2.ne').2 hc.symm,(eq_div_iff h1.ne').2 hd]
  field_simp [h1.ne',h2.ne',hL.ne',hm'.ne']
  ring

end ManickamMiklosSinghi.SevenK
