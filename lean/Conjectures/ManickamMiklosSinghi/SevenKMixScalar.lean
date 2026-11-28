import Mathlib

namespace ManickamMiklosSinghi.SevenK

/-- Algebraic local-to-global step for sequentially revealing the avoided set.
V j is the average residual variance after j distinct excluded points. The last
step is allowed to land exactly at m−a=b. -/
theorem variance_chain (m b : ℝ) (a : ℕ) (V : ℕ → ℝ) (hb : 0 < b)
    (hab : (a:ℝ)+b ≤ m) (hmb : b < m)
    (hstep : ∀ j : ℕ, j < a →
      ((m-j)*(m-j-b-1)/((m-j-1)*(m-j-b)))*V j ≤ V (j+1)) :
    (m*(m-a-b)/((m-a)*(m-b)))*V 0 ≤ V a := by
  have H : ∀ j : ℕ, j ≤ a → (m*(m-j-b)/((m-j)*(m-b)))*V 0 ≤ V j := by
    intro j
    induction j with
    | zero =>
      intro _
      have hm : m ≠ 0 := by linarith
      have h₀ : m-b ≠ 0 := by linarith
      simp [hm,h₀]
    | succ j ih =>
      intro hj
      have hja : j<a := by omega
      have hj' : (j:ℝ)+1 ≤ a := by exact_mod_cast hj
      have h1 : 0 < m-(j:ℝ)-1 := by linarith
      have h2 : 0 < m-(j:ℝ)-b := by linarith
      have h3 : 0 < m-(j:ℝ) := by linarith
      have h4 : 0 ≤ m-(j:ℝ)-b-1 := by linarith
      let q := (m-j)*(m-j-b-1)/((m-j-1)*(m-j-b))
      have hq : 0 ≤ q := by dsimp [q]; positivity
      have heq : m*(m-(j+1:ℕ)-b)/((m-(j+1:ℕ))*(m-b)) =
          q*(m*(m-j-b)/((m-j)*(m-b))) := by
        push_cast
        have h5 : m-((j:ℝ)+1) ≠ 0 := by linarith
        dsimp [q]
        field_simp [h1.ne',h2.ne',h3.ne',h5,sub_ne_zero.mpr hmb.ne'] <;> ring
      rw [heq,mul_assoc]
      exact (mul_le_mul_of_nonneg_left (ih hja.le) hq).trans (hstep j hja)
  exact H a (le_refl _)

/-- Applying ordinary covariance Cauchy–Schwarz after the residual variance
loss yields the one-sided disjoint mixing inequality. -/
theorem covariance_mix (j b e ρ ve : ℝ) (hρ : 0 ≤ ρ)
    (hb : 0 ≤ b*(1-b)) (he : 0 ≤ e*(1-e))
    (hcs : (j-b*e)^2 ≤ b*(1-b)*ve)
    (hvar : ve ≤ ρ^2*(e*(1-e))) :
    j ≤ b*e+ρ*Real.sqrt (b*(1-b)*e*(1-e)) := by
  have hs : 0 ≤ b*(1-b)*e*(1-e) := by simpa only [mul_assoc] using mul_nonneg hb he
  have hmul := mul_le_mul_of_nonneg_left hvar hb
  have heq := congrArg (fun x : ℝ => ρ^2*x) (Real.sq_sqrt hs)
  have hh : (j-b*e)^2 ≤ (ρ*Real.sqrt (b*(1-b)*e*(1-e)))^2 := by
    nlinarith only [heq,hcs,hmul]
  have hle := le_of_sq_le_sq hh (mul_nonneg hρ (Real.sqrt_nonneg _))
  linarith

end ManickamMiklosSinghi.SevenK
