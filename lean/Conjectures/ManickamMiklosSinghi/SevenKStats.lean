import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ManickamMiklosSinghi.SevenK

variable {ι : Type*}

noncomputable def positive (y : ℝ) := max y 0
noncomputable def negative (y : ℝ) := max (-y) 0
noncomputable def nonnegInd (y : ℝ) : ℝ := if 0 ≤ y then 1 else 0

/-- Cauchy–Schwarz with the positive support of the random variable as one
factor. No strict-positivity or continuity assumption on the distribution. -/
theorem sign_cs (s : Finset ι) (w Y : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * positive (Y i))^2 ≤
    (∑ i ∈ s, w i * nonnegInd (Y i))*(∑ i ∈ s, w i * positive (Y i)^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
  · intro i hi
    apply mul_nonneg (hw i hi)
    dsimp only [nonnegInd]
    split_ifs <;> norm_num
  · exact fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)
  · intro i hi
    by_cases h : 0 ≤ Y i
    · simp only [positive,max_eq_left h,nonnegInd,ite_eq_left h,mul_one]
      apply le_of_eq
      ring
    · simp [positive,max_eq_right (lt_of_not_ge h).le,nonnegInd,h]

theorem parts_mean (s : Finset ι) (w Y : ι → ℝ)
    (hm : ∑ i ∈ s, w i * Y i = 0) :
    (∑ i ∈ s, w i * positive (Y i)) = ∑ i ∈ s, w i * negative (Y i) := by
  apply sub_eq_zero.mp
  rw [← hm,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [positive,negative]
  rcases le_total 0 (Y i) with h | h
  · rw [max_eq_left h,max_eq_right (neg_nonpos.mpr h)]; ring
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h)]; ring

theorem parts_even (s : Finset ι) (w Y : ι → ℝ) (m : ℕ) (hm : 0 < m) :
    (∑ i ∈ s, w i * positive (Y i)^(2*m)) + (∑ i ∈ s, w i * negative (Y i)^(2*m))
    = ∑ i ∈ s, w i * (Y i)^(2*m) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hnm : 2*m ≠ 0 := by omega
  dsimp only [positive,negative]
  rcases le_total 0 (Y i) with h | h
  · simp only [max_eq_left h,max_eq_right (neg_nonpos.mpr h),zero_pow hnm,mul_zero,add_zero]
  · rw [max_eq_right h,max_eq_left (neg_nonneg.mpr h),zero_pow hnm,mul_zero,zero_add]
    simp [pow_mul]

/-- Finite one-sided Chebyshev inequality in its denominator-free form. -/
theorem cantelli (s : Finset ι) (w Y : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (μ b V : ℝ) (hμ : 0 ≤ μ)
    (hmean : ∑ i ∈ s, w i * Y i = μ)
    (hgood : ∑ i ∈ s, w i * nonnegInd (Y i) = 1-b)
    (h₂ : ∑ i ∈ s, w i * (Y i)^2 = V+μ^2) :
    b*μ^2 ≤ (1-b)*V := by
  let m := ∑ i ∈ s, w i * positive (Y i)
  have hmp : μ ≤ m := by
    rw [← hmean]
    exact Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (le_max_left _ _) (hw i hi)
  have hmq : μ^2 ≤ m^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hmp) (add_nonneg (hμ.trans hmp) hμ)]
  have hV : (∑ i ∈ s, w i * positive (Y i)^2) ≤ V+μ^2 := by
    rw [← h₂]
    apply Finset.sum_le_sum
    intro i hi
    apply mul_le_mul_of_nonneg_left _ (hw i hi)
    rcases le_total 0 (Y i) with h | h
    · simp [positive,max_eq_left h]
    · simpa [positive,max_eq_right h] using sq_nonneg (Y i)
  have hbn : 0 ≤ 1-b := by
    rw [← hgood]
    apply Finset.sum_nonneg
    intro i hi
    dsimp only [nonnegInd]
    split_ifs <;> simp [hw i hi]
  have hc := sign_cs s w Y hw
  rw [hgood] at hc
  change m^2 ≤ _ at hc
  nlinarith only [hmq,hc,mul_le_mul_of_nonneg_left hV hbn]

theorem positive_cap (A D p P v b β : ℝ)
    (hD : 0 ≤ D) (hβ : 0 < β) (hb : β ≤ b) (hb' : b ≤ 1) (hp : 0 ≤ p)
    (hp' : p ≤ P) (hP : P < 1) (hv : 1-P ≤ v) (hA : A^2 ≤ 1)
    (hc : b*(v*A)^2 ≤ (1-b)*(p*v*(1-A^2)))
    (hd : P*(1-β) ≤ D^2*((1-P)*β+P*(1-β))) : A ≤ D := by
  have hv' : 0 < v := by linarith
  have hβ' : 0 ≤ 1-β := by linarith
  have hbn := sub_nonneg.mpr hb'
  have hP' := hp.trans hp'
  have hpos : 0 < (1-P)*β+P*(1-β) := by
    have := mul_pos (sub_pos.mpr hP) hβ
    linarith only [this, mul_nonneg hP' hβ']
  have h1 : b*v*A^2 ≤ (1-b)*p*(1-A^2) := by
    have hh : (b*v*A^2)*v ≤ ((1-b)*p*(1-A^2))*v := by nlinarith only [hc]
    exact le_of_mul_le_mul_right hh hv'
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul hb hv (sub_nonneg.mpr hP.le)
    (hβ.le.trans hb)) (sq_nonneg A)
  have h3 := mul_le_mul_of_nonneg_right (mul_le_mul
    (show 1-b ≤ 1-β by linarith) hp' hp hβ') (sub_nonneg.mpr hA)
  apply le_of_sq_le_sq _ hD
  have h4 : A^2*((1-P)*β+P*(1-β)) ≤ D^2*((1-P)*β+P*(1-β)) := by
    nlinarith only [h1,h2,h3,hd]
  exact le_of_mul_le_mul_right h4 hpos

theorem negative_cap (h H p P v r m vp vn : ℝ)
    (hh : 0 ≤ h) (hH : 0 ≤ H) (hp : 0 < p) (hP : P < 1) (hv : 1-P ≤ v)
    (hr : 0 < r) (hm : p*v*h ≤ m) (hcs : m^2 ≤ r*p*vp)
    (hn : p*v^2*h^2 ≤ vn) (ht : vp+vn=p*v)
    (hcert : r ≤ H^2*(1-P)*(1+r)) : h ≤ H := by
  have hv' : 0 < v := by linarith
  have hm' : 0 ≤ p*v*h := by positivity
  have hs : (p*v*h)^2 ≤ m^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hm) (add_nonneg (hm'.trans hm) hm')]
  have hc : (p*p*v)*(v*(1+r)*h^2) ≤ (p*p*v)*r := by
    nlinarith only [hs,hcs,mul_le_mul_of_nonneg_left hn (mul_nonneg hr.le hp.le),
      congrArg (fun z : ℝ => r*p*z) ht]
  have hf := le_of_mul_le_mul_left hc (mul_pos (mul_pos hp hp) hv')
  have hcoef : 0 < (1-P)*(1+r) := mul_pos (sub_pos.mpr hP) (by linarith)
  have hscaled : h^2*((1-P)*(1+r)) ≤ H^2*((1-P)*(1+r)) := by
    nlinarith only [hf,hcert,mul_le_mul_of_nonneg_right hv
      (mul_nonneg (show 0 ≤ 1+r by linarith) (sq_nonneg h))]
  exact le_of_sq_le_sq (le_of_mul_le_mul_right hscaled hcoef) hH

end ManickamMiklosSinghi.SevenK
