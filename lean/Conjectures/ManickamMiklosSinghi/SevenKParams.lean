import Mathlib

namespace ManickamMiklosSinghi.SevenK

/-- Uniform bounds on all coefficients of the slice moments, including both
finite-population correction factors. -/
theorem moment_param_bounds (n k p v g w l P : ℝ) (hk : 2 ≤ k) (hn : 5*k ≤ n)
    (hp : p=k/n) (hv : v=(n-k)/(n-1)) (hg : g=(n-2*k)/(n-2))
    (hw : w=(k-1)*(n-k-1)/((n-2)*(n-3))) (hl : 0 ≤ l)
    (hl' : l ≤ p) (hP : p ≤ P) (hP' : P ≤ 1/5) :
    0 < p ∧ 1-p ≤ v ∧ v ≤ 1 ∧ 0 ≤ w ∧ w ≤ P*(1-P) ∧ w ≤ 1/6 ∧
    1-2*P ≤ g ∧ g ≤ (1-2*l)/(1-l) := by
  have hn' : 0 < n := by linarith
  have hn1 : 0 < n-1 := by linarith
  have hn2 : 0 < n-2 := by linarith
  have hn3 : 0 < n-3 := by linarith
  have hpp := (eq_div_iff hn'.ne').1 hp
  have hvv := (eq_div_iff hn1.ne').1 hv
  have hgg := (eq_div_iff hn2.ne').1 hg
  have hww := (eq_div_iff (mul_pos hn2 hn3).ne').1 hw
  have hp0 : 0 < p := by rw [hp]; exact div_pos (by linarith) hn'
  have hp' := hP.trans hP'
  have h0 : 1-p ≤ v := by
    rw [hv,le_div_iff₀ hn1]
    nlinarith only [hpp,hp']
  have hv' : v ≤ 1 := by rw [hv,div_le_iff₀ hn1]; linarith
  have hw' : 0 ≤ w := by
    rw [hw]
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hn2.le hn3.le)
  have hnk : 0 ≤ n-k := by linarith
  have hpz : 0 ≤ n^2/5-k*(n-k) := by
    nlinarith only [mul_nonneg (show 0 ≤ n/5-k by linarith) hn'.le,sq_nonneg k]
  have hwpp : w ≤ p*(1-p) := by
    have hmul := mul_nonneg hpz (show 0 ≤ 5*n-6 by linarith)
    have hcoeff : 0 ≤ n^2*(n-1)-k*(n-k)*(5*n-6) := by
      nlinarith only [hmul,sq_nonneg n]
    have hle : (k-1)*(n-k-1)*n^2 ≤ k*(n-k)*((n-2)*(n-3)) := by
      nlinarith only [hcoeff]
    have he : p*(1-p)*n^2=k*(n-k) := by
      rw [hp]; field_simp [hn'.ne'] <;> ring
    have h1 : w*((n-2)*(n-3))*n^2 ≤ (p*(1-p)*n^2)*((n-2)*(n-3)) := by
      rwa [hww,he]
    have h2 : w*((n-2)*(n-3)*n^2) ≤ (p*(1-p))*((n-2)*(n-3)*n^2) := by
      nlinarith only [h1]
    exact le_of_mul_le_mul_right h2 (by positivity)
  have hwP : w ≤ P*(1-P) := hwpp.trans (by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hP) (show 0 ≤ 1-p-P by linarith)])
  have hw6 : w ≤ 1/6 := by
    nlinarith only [hwP,mul_nonneg (sub_nonneg.mpr hP') (show 0 ≤ 4/5-P by linarith)]
  have hgL : 1-2*P ≤ g := by
    rw [hg,le_div_iff₀ hn2]
    have h := mul_le_mul_of_nonneg_right hP hn'.le
    nlinarith only [h,hpp,hP']
  have hgU : g ≤ (1-2*l)/(1-l) := by
    have hl1 : 0 < 1-l := by linarith
    apply (le_div_iff₀ hl1).2
    have hComp : (n-2*k)*(1-l) ≤ (1-2*l)*(n-2) := by
      have hnK : (2:ℝ) ≤ k := hk
      have h := mul_le_mul_of_nonneg_right hl' hn'.le
      have h₂ := mul_nonneg (show 0 ≤ k-2 by linarith) (show 0 ≤ 1-2*l by linarith)
      nlinarith only [h₂,h,hpp]
    have hmul : (g*(1-l))*(n-2) ≤ (1-2*l)*(n-2) := by
      nlinarith only [hComp, congrArg (fun z : ℝ => z*(1-l)) hgg]
    exact le_of_mul_le_mul_right hmul hn2
  exact ⟨hp0,h0,hv',hw',hwP,hw6,hgL,hgU⟩

end ManickamMiklosSinghi.SevenK
