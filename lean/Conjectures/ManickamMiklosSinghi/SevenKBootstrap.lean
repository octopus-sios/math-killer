import Conjectures.ManickamMiklosSinghi.SevenKBound
import Conjectures.ManickamMiklosSinghi.SevenKScalar
import Conjectures.ManickamMiklosSinghi.SevenKStats
namespace ManickamMiklosSinghi.SevenK

/-- Assemble the continuous bootstrapping step, once the finite disjoint
experiment and conditional-variance estimates have supplied their scalar
bounds. This is an implication about empirical measures, not MMSHolds. -/
theorem bootstrap_band {ι α : Type*} (s : Finset ι) (U : Finset α) (j : α) (hj : j ∈ U)
    (μ Y : ι → ℝ) (x : α → ℝ) (b : Band)
    (hrw : b = row1 ∨ b = row2 ∨ b = row3 ∨ b = row4)
    (p v w g R h A bad t m vp vn : ℝ)
    (hp : 0 < p) (hp' : p ≤ b.P) (hv : 1-b.P ≤ v) (hR : R < b.r)
    (hw : 0 ≤ w) (hw' : w ≤ b.W) (hw'' : w ≤ 1/6)
    (hg : b.gLo ≤ g) (hg' : g ≤ b.gHi) (hh : 0 ≤ h)
    (hA : A^2 ≤ 1) (hmin : x j = -h)
    (hlo : ∀ i ∈ U, -h ≤ x i) (hhi : ∀ i ∈ U, x i ≤ A)
    (hs : ∑ i ∈ U, (x i)^2=1) (hμ : ∀ i ∈ s, 0 ≤ μ i)
    (m₁ : ∑ i ∈ s, μ i * Y i = 0)
    (m₂ : ∑ i ∈ s, μ i * (Y i)^2 = p*v)
    (m₃ : ∑ i ∈ s, μ i * (Y i)^3 = p*v*g*(∑ i ∈ U, (x i)^3))
    (m₄ : ∑ i ∈ s, μ i * (Y i)^4 = p*v*(3*w+(1-6*w)*(∑ i ∈ U, (x i)^4)))
    (density : ∑ i ∈ s, μ i*(if 0 ≤ Y i then (1:ℝ) else 0) = p*R)
    (hbad : 0 < bad) (hbad' : bad ≤ 1) (hgap : 0 ≤ bad+b.r-1)
    (ht : 0 ≤ t) (ht' : t ≤ b.T)
    (mix : b.rc ≤ bad+b.r-1+Real.sqrt (t*(1-bad)*(bad+b.r-1)/bad))
    (hvar : bad*(v*A)^2 ≤ (1-bad)*(p*v*(1-A^2)))
    (hm : p*v*h ≤ m) (hcs : m^2 ≤ b.r*p*vp)
    (hn : p*v^2*h^2 ≤ vn) (htot : vp+vn=p*v) : False := by
  obtain ⟨hb,hCells⟩ := rows_certified b hrw
  have hP : b.P < 1 := by linarith only [hb.P_le]
  have hforce := force_bad_density t b.T bad b.beta b.r b.rc b.y b.zeta ht ht'
    hbad hbad' hb.beta_pos hb.beta_lt hb.r_le rfl hb.y_nonneg rfl hgap hb.mono_mix
    hb.strict_mix hb.y_lt mix
  have hpos := positive_cap A b.D p b.P v bad b.beta hb.D_nonneg hb.beta_pos
    hforce.le hbad' hp.le hp' hP hv hA hvar hb.D_cap
  have hneg := negative_cap h b.H p b.P v b.r m vp vn hh hb.H_pos.le hp hP hv
    hb.r_pos hm hcs hn htot hb.H_cap
  obtain ⟨c,hc,hl,hr⟩ := hCells h hh hneg
  let S₃ := ∑ i ∈ U, (x i)^3
  let B := 3*w+(1-6*w)*(∑ i ∈ U, (x i)^4)
  have hscore := capped_score U x j hj b c hb hc w g h hh hl hr hw hw' (by linarith)
    hg hg' hmin hlo (fun i hi => (hhi i hi).trans hpos) hs
  change B+c.lam*g*S₃ ≤ c.I-b.r/((1-b.P)*c.coef) at hscore
  have hc0 : 0 < c.coef := by
    have hz := hc.z_pos
    have hu := hc.u_pos
    dsimp only [Cell.coef]
    positivity
  have hcoef : 0 < (1-b.P)*c.coef := mul_pos (sub_pos.mpr hP) hc0
  have H : b.r/((1-b.P)*c.coef) ≤ c.I-(B+c.lam*g*S₃) := by linarith only [hscore]
  have HI := (div_le_iff₀ hcoef).mp H
  have HI' : 0 ≤ c.I-(B+c.lam*g*S₃) :=
    (div_nonneg hb.r_pos.le hcoef.le).trans H
  have hminor := moment_minorant s μ Y c hc.z_pos hc.u_pos.le p v g B S₃ R hμ hp
    m₁ m₂ m₃ m₄ density
  have hmon := mul_le_mul_of_nonneg_right hv (mul_nonneg hc0.le HI')
  nlinarith only [HI,hminor,hmon,hR]

end ManickamMiklosSinghi.SevenK
