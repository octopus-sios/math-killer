import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

set_option maxHeartbeats 90000

namespace ManickamMiklosSinghi.SevenK

/-- The discriminant step in the initial 69/100 estimate. -/
theorem density_start_scalar (a w s R v B : ℝ)
    (ha : 0 < a) (hs : 0 ≤ s) (hw : 0 ≤ w) (hw' : w ≤ 1/6)
    (hv : 4/5 ≤ v) (hr : R = v*s)
    (hB : B ≤ 3*w + (1-6*w)*(s*a))
    (hm : a^3 + (1-a)^3 ≤ a*s*B) : 69/100 < R := by
  let z := 1/a
  have h₁ : (1:ℝ) ≤ (3+3*w*s)*a + ((1-6*w)*s^2-3)*a^2 := by
    have hh := mul_le_mul_of_nonneg_left hB (mul_nonneg ha.le hs)
    nlinarith only [hm,hh]
  have haz : a*z=1 := by dsimp [z]; field_simp [ha.ne']
  have h₂ : z^2 ≤ (3+3*w*s)*z + ((1-6*w)*s^2-3) := by
    have hh := mul_le_mul_of_nonneg_right h₁ (sq_nonneg z)
    calc
      z^2 = 1*z^2 := by ring
      _ ≤ _ := hh
      _ = _ := by linear_combination ( (3+3*w*s)*z + ((1-6*w)*s^2-3)*(a*z+1))*haz
  have disc : 3/4 ≤ (1-6*w+(9/4)*w^2)*s^2+(9/2)*w*s := by
    nlinarith only [sq_nonneg (2*z-(3+3*w*s)), h₂]
  have hs' : 69/80 < s := by
    by_contra! h
    have hc : 0 ≤ 1-6*w+(9/4)*w^2 := by nlinarith only [hw', sq_nonneg w]
    have hsq : s^2 ≤ (69/80:ℝ)^2 := pow_le_pow_left₀ hs h 2
    have hA := mul_le_mul_of_nonneg_left hsq hc
    have hB' := mul_le_mul_of_nonneg_left h (show 0 ≤ (9/2:ℝ)*w by positivity)
    have hC := mul_nonneg hw (sub_nonneg.mpr hw')
    have hup : w ≤ 1/6 := hw'
    -- At this s, even the secant majorant in w is below 3/4.
    nlinarith only [disc,hA,hB',hC,hw,hup]
  rw [hr]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hv) hs,hs']

/-- From the disjoint-pair probability estimate, obtain the scalar requirement
on the conditional bad density. Here j is the joint probability. -/
theorem mixing_to_gap (t b e r rc j : ℝ) (ht : 0 < t) (hb : 0 < b)
    (hb1 : b ≤ 1) (he : 0 ≤ e) (he1 : e ≤ 1)
    (he' : e ≤ t*(b+r-1))
    (hjlo : b*t*rc ≤ j)
    (hjhi : j ≤ b*e + t*Real.sqrt (b*(1-b)*e*(1-e))) :
    rc ≤ b+r-1 + Real.sqrt (t*(1-b)*(b+r-1)/b) := by
  have hy : 0 ≤ b+r-1 := nonneg_of_mul_nonneg_right (he.trans he') ht
  have hbn := sub_nonneg.mpr hb1
  have hen := sub_nonneg.mpr he1
  have hx : 0 ≤ t*(1-b)*(b+r-1)/b := by positivity
  have hprod : 0 ≤ b*(1-b)*e*(1-e) := by positivity
  have h1 : b*(1-b)*e*(1-e) ≤ b*(1-b)*e := by
    nlinarith only [mul_nonneg (mul_nonneg (mul_nonneg hb.le hbn) he) he]
  have h2 := mul_le_mul_of_nonneg_left he' (mul_nonneg hb.le hbn)
  have hs : Real.sqrt (b*(1-b)*e*(1-e)) ≤ b*Real.sqrt (t*(1-b)*(b+r-1)/b) := by
    have hh : b^2*(t*(1-b)*(b+r-1)/b) = b*(1-b)*(t*(b+r-1)) := by
      field_simp [hb.ne']
    have heq := Real.sq_sqrt hx
    have hq := Real.sq_sqrt hprod
    have hmul := congrArg (fun z : ℝ => b^2*z) heq
    have hqle : (Real.sqrt (b*(1-b)*e*(1-e)))^2 ≤
        (b*Real.sqrt (t*(1-b)*(b+r-1)/b))^2 := by
      nlinarith only [h1,h2,hmul,hq,hh]
    exact le_of_sq_le_sq hqle (by positivity)
  have h3 := mul_le_mul_of_nonneg_left hs ht.le
  have h4 := mul_le_mul_of_nonneg_left he' hb.le
  have hh : (b*t)*rc ≤ (b*t)*(b+r-1+Real.sqrt (t*(1-b)*(b+r-1)/b)) := by nlinarith only [hjlo,hjhi,h3,h4]
  exact le_of_mul_le_mul_left hh (by positivity)

/-- A monotonicity certificate for eq. (5), avoiding calculus or square-root
derivatives. For d=β−b≥0, (sqrt(C*(1−β))+d)^2 dominates C*(1−b). -/
theorem force_bad_density (t T b β r rc y ζ : ℝ)
    (ht : 0 ≤ t) (ht' : t ≤ T)
    (hb : 0 < b) (hb' : b ≤ 1) (hβ : 0 < β) (hβ' : β < 1)
    (hr : r ≤ 1) (hy : y = β+r-1) (hy' : 0 ≤ y) (hz : ζ = y/β)
    (hgap : 0 ≤ b+r-1) (hcert : T*ζ ≤ 4*(1-β))
    (hstrict : T*(1-β)*ζ < (rc-y)^2) (hrc : y < rc)
    (hmix : rc ≤ b+r-1 + Real.sqrt (t*(1-b)*(b+r-1)/b)) : β < b := by
  by_contra! hf
  have hT := ht.trans ht'
  have hζ : 0 ≤ ζ := by rw [hz]; positivity
  have hc : 0 ≤ T*ζ := mul_nonneg hT hζ
  have hd : 0 ≤ β-b := sub_nonneg.mpr hf
  have hbn := sub_nonneg.mpr hb'
  have hβn : 0 ≤ 1-β := by linarith
  have hratio : (b+r-1)/b ≤ ζ := by
    rw [hz, div_le_div_iff₀ hb hβ, hy]
    nlinarith only [mul_nonneg hd (sub_nonneg.mpr hr)]
  have hr0 : 0 ≤ (b+r-1)/b := div_nonneg hgap hb.le
  have hmul := mul_le_mul ht' hratio hr0 hT
  have hmul' := mul_le_mul_of_nonneg_right hmul hbn
  have hlow : t*(1-b)*(b+r-1)/b ≤ (T*ζ)*(1-b) := by
    convert hmul' using 1; ring
  let q := Real.sqrt ((T*ζ)*(1-β))
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q^2=(T*ζ)*(1-β) := Real.sq_sqrt (mul_nonneg hc hβn)
  have hcle : T*ζ ≤ 2*q := by
    apply le_of_sq_le_sq _ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_right hcert hc,hq2]
  have hsle : Real.sqrt (t*(1-b)*(b+r-1)/b) ≤ q + (β-b) := by
    have hArg : 0 ≤ t*(1-b)*(b+r-1)/b := by positivity
    apply le_of_sq_le_sq _ (add_nonneg hq hd)
    nlinarith only [Real.sq_sqrt hArg,hlow,hq2,sq_nonneg (β-b),
      mul_le_mul_of_nonneg_right hcle hd]
  have hrc' : rc-y ≤ q := by linarith only [hy,hmix,hsle]
  have hf' := mul_nonneg (sub_nonneg.mpr hrc') (show 0 ≤ q+(rc-y) by linarith only [hq,hrc])
  nlinarith only [hf',hq2,hstrict]

end ManickamMiklosSinghi.SevenK
