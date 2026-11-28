import Conjectures.ManickamMiklosSinghi.SevenKCells
import Conjectures.ManickamMiklosSinghi.SevenKQuartic
namespace ManickamMiklosSinghi.SevenK

private theorem quad_bound (a b t A B C : ℝ) (ha : a ≤ t) (hb : t ≤ b) (hA : 0 ≤ A) :
    A*t^2+B*t+C ≤ max (A*a^2+B*a+C) (A*b^2+B*b+C) := by
  by_cases hh : A*(t+a)+B ≤ 0
  · apply le_trans _ (le_max_left _ _)
    nlinarith only [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ha) hh]
  · apply le_trans _ (le_max_right _ _)
    have hs : 0 ≤ A*(t+b)+B := by
      nlinarith only [lt_of_not_ge hh,mul_nonneg hA (sub_nonneg.mpr (ha.trans hb))]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hb) hs]

/-- Retain the mass of one distinguished atom while bounding every other score
by the larger of the two endpoint scores. -/
private theorem sum_with_atom {ι : Type*} (s : Finset ι) (w f : ι → ℝ) (j : ι) (hj : j ∈ s)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hn : ∑ i ∈ s, w i = 1)
    (L U C : ℝ) (hf : f j ≤ L) (hg : ∀ i ∈ s, f i ≤ max L U)
    (hL : L ≤ C) (hU : w j * L + (1-w j)*U ≤ C) :
    ∑ i ∈ s, w i * f i ≤ C := by
  classical
  rcases le_total U L with hh | hh
  · calc
      _ ≤ ∑ i ∈ s, w i * L := Finset.sum_le_sum (fun i hi =>
        mul_le_mul_of_nonneg_left ((hg i hi).trans (max_eq_left hh).le) (hw i hi))
      _ = L := by rw [← Finset.sum_mul, hn, one_mul]
      _ ≤ _ := hL
  · have he := Finset.add_sum_erase s w hj
    have he' : ∑ i ∈ s.erase j, w i = 1-w j := by linarith only [hn,he]
    calc
      _ = w j * f j + ∑ i ∈ s.erase j, w i * f i :=
        (Finset.add_sum_erase s (fun i => w i * f i) hj).symm
      _ ≤ w j * L + ∑ i ∈ s.erase j, w i * U := by
        apply add_le_add (mul_le_mul_of_nonneg_left hf (hw j hj))
        apply Finset.sum_le_sum
        intro i hi
        have his := Finset.mem_of_mem_erase hi
        exact mul_le_mul_of_nonneg_left ((hg i his).trans (max_eq_right hh).le) (hw i his)
      _ = w j * L + (1-w j)*U := by rw [← Finset.sum_mul,he']
      _ ≤ _ := hU

/-- Continuous coordinate-to-moment bound, eq. (9), using the two polynomial
certificates supplied by a cell and one attaining minimum. -/
theorem capped_score {ι : Type*} (s : Finset ι) (x : ι → ℝ) (j : ι) (hj : j ∈ s)
    (b : Band) (c : Cell) (hb : b.Admissible) (hc : c.Admissible b)
    (w g h : ℝ) (hh : 0 ≤ h) (hl : c.left ≤ h) (hr : h ≤ c.right)
    (hw : 0 ≤ w) (hwW : w ≤ b.W) (hw6 : 0 ≤ 1-6*w)
    (hgL : b.gLo ≤ g) (hgU : g ≤ b.gHi)
    (hmin : x j = -h) (hlo : ∀ i ∈ s, -h ≤ x i) (hhi : ∀ i ∈ s, x i ≤ b.D)
    (hs : ∑ i ∈ s, (x i)^2 = 1) :
    3*w+(1-6*w)*(∑ i ∈ s, (x i)^4)+c.lam*g*(∑ i ∈ s, (x i)^3) ≤ c.threshold b := by
  let f := fun t : ℝ => (1-6*w)*t^2 + (c.lam*g)*t + 3*w
  let θ := if 0 ≤ 3-6*h^2 then b.W else 0
  have hθ : w*(3-6*h^2) ≤ θ*(3-6*h^2) := by
    dsimp only [θ]
    split_ifs with hθ
    · exact mul_le_mul_of_nonneg_right hwW hθ
    · exact mul_le_mul_of_nonpos_right hw (le_of_lt (lt_of_not_ge hθ))
  have hbds : c.Bounds b θ := by
    dsimp only [θ]
    split_ifs <;> first | exact hc.W_bound | exact hc.zero_bound
  let L := 3*θ+(1-6*θ)*h^2-c.lam*b.gLo*h
  have hn : f (-h) ≤ L := by
    have hlg := mul_le_mul_of_nonneg_right hgL (mul_nonneg hc.lam_nonneg hh)
    dsimp [f,L]
    nlinarith only [hθ,hlg]
  have hp : f b.D ≤ c.plus b := by
    have hdr : 0 ≤ 3-6*b.D^2 := by linarith only [hb.D_sq]
    have hw' := mul_le_mul_of_nonneg_right hwW hdr
    have hg' := mul_le_mul_of_nonneg_right hgU (mul_nonneg hc.lam_nonneg hb.D_nonneg)
    dsimp [f,Cell.plus]
    nlinarith only [hw',hg']
  have hf (i) (hi : i ∈ s) : f (x i) ≤ max L (c.plus b) :=
    (quad_bound (-h) b.D (x i) _ _ _ (hlo i hi) (hhi i hi) hw6).trans
      (max_le_max hn hp)
  have hL : L ≤ c.threshold b := by
    have hz := hbds.1 h hl hr
    dsimp [L]
    nlinarith only [hz]
  have hU : (x j)^2*L + (1-(x j)^2)*c.plus b ≤ c.threshold b := by
    have hz := hbds.2 h hl hr
    rw [hmin]
    dsimp [L]
    nlinarith only [hz]
  have hatom := sum_with_atom s (fun i => x i ^2) (fun i => f (x i)) j hj
    (fun i _ => sq_nonneg _) hs L (c.plus b) (c.threshold b) (by simpa only [hmin] using hn) hf hL hU
  have hsum : ∑ i ∈ s, (x i)^2*f (x i) =
        3*w*(∑ i ∈ s, (x i)^2)+(1-6*w)*(∑ i ∈ s, (x i)^4)+c.lam*g*(∑ i ∈ s, (x i)^3) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f]
    ring
  rw [hsum,hs,mul_one] at hatom
  exact hatom

/-- The quartic expectation inequality, uniformly for any finite distribution
represented by nonnegative weights. The moment identities here are inputs. -/
theorem moment_minorant {ι : Type*} (s : Finset ι) (w Y : ι → ℝ)
    (c : Cell) (hz : 0 < c.z) (hu : 0 ≤ c.u) (p v g B S₃ R : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hp : 0 < p)
    (m₁ : ∑ i ∈ s, w i * Y i = 0)
    (m₂ : ∑ i ∈ s, w i * (Y i)^2 = p*v)
    (m₃ : ∑ i ∈ s, w i * (Y i)^3 = p*v*g*S₃)
    (m₄ : ∑ i ∈ s, w i * (Y i)^4 = p*v*B)
    (hR : ∑ i ∈ s, w i * (if 0 ≤ Y i then (1:ℝ) else 0) = p*R) :
    c.coef*v*(c.I-(B+c.lam*g*S₃)) ≤ R := by
  have he : ∑ i ∈ s, w i * (c.coef*Y i*(Y i+c.u)^2*(c.d-Y i)) =
      c.coef*(c.u^2*c.d*(∑ i ∈ s, w i * Y i) +
      c.I*(∑ i ∈ s, w i * (Y i)^2)-c.lam*(∑ i ∈ s, w i * (Y i)^3)-
      (∑ i ∈ s, w i * (Y i)^4)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Cell.I,Cell.lam]
    ring
  have hh : ∑ i ∈ s, w i * (c.coef*Y i*(Y i+c.u)^2*(c.d-Y i)) ≤ p*R := by
    rw [← hR]
    exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left
      (quartic_minorant c.z c.u (Y i) hz hu) (hw i hi))
  rw [he,m₁,m₂,m₃,m₄] at hh
  have hf : p*(c.coef*v*(c.I-(B+c.lam*g*S₃))) ≤ p*R := by nlinarith only [hh]
  exact le_of_mul_le_mul_left hf hp

end ManickamMiklosSinghi.SevenK
