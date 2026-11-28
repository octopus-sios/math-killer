import Conjectures.ManickamMiklosSinghi.SevenKChain
namespace ManickamMiklosSinghi.SevenK
open Finset

def BitOn {ι : Type*} (s : Finset ι) (f : ι → ℝ) := ∀ i ∈ s, f i = 0 ∨ f i = 1

theorem bit_mean {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {f : ι → ℝ} (hf : BitOn s f) :
    0 ≤ av s f ∧ av s f ≤ 1 ∧ variance s f = av s f*(1-av s f) := by
  have h0 : ∀ i ∈ s, 0 ≤ f i := fun i hi => by rcases hf i hi with h|h <;> rw [h] <;> norm_num
  have h1 : ∀ i ∈ s, f i ≤ 1 := fun i hi => by rcases hf i hi with h|h <;> rw [h] <;> norm_num
  refine ⟨(av_const hs 0) ▸ av_mono h0,(av_const hs 1) ▸ av_mono h1,?_⟩
  have hsq : av s (fun i => (f i)^2) = av s f := av_congr (fun i hi => by
    rcases hf i hi with h|h <;> rw [h] <;> norm_num)
  rw [variance,hsq]
  ring

theorem covariance_cs {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) :
    (av s (fun i => f i*g i)-av s f*av s g)^2 ≤ variance s f*variance s g := by
  have hc := av_cs s (fun i => f i-av s f) (fun i => g i-av s g)
  rw [av_centered_sq hs,av_centered_sq hs] at hc
  have he : av s (fun i => (f i-av s f)*(g i-av s g)) =
      av s (fun i => f i*g i)-av s f*av s g := by
    have h := av_congr (s:=s) (f:=fun i => (f i-av s f)*(g i-av s g))
      (g:=fun i => ((f i*g i-av s f*g i)-av s g*f i)-(-(av s f*av s g)))
      (fun i _ => by ring)
    rw [h,av_sub,av_sub,av_sub,av_scale,av_scale,av_const hs]
    ring
  rwa [he] at hc

variable {α : Type*} [DecidableEq α]

/-- Disjoint mixing with any upper bound on the correlation coefficient. -/
theorem disjoint_mixing (U : Finset α) (a b : ℕ) (hb : 0 < b) (hb' : b < U.card)
    (hab : a+b ≤ U.card) (F G : Finset α → ℝ)
    (hF : BitOn (U.powersetCard a) F) (hG : BitOn (U.powersetCard b) G)
    (t : ℝ) (ht : 0 ≤ t)
    (ht' : (a:ℝ)*b/(((U.card:ℝ)-a)*(U.card-b)) ≤ t^2) :
    let K := U.powersetCard a
    let B := av K F
    let e := av (U.powersetCard b) G
    av K (fun A => F A * av ((U \ A).powersetCard b) G) ≤
    B*e + t*Real.sqrt (B*(1-B)*e*(1-e)) := by
  let K := U.powersetCard a
  let D := U.powersetCard b
  let Z := fun A => av ((U \ A).powersetCard b) G
  have hK := slice_ne U (show a ≤ U.card by omega)
  obtain ⟨hb0,hb1,hB⟩ := bit_mean hK hF
  obtain ⟨he0,he1,hE⟩ := bit_mean (slice_ne U hb'.le) hG
  have hs : av K Z = av D G := av_disjoint U a b hab G
  have hc := covariance_cs K hK F Z
  rw [hs,hB] at hc
  have hvar := disjoint_variance U a b hb hb' hab G
  dsimp only at hvar
  rw [hE] at hvar
  have hnn := mul_nonneg he0 (sub_nonneg.mpr he1)
  exact covariance_mix _ _ _ t (variance K Z) ht (mul_nonneg hb0 (sub_nonneg.mpr hb1)) hnn hc
    (hvar.trans (mul_le_mul_of_nonneg_right ht' hnn))

end ManickamMiklosSinghi.SevenK
