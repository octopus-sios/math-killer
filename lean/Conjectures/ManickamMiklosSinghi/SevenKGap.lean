import Conjectures.ManickamMiklosSinghi.SevenKMix
import Conjectures.ManickamMiklosSinghi.SevenKScalar
namespace ManickamMiklosSinghi.SevenK
open Finset

theorem star_rho {n k : ℕ} (hk : 2 ≤ k) (hn : 2*k+1 ≤ n) :
    (((k-1:ℕ):ℝ)*k)/((((n-1:ℕ):ℝ)-(k-1:ℕ))*(((n-1:ℕ):ℝ)-k)) ≤
      ((k:ℝ)/((n:ℝ)-k))^2 := by
  have hk' : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hn' : 2*(k:ℝ)+1 ≤ n := by exact_mod_cast hn
  have hd : 0 < (n:ℝ)-k := by linarith
  have he : 0 < (n:ℝ)-1-k := by linarith
  have h : ((k:ℝ)-1)/((n:ℝ)-1-k) ≤ (k:ℝ)/((n:ℝ)-k) := by
    apply (div_le_div_iff₀ he hd).2
    nlinarith only [hn']
  simp only [Nat.cast_sub (show 1 ≤ k by omega),Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one]
  rw [show (n:ℝ)-1-((k:ℝ)-1)=(n:ℝ)-k by ring]
  calc
    _ = (k/((n:ℝ)-k))*(((k:ℝ)-1)/((n:ℝ)-1-k)) := by field_simp [hd.ne', he.ne']
    _ ≤ _ := by simpa only [pow_two] using mul_le_mul_of_nonneg_left h (div_nonneg (Nat.cast_nonneg k) hd.le)

/-- Combine disjoint mixing with a lower density valid in every bad
complement. No assumption here that a bad star already has positive mass. -/
theorem gap_from_complement {α : Type*} [DecidableEq α] (U : Finset α) (n k : ℕ)
    (hU : U.card=n-1) (hk : 2 ≤ k) (hn : 2*k+1 ≤ n)
    (F G : Finset α → ℝ) (hF : BitOn (U.powersetCard (k-1)) F) (hG : BitOn (U.powersetCard k) G)
    (p t R r rc : ℝ) (hp : 0 < p) (hp' : p < 1) (ht : t=(k:ℝ)/((n:ℝ)-k))
    (hpt : (1-p)*t=p) (hr : R < r) (hr' : r ≤ 1)
    (H : ∀ T ∈ U.powersetCard (k-1), F T=1 → t*rc ≤ av ((U \ T).powersetCard k) G)
    (split : p*R = p*(1-av (U.powersetCard (k-1)) F)+(1-p)*av (U.powersetCard k) G) :
    let b := av (U.powersetCard (k-1)) F
    0 < b ∧ b ≤ 1 ∧ 0 ≤ b+r-1 ∧ rc ≤ b+r-1 + Real.sqrt (t*(1-b)*(b+r-1)/b) := by
  let K := U.powersetCard (k-1)
  let b := av K F
  let e := av (U.powersetCard k) G
  let j := av K (fun T => F T * av ((U \ T).powersetCard k) G)
  have hab : k-1+k ≤ U.card := by omega
  have hb' : k < U.card := by omega
  have hden := sub_pos.mpr hp'
  have ht0 : 0 < t := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos hden.le h
    linarith only [this,hpt,hp]
  obtain ⟨_,hb1,_⟩ := bit_mean (slice_ne U (by omega)) hF
  obtain ⟨he0,he1,_⟩ := bit_mean (slice_ne U hb'.le) hG
  have he : e < t*(b+r-1) := by
    have h : (1-p)*e = (1-p)*(t*(b+R-1)) := by
      rw [← mul_assoc,hpt]
      change p*R=p*(1-b)+(1-p)*e at split
      linarith only [split]
    rw [mul_left_cancel₀ hden.ne' h]
    exact mul_lt_mul_of_pos_left (by linarith only [hr]) ht0
  have hgap : 0 < b+r-1 := by
    by_contra! h
    have := mul_nonpos_of_nonneg_of_nonpos ht0.le h
    linarith only [this,he,he0]
  have hb : 0 < b := by linarith only [hgap,hr']
  have hlo : b*t*rc ≤ j := calc
    _ = av K (fun T => (t*rc)*F T) := by rw [av_scale]; dsimp [b]; ring
    _ ≤ _ := by
      apply av_mono
      intro T hT
      rcases hF T hT with hh|hh
      · rw [hh,mul_zero,zero_mul]
      · simpa only [hh,mul_one,one_mul] using H T hT hh
  have hup := disjoint_mixing U (k-1) k (by omega) hb' hab F G hF hG t ht0.le
    (by rw [hU,ht]; exact star_rho hk hn)
  exact ⟨hb,hb1,hgap.le,mixing_to_gap t b e r rc j ht0 hb hb1 he0 he1 he.le hlo hup⟩

end ManickamMiklosSinghi.SevenK
