import Conjectures.ManickamMiklosSinghi.SevenKStarWeights
import Conjectures.ManickamMiklosSinghi.SevenKExposure
import Conjectures.ManickamMiklosSinghi.SevenKMean
namespace ManickamMiklosSinghi.SevenK
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem star_partition (i : α) (a : ℕ) (f : Finset α → ℝ) :
    let U := (univ : Finset α).erase i
    (∑ T ∈ U.powersetCard a, f (insert i T)) +
      (∑ D ∈ U.powersetCard (a+1), f D) = ∑ S ∈ univ.powersetCard (a+1), f S := by
  dsimp only
  rw [sum_insert_slice _ i a (mem_univ _) f,powersetCard_erase_eq]
  simp only [sum_filter,← sum_add_distrib]
  exact sum_congr rfl fun S _ => by by_cases h : i ∈ S <;> simp [h]

theorem star_split (k : ℕ) (hk : 2 ≤ k) (hn : 2*k ≤ Fintype.card α) (i : α) (f : Finset α → ℝ) :
    let p := (k:ℝ)/Fintype.card α
    let U := (univ : Finset α).erase i
    av (univ.powersetCard k) f =
      p*av (U.powersetCard (k-1)) (fun T => f (insert i T)) + (1-p)*av (U.powersetCard k) f := by
  let n := Fintype.card α
  let U := (univ : Finset α).erase i
  let L : ℝ := (U.powersetCard (k-1)).card
  let W : ℝ := (U.powersetCard k).card
  let D : ℝ := ((univ : Finset α).powersetCard k).card
  let p := (k:ℝ)/n
  have hU : U.card=n-1 := by dsimp only [U,n]; rw [card_erase_of_mem (mem_univ _),card_univ]
  have hs (g : Finset α → ℝ) := star_partition i (k-1) g
  simp only [Nat.sub_add_cancel (show 1 ≤ k by omega)] at hs
  have hL : 0 < L := by
    apply Nat.cast_pos.mpr
    exact card_pos.mpr (slice_ne _ (by rw [hU]; dsimp only [n]; omega))
  have hW : 0 < W := by
    apply Nat.cast_pos.mpr
    exact card_pos.mpr (slice_ne _ (by rw [hU]; dsimp only [n]; omega))
  have hD : 0 < D := by
    apply Nat.cast_pos.mpr
    exact card_pos.mpr (slice_ne _ (by rw [card_univ]; omega))
  have hm := hs (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,mul_one] at hm
  change L+W=D at hm
  have hcnt : L=D*p := by
    dsimp [L,D]
    rw [card_powersetCard,hU,card_powersetCard,card_univ,← singleton_count (by omega) (show k ≤ n by dsimp only [n]; omega)]
    exact (star_weights hk hn).1
  have he : p=L/D := (eq_div_iff hD.ne').2 (by linarith only [hcnt])
  have he' : 1-p=W/D := (eq_div_iff hD.ne').2 (by linarith only [hcnt,hm])
  dsimp only
  unfold av
  change (∑ S ∈ univ.powersetCard k,f S)/D = p*((∑ T ∈ U.powersetCard (k-1),f (insert i T))/L)+(1-p)*((∑ D ∈ U.powersetCard k,f D)/W)
  rw [← hs f,he',he,add_div]
  field_simp [hD.ne',hL.ne',hW.ne'] <;> ring

theorem star_raw (i : α) (k j : ℕ) (hk : 0 < k) (hkn : k ≤ Fintype.card α) (x : α → ℝ) :
    av (((univ : Finset α).erase i).powersetCard (k-1)) (fun T => (∑ l ∈ insert i T,x l)^j) =
      raw k x j {i}/Cnt (Fintype.card α) k 1 := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [av,card_powersetCard,card_erase_of_mem (mem_univ _),card_univ,singleton_count hk hkn]
  simp only [Nat.succ_sub_one]
  rw [sum_insert_slice _ i a (mem_univ _) (fun S => (∑ l ∈ S,x l)^j)]
  simp only [raw,sum_filter,singleton_subset_iff]

theorem star_moments (i : α) (k : ℕ) (hk : 2 ≤ k) (hn : 2*k ≤ Fintype.card α)
    (x : α → ℝ) (hx : ∑ j,x j=0) (hs : ∑ j,(x j)^2=1) :
    let v := ((Fintype.card α:ℝ)-k)/(Fintype.card α-1)
    let p := (k:ℝ)/Fintype.card α
    let K := ((univ : Finset α).erase i).powersetCard (k-1)
    let Y := fun T => ∑ j ∈ insert i T,x j
    av K Y = v*x i ∧ av K (fun T => (Y T)^2) ≤ (v*x i)^2 + p*v*(1-(x i)^2) := by
  let d := Cnt (Fintype.card α) k
  let v := ((Fintype.card α:ℝ)-k)/(Fintype.card α-1)
  let p := (k:ℝ)/Fintype.card α
  have hkn : k ≤ Fintype.card α := by omega
  have hk0 : 0 < k := by omega
  have hD : 0 < d 1 := by
    rw [show d 1 = _ from singleton_count hk0 hkn]
    exact_mod_cast Nat.choose_pos (show k-1 ≤ Fintype.card α-1 by omega)
  have hA := single_le_sum (s:=univ) (fun j (_ : j ∈ (univ : Finset α)) => sq_nonneg (x j)) (mem_univ i)
  rw [hs] at hA
  obtain ⟨_,hc,hc2,hc3⟩ := star_weights hk hn
  have h₁ := raw_one k hkn x hx {i}
  have h₂ := raw_two k hkn x hx {i}
  rw [ps_compl] at h₂
  simp only [card_singleton,ps,sum_singleton,pow_one,diff₂,diff,Nat.reduceAdd,hs] at h₁ h₂
  dsimp only
  constructor
  · have h := star_raw i k 1 hk0 hkn x
    simp only [pow_one] at h
    rw [h,h₁,hc]
    apply (div_eq_iff hD.ne').2
    ring
  · rw [star_raw i k 2 hk0 hkn x,h₂]
    apply (div_le_iff₀ hD).2
    nlinarith only [mul_le_mul_of_nonneg_right hc2 (sq_nonneg (x i)),
      mul_le_mul_of_nonneg_right hc3 (sub_nonneg.mpr hA)]

end ManickamMiklosSinghi.SevenK
