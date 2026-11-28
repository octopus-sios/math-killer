import Conjectures.ManickamMiklosSinghi.SevenKBase
import Conjectures.ManickamMiklosSinghi.SevenKTransport
namespace ManickamMiklosSinghi.SevenK
open Finset

noncomputable def score {α : Type*} (x : α → ℝ) (S : Finset α) := nonnegInd (∑ i ∈ S, x i)

theorem score_count {α : Type*} (U : Finset α) (k : ℕ) (x : α → ℝ) :
    av (U.powersetCard k) (score x) = ((good U k x).card:ℝ)/(U.card.choose k:ℝ) := by
  classical
  unfold av score nonnegInd good
  simp only [← sum_filter,sum_const,nsmul_eq_mul,mul_one,card_powersetCard]

theorem score_lift {α : Type*} [DecidableEq α] (U : Finset α) (k : ℕ) (x : α → ℝ) :
    av ((univ : Finset U).powersetCard k) (score (fun i : U => x i)) = av (U.powersetCard k) (score x) := by
  unfold av
  rw [card_powersetCard,card_powersetCard,card_univ,Fintype.card_coe,← slice_lift U k (score x)]
  congr 1
  apply sum_congr rfl
  intro T _
  simp [score,valEmb]

/-- Apply an estimate for every centered unit list to any population of
nonnegative total, preserving weak signs even at zero. -/
theorem extend_unit {α : Type*} [Fintype α] (k : ℕ) (hk : k ≤ Fintype.card α)
    (hn : 0 < Fintype.card α) (c : ℝ) (hc : c ≤ 1)
    (unit : ∀ z : α → ℝ, ∑ i, z i = 0 → ∑ i, (z i)^2 = 1 →
      c ≤ av (univ.powersetCard k) (score z)) (x : α → ℝ) (hx : 0 ≤ ∑ i, x i) :
    c ≤ av (univ.powersetCard k) (score x) := by
  classical
  let m := (∑ i, x i)/(Fintype.card α:ℝ)
  let y := fun i => x i-m
  let Q := ∑ i, (y i)^2
  have hn' : (Fintype.card α:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hm : 0 ≤ m := div_nonneg hx (Nat.cast_nonneg _)
  have hy : ∑ i,y i = 0 := by simp [y,sum_sub_distrib,nsmul_eq_mul,m,mul_div_cancel₀ _ hn']
  have hq : 0 ≤ Q := sum_nonneg fun i _ => sq_nonneg (y i)
  by_cases hz : Q = 0
  · have h := (sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (univ : Finset α)) => sq_nonneg (y i))).mp hz
    have hpos (i) : 0 ≤ x i := by
      have hi := h i (mem_univ _)
      have hh : y i = 0 := by nlinarith only [hi,sq_nonneg (y i)]
      change x i-m = 0 at hh
      linarith only [hh,hm]
    have hs (S : Finset α) : score x S = 1 := by
      exact ite_eq_left (sum_nonneg fun i _ => hpos i)
    have he := av_congr (s:=univ.powersetCard k) (fun S _ => hs S)
    rw [he,av_const (slice_ne _ (by simpa using hk))]
    exact hc
  let t := Real.sqrt Q
  have ht : 0 < t := Real.sqrt_pos.mpr (lt_of_le_of_ne hq (Ne.symm hz))
  let z := fun i => y i/t
  have hsum : ∑ i,z i=0 := by simp [z,← sum_div,hy]
  have h2 : ∑ i,(z i)^2=1 := by
    simp only [z,div_pow,← sum_div]
    change Q/t^2=1
    rw [Real.sq_sqrt hq,div_self hz]
  apply (unit z hsum h2).trans (av_mono ?_)
  intro S _
  have hle : (∑ i ∈ S,z i)*t ≤ ∑ i ∈ S,x i := by
    rw [sum_mul]
    apply sum_le_sum
    intro i _
    dsimp only [z,y]
    rw [div_mul_cancel₀ _ ht.ne']
    linarith only [hm]
  by_cases h : 0 ≤ ∑ i ∈ S,z i
  · have hg := (mul_nonneg h ht.le).trans hle
    simp [score,nonnegInd,h,hg]
  · unfold score nonnegInd
    split_ifs <;> simp_all

theorem five_k_density {α : Type*} [DecidableEq α] (U : Finset α) (k : ℕ) (x : α → ℝ)
    (hk : 2 ≤ k) (hn : 5*k ≤ U.card) (htot : 0 ≤ ∑ i ∈ U, x i) :
    69/100*((k:ℝ)/U.card) ≤ av (U.powersetCard k) (score x) := by
  rw [← score_lift]
  have hcard := Fintype.card_coe U
  have hK : k ≤ Fintype.card U := by rw [hcard]; omega
  have hN : 0 < Fintype.card U := by rw [hcard]; omega
  have hn' : (0:ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
  have hk' : (k:ℝ) ≤ U.card := by exact_mod_cast (show k ≤ U.card by omega)
  apply extend_unit k hK hN _ (by
    have hp := (div_le_one hn').2 hk'
    have hp0 := div_nonneg (Nat.cast_nonneg k) hn'.le
    linarith) _ _ (by rw [lift_coord]; exact htot)
  intro z hz h2
  rw [score_count,card_univ,hcard]
  have hD : (0:ℝ) < U.card.choose k := by exact_mod_cast Nat.choose_pos (show k ≤ U.card by omega)
  apply (le_div_iff₀ hD).2
  have h := centered_five_k k z hk (by simpa only [hcard] using hn) hz h2
  simpa only [hcard] using h.le

end ManickamMiklosSinghi.SevenK
