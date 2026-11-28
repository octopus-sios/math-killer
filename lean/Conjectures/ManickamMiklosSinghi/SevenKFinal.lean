import Conjectures.ManickamMiklosSinghi.SevenKBand
namespace ManickamMiklosSinghi.SevenK
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem centered_six_k (k : ℕ) (x : α → ℝ) (hk : 2 ≤ k) (hn : 6*k ≤ Fintype.card α)
    (hx : ∑ i,x i=0) (hs : ∑ i,(x i)^2=1) :
    (87/100)*((k:ℝ)/Fintype.card α) ≤ av (univ.powersetCard k) (score x) := by
  let p := (k:ℝ)/Fintype.card α
  have hn' : (0:ℝ) < Fintype.card α := by exact_mod_cast (show 0 < Fintype.card α by omega)
  have hnK : 6*(k:ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hp6 : p ≤ 1/6 := (div_le_iff₀ hn').2 (by linarith only [hnK])
  have hc (V : Finset α) (hV : V.card=Fintype.card α-k) (h0 : 0 ≤ ∑ i ∈ V,x i) :=
    five_k_density V k x hk (show 5*k ≤ V.card by omega) h0
  by_cases h : p ≤ 1/7
  · have hb := band_centered k hk (by omega) x hx hs row1 (Or.inl rfl) 0 (by norm_num)
      (by norm_num [row1,Band.gHi]) (div_nonneg (Nat.cast_nonneg _) hn'.le)
      (by simpa only [row1] using h) (by rw [show row1.rc = 69/100 by norm_num [row1]]; exact hc)
    rwa [show row1.r = 87/100 by norm_num [row1]] at hb
  · have hb := band_centered k hk (by omega) x hx hs row2 (Or.inr (Or.inl rfl)) (1/7) (by norm_num)
      (by norm_num [row2,Band.gHi]) (lt_of_not_ge h).le
      (by simpa only [row2] using hp6) (by rw [show row2.rc = 69/100 by norm_num [row2]]; exact hc)
    rwa [show row2.r = 87/100 by norm_num [row2]] at hb

theorem six_k_density {β : Type*} [DecidableEq β] (V : Finset β) (k : ℕ) (x : β → ℝ)
    (hk : 2 ≤ k) (hn : 6*k ≤ V.card) (htot : 0 ≤ ∑ i ∈ V,x i) :
    (87/100)*((k:ℝ)/V.card) ≤ av (V.powersetCard k) (score x) := by
  rw [← score_lift]
  have hc := Fintype.card_coe V
  have hK : k ≤ Fintype.card V := by rw [hc]; omega
  have hN : 0 < Fintype.card V := by rw [hc]; omega
  have hn' : (0:ℝ) < V.card := by exact_mod_cast (show 0 < V.card by omega)
  have hp := (div_le_one hn').2 (show (k:ℝ) ≤ V.card by exact_mod_cast (show k ≤ V.card by omega))
  apply extend_unit k hK hN _ (by linarith only [hp]) _ _ (by rwa [lift_coord])
  intro z hz h2
  simpa only [hc] using centered_six_k k z hk (by simpa only [hc] using hn) hz h2

theorem centered_seven_k (k : ℕ) (x : α → ℝ) (hk : 2 ≤ k) (hn : 7*k ≤ Fintype.card α)
    (hx : ∑ i,x i=0) (hs : ∑ i,(x i)^2=1) :
    (k:ℝ)/Fintype.card α ≤ av (univ.powersetCard k) (score x) := by
  let p := (k:ℝ)/Fintype.card α
  have hn' : (0:ℝ) < Fintype.card α := by exact_mod_cast (show 0 < Fintype.card α by omega)
  have hnK : 7*(k:ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hp7 : p ≤ 1/7 := (div_le_iff₀ hn').2 (by linarith only [hnK])
  have hc (V : Finset α) (hV : V.card=Fintype.card α-k) (h0 : 0 ≤ ∑ i ∈ V,x i) :=
    six_k_density V k x hk (show 6*k ≤ V.card by omega) h0
  rw [← one_mul ((k:ℝ)/Fintype.card α)]
  by_cases h : p ≤ 1/8
  · have hb := band_centered k hk (by omega) x hx hs row3 (Or.inr (Or.inr (Or.inl rfl))) 0 (by norm_num)
      (by norm_num [row3,Band.gHi]) (div_nonneg (Nat.cast_nonneg _) hn'.le)
      (by simpa only [row3] using h) (by rw [show row3.rc = 87/100 by norm_num [row3]]; exact hc)
    rwa [show row3.r = 1 by norm_num [row3]] at hb
  · have hb := band_centered k hk (by omega) x hx hs row4 (Or.inr (Or.inr (Or.inr rfl))) (1/8) (by norm_num)
      (by norm_num [row4,Band.gHi]) (lt_of_not_ge h).le
      (by simpa only [row4] using hp7) (by rw [show row4.rc = 87/100 by norm_num [row4]]; exact hc)
    rwa [show row4.r = 1 by norm_num [row4]] at hb

end ManickamMiklosSinghi.SevenK

namespace ManickamMiklosSinghi
open SevenK Finset

theorem mms_seven_k (n k : ℕ) (hk : 0 < k) (hn : 7*k ≤ n) : MMSHolds n k := by
  by_cases h : k=1
  · subst k; exact mms_one n (by omega)
  have hk' : 2 ≤ k := by omega
  apply mms_of_centered_unit (by omega) hk
  intro x hx hs
  have H := centered_seven_k k x hk' (by simpa using hn) hx hs
  rw [score_count,card_univ,Fintype.card_fin] at H
  have hD : (0:ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos (show k ≤ n by omega)
  have M := (le_div_iff₀ hD).mp H
  have he : ((n-1).choose (k-1):ℝ) = ((k:ℝ)/n)*(n.choose k:ℝ) := by
    rw [← singleton_count hk (by omega),(star_weights hk' (show 2*k ≤ n by omega)).1,mul_comm]
  rw [← he] at M
  exact_mod_cast M

end ManickamMiklosSinghi
