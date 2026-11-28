import Conjectures.ManickamMiklosSinghi.SevenKStar
import Conjectures.ManickamMiklosSinghi.SevenKBase
namespace ManickamMiklosSinghi.SevenK
open Finset

theorem weighted_mean {α : Type*} (s : Finset α) (f : α → ℝ) :
    (∑ i ∈ s, (1/(s.card:ℝ))*f i) = av s f := by rw [← mul_sum,av]; ring

theorem av_nonneg {α : Type*} {s : Finset α} {f : α → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) :
    0 ≤ av s f := div_nonneg (sum_nonneg hf) (Nat.cast_nonneg _)

private theorem one_sq_mean {ι : Type*} (s : Finset ι) (hne : s.Nonempty) (f : ι → ℝ) :
    (av s f)^2 ≤ av s (fun i => (f i)^2) := by
  have h := av_cs s (fun _ => 1) f
  simpa only [one_mul,one_pow,av_const hne] using h

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cap_data (k : ℕ) (hk : 2 ≤ k) (hn : 5*k ≤ Fintype.card α)
    (x : α → ℝ) (hx : ∑ i,x i=0) (hs : ∑ i,(x i)^2=1)
    (i j : α) (hi : 0 ≤ x i) (hj : x j ≤ 0) (r : ℝ) :
    let n := Fintype.card α
    let p := (k:ℝ)/n
    let v := ((n:ℝ)-k)/(n-1)
    let K := (univ : Finset α).powersetCard k
    let Y := fun S : Finset α => ∑ l ∈ S,x l
    let A := ((univ : Finset α).erase i).powersetCard (k-1)
    let bad := av A (fun T => 1-nonnegInd (Y (insert i T)))
    let m := av K (fun S => positive (Y S))
    let vp := av K (fun S => positive (Y S)^2)
    let vn := av K (fun S => negative (Y S)^2)
    av K (fun S => nonnegInd (Y S)) ≤ r*p →
    bad*(v*x i)^2 ≤ (1-bad)*(p*v*(1-(x i)^2)) ∧ p*v*(-x j) ≤ m ∧ m^2 ≤ r*p*vp ∧
    p*v^2*(-x j)^2 ≤ vn ∧ vp+vn=p*v := by
  intro n p v K Y A bad m vp vn hR
  have hn' : 0 < (n:ℝ) := by exact_mod_cast (show 0 < Fintype.card α by omega)
  have hnk : (k:ℝ) ≤ n := by exact_mod_cast (show k ≤ Fintype.card α by omega)
  have hp : 0 ≤ p := div_nonneg (Nat.cast_nonneg _) hn'.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hnk) (by
    have : (1:ℝ) ≤ n := by exact_mod_cast (show 1 ≤ Fintype.card α by omega)
    linarith)
  have hp1 : 0 ≤ 1-p := sub_nonneg.mpr ((div_le_one hn').2 hnk)
  have hK : (K.card:ℝ) = (n.choose k:ℝ) := by simp [K,n]
  have hA : A.Nonempty := slice_ne _ (by rw [card_erase_of_mem (mem_univ _),card_univ]; omega)
  have hstar := star_moments i k hk (by omega) x hx hs
  let Z := fun T => Y (insert i T)
  change av A Z=v*x i ∧ av A (fun T => (Z T)^2) ≤ _ at hstar
  have hgood : av A (fun T => nonnegInd (Z T)) = 1-bad := by
    dsimp only [bad]
    rw [av_sub,av_const hA]
    ring
  have hgood0 : 0 ≤ 1-bad := hgood ▸ av_nonneg (fun T _ => by unfold nonnegInd; split_ifs <;> norm_num)
  have hc := cantelli A (fun _ => 1/(A.card:ℝ)) Z (fun _ _ => by positivity) (v*x i) bad
    (av A (fun T => (Z T)^2)-(v*x i)^2) (mul_nonneg hv hi)
    ((weighted_mean A Z).trans hstar.1) ((weighted_mean A _).trans hgood)
    (by rw [weighted_mean]; ring)
  have hvar : bad*(v*x i)^2 ≤ (1-bad)*(p*v*(1-(x i)^2)) :=
    hc.trans (mul_le_mul_of_nonneg_left (by linarith only [hstar.2]) hgood0)
  have hdom (f : Finset α → ℝ) (hf : ∀ S, 0 ≤ f S) :
      p*av (((univ : Finset α).erase j).powersetCard (k-1)) (fun T => f (insert j T)) ≤ av K f := by
    have h := star_split k hk (by omega) j f
    exact h ▸ le_add_of_nonneg_right (mul_nonneg hp1 (av_nonneg (fun S _ => hf S)))
  let J := ((univ : Finset α).erase j).powersetCard (k-1)
  let W := fun T => Y (insert j T)
  let M := av J (fun T => negative (W T))
  have hJ : J.Nonempty := slice_ne _ (by rw [card_erase_of_mem (mem_univ _),card_univ]; omega)
  have hμ := (star_moments j k hk (by omega) x hx hs).1
  change av J W=v*x j at hμ
  have hM : v*(-x j) ≤ M := calc
    _ = av J (fun T => (-1)*W T) := by rw [av_scale,hμ]; ring
    _ ≤ _ := av_mono (fun T _ => by simpa only [neg_one_mul, negative] using le_max_left (-W T) 0)
  have hM2 : (v*(-x j))^2 ≤ av J (fun T => negative (W T)^2) :=
    (pow_le_pow_left₀ (mul_nonneg hv (neg_nonneg.mpr hj)) hM 2).trans (one_sq_mean J hJ _)
  have hneg := hdom (fun S => negative (Y S)) (fun _ => le_max_right _ _)
  have hneg2 := hdom (fun S => negative (Y S)^2) (fun _ => sq_nonneg _)
  change p*M ≤ _ at hneg
  have h2low : p*v^2*(-x j)^2 ≤ vn := by
    have h := (mul_le_mul_of_nonneg_left hM2 hp).trans hneg2
    nlinarith only [h]
  obtain ⟨c₁,c₂,_,_,_⟩ := slice_identities k x (by omega) (by omega) hx hs
  let w := fun _ : Finset α => 1/(K.card:ℝ)
  have h₁ : ∑ S ∈ K,w S*Y S=0 := by dsimp only [w]; rw [hK]; exact c₁
  have h₂ : ∑ S ∈ K,w S*(Y S)^2=p*v := by dsimp only [w]; rw [hK]; exact c₂
  have hm := parts_mean K w Y h₁
  dsimp only [w] at hm
  rw [weighted_mean,weighted_mean] at hm
  change m = _ at hm
  have hlow : p*v*(-x j) ≤ m := by
    rw [hm,mul_assoc]
    exact (mul_le_mul_of_nonneg_left hM hp).trans hneg
  have hcs := sign_cs K w Y (fun _ _ => by dsimp [w]; positivity)
  dsimp only [w] at hcs
  simp only [weighted_mean] at hcs
  have htot := (parts_even K w Y 1 (by decide)).trans h₂
  change (∑ S ∈ K,1/(K.card:ℝ)*positive (Y S)^2)+(∑ S ∈ K,1/(K.card:ℝ)*negative (Y S)^2)=p*v at htot
  rw [weighted_mean,weighted_mean] at htot
  exact ⟨hvar,hlow,hcs.trans (mul_le_mul_of_nonneg_right hR (av_nonneg fun S _ => sq_nonneg _)),h2low,htot⟩

end ManickamMiklosSinghi.SevenK
