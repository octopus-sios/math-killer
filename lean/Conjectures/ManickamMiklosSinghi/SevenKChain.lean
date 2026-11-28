import Conjectures.ManickamMiklosSinghi.SevenKLoss
import Conjectures.ManickamMiklosSinghi.SevenKMixScalar
namespace ManickamMiklosSinghi.SevenK
open Finset

noncomputable def retained (m a b : ℝ) := m*(m-a-b)/((m-a)*(m-b))

private theorem retained_next (m a b : ℝ) (hm : a+1+b < m) (ha : 0 ≤ a) (hb : 0 < b) :
    retained m (a+1) b =
    retained (m-1) a b * (m*(m-b-1)/((m-1)*(m-b))) := by
  have h1 : m-1 ≠ 0 := by linarith
  have h2 : m-1-b ≠ 0 := by linarith
  have h3 : m-b ≠ 0 := by linarith
  have h4 : m-1-a ≠ 0 := by linarith
  have h5 : m-(a+1) ≠ 0 := by linarith
  unfold retained
  field_simp [h1,h2,h3,h4,h5]
  ring

variable {α : Type*} [DecidableEq α]

/-- Average residual variance after a uniformly chosen set of exclusions. -/
theorem residual_chain (U : Finset α) (a b : ℕ) (hb : 0 < b) (hab : a+b < U.card)
    (f : Finset α → ℝ) :
    retained U.card a b * variance (U.powersetCard b) f ≤
    av (U.powersetCard a) (fun T => variance ((U \ T).powersetCard b) f) := by
  induction a generalizing U with
  | zero =>
    have hm : (0:ℝ) < U.card := by exact_mod_cast (show 0 < U.card by omega)
    have hd : (U.card:ℝ)-b ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (show U.card ≠ b by omega))
    simp [retained,av,hm.ne',hd]
  | succ a ih =>
    let m : ℝ := U.card
    have h : (a:ℝ)+1+b < m := by dsimp only [m]; exact_mod_cast hab
    have ha : (0:ℝ) ≤ a := Nat.cast_nonneg _
    have hb' : (0:ℝ) < b := by exact_mod_cast hb
    let c := retained (m-1) a b
    have hc : 0 ≤ c := by
      unfold c retained
      exact div_nonneg (mul_nonneg (by linarith) (by linarith))
        (mul_nonneg (by linarith) (by linarith))
    rw [← av_expose U a (by omega)]
    change retained m ((a+1:ℕ):ℝ) b * _ ≤ _
    rw [Nat.cast_add,Nat.cast_one,retained_next m a b h ha hb',mul_assoc]
    apply le_trans (mul_le_mul_of_nonneg_left (variance_exclude U b hb (by omega) f) hc)
    rw [← av_scale]
    apply av_mono
    intro i hi
    have hi' : ((U.erase i).card:ℝ) = m-1 := by
      rw [card_erase_of_mem hi,Nat.cast_sub (show 1 ≤ U.card by omega),Nat.cast_one]
    have H := ih (U.erase i) (by rw [card_erase_of_mem hi]; omega)
    rw [hi'] at H
    apply H.trans_eq
    apply av_congr
    intro T _
    have he : U.erase i \ T = U \ insert i T := by ext j; simp; tauto
    rw [he]

theorem disjoint_variance (U : Finset α) (a b : ℕ) (hb : 0 < b) (hb' : b < U.card)
    (hab : a+b ≤ U.card) (f : Finset α → ℝ) :
    let m : ℝ := U.card
    variance (U.powersetCard a) (fun T => av ((U \ T).powersetCard b) f) ≤
    ((a:ℝ)*b/((m-a)*(m-b)))*variance (U.powersetCard b) f := by
  let m : ℝ := U.card
  let K := U.powersetCard a
  let E := fun T => (U \ T).powersetCard b
  let V := variance (U.powersetCard b) f
  change variance K (fun T => av (E T) f) ≤ _*V
  have hchain : retained m a b * V ≤ av K (fun T => variance (E T) f) := by
    rcases hab.lt_or_eq with h | h
    · exact residual_chain U a b hb h f
    · have he : (m-(a:ℝ)-b) = 0 := by dsimp [m]; rw [← h,Nat.cast_add]; ring
      rw [retained,he,mul_zero,zero_div,zero_mul]
      apply div_nonneg _ (Nat.cast_nonneg _)
      apply sum_nonneg
      intro T hT
      have ht := mem_powersetCard.mp hT
      have hE : (E T).Nonempty := slice_ne _ (by rw [card_sdiff_of_subset ht.1,ht.2]; omega)
      rw [← av_centered_sq hE]
      exact div_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (Nat.cast_nonneg _)
  have hv : variance K (fun T => av (E T) f) = V-av K (fun T => variance (E T) f) := by
    simp only [V,E,K,variance,av_sub,av_disjoint U a b hab]
    ring
  have ha : 0 < m-(a:ℝ) := sub_pos.mpr (by dsimp only [m]; exact_mod_cast (show a < U.card by omega))
  have hd : 0 < m-(b:ℝ) := sub_pos.mpr (by dsimp only [m]; exact_mod_cast hb')
  have hid : 1-retained m a b = (a:ℝ)*b/((m-a)*(m-b)) := by
    unfold retained
    field_simp [ha.ne',hd.ne']
    ring
  rw [hv,← hid]
  linarith only [hchain]

end ManickamMiklosSinghi.SevenK
