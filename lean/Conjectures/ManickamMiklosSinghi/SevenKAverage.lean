import Conjectures.ManickamMiklosSinghi.SevenKExposure
import Conjectures.ManickamMiklosSinghi.SevenKMean
namespace ManickamMiklosSinghi.SevenK
open Finset

/-- Normalise a constant-degree double count without having to simplify any
binomial coefficient. The count for the constant function supplies the mass. -/
private theorem av_rows {ι α β : Type*} (s : Finset ι) (t : Finset β)
    (K : ι → Finset α) (f : ι → α → β) (L c : ℝ)
    (hs : s.Nonempty) (ht : t.Nonempty) (hL : 0 < L)
    (hcard : ∀ i ∈ s, ((K i).card:ℝ)=L)
    (count : ∀ G : β → ℝ, (∑ i ∈ s, ∑ a ∈ K i, G (f i a)) = c*(∑ b ∈ t, G b))
    (G : β → ℝ) :
    av s (fun i => av (K i) (fun a => G (f i a))) = av t G := by
  have h1 := count (fun _ => 1)
  simp only [sum_const,nsmul_eq_mul,mul_one] at h1
  have h2 : (∑ i ∈ s, ((K i).card:ℝ)) = (s.card:ℝ)*L := by
    rw [sum_congr rfl hcard]
    simp [nsmul_eq_mul]
  rw [h2] at h1
  have hs' : (0:ℝ) < s.card := by exact_mod_cast card_pos.mpr hs
  have ht' : (0:ℝ) < t.card := by exact_mod_cast card_pos.mpr ht
  have hrow (i) (hi : i ∈ s) : av (K i) (fun a => G (f i a)) =
      (∑ a ∈ K i, G (f i a))/L := by rw [av,hcard i hi]
  unfold av
  change (∑ i ∈ s, av (K i) (fun a => G (f i a)))/(s.card:ℝ)=_
  rw [sum_congr rfl hrow,← sum_div,count]
  field_simp [hs'.ne',ht'.ne',hL.ne']
  linear_combination -(∑ b ∈ t, G b)*h1

variable {α : Type*} [DecidableEq α]

theorem av_expose (U : Finset α) (a : ℕ) (ha : a+1 ≤ U.card) (G : Finset α → ℝ) :
    av U (fun i => av ((U.erase i).powersetCard a) (fun T => G (insert i T))) =
    av (U.powersetCard (a+1)) G := by
  apply av_rows U _ _ _ (((U.card-1).choose a:ℕ):ℝ) ((a:ℝ)+1)
    (card_pos.mp (by omega)) (slice_ne U ha)
  · exact_mod_cast Nat.choose_pos (show a ≤ U.card-1 by omega)
  · intro i hi
    rw [card_powersetCard,card_erase_of_mem hi]
  · exact exposure_sum U a

theorem av_exclude (U : Finset α) (b : ℕ) (hb : b < U.card) (G : Finset α → ℝ) :
    av U (fun i => av ((U.erase i).powersetCard b) G) = av (U.powersetCard b) G := by
  apply av_rows U _ _ (fun _ D => D) (((U.card-1).choose b:ℕ):ℝ) ((U.card:ℝ)-b)
    (card_pos.mp (by omega)) (slice_ne U hb.le)
  · exact_mod_cast Nat.choose_pos (show b ≤ U.card-1 by omega)
  · intro i hi
    rw [card_powersetCard,card_erase_of_mem hi]
  · exact exclusion_sum U b hb.le

/-- The terminal sample is uniform even after first sampling a disjoint set. -/
theorem av_disjoint (U : Finset α) (a b : ℕ) (hab : a+b ≤ U.card)
    (G : Finset α → ℝ) :
    av (U.powersetCard a) (fun T => av ((U \ T).powersetCard b) G) =
    av (U.powersetCard b) G := by
  induction a generalizing U with
  | zero => simp [av]
  | succ a ih =>
    rw [← av_expose U a (by omega),← av_exclude U b (by omega)]
    apply av_congr
    intro i hi
    have h := ih (U.erase i) (by rw [card_erase_of_mem hi]; omega)
    apply Eq.trans _ h
    apply av_congr
    intro T _
    have he : U \ insert i T = U.erase i \ T := by ext j; simp; tauto
    rw [he]

end ManickamMiklosSinghi.SevenK
