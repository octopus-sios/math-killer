import Conjectures.ManickamMiklosSinghi.SevenKAverage
import Conjectures.ManickamMiklosSinghi.SevenKTransport
import Conjectures.ManickamMiklosSinghi.SevenKLossScalar
namespace ManickamMiklosSinghi.SevenK
open Finset

theorem variance_shift {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ) :
    variance s (fun i => f i-c) = variance s f := by
  rw [← av_centered_sq hs,← av_centered_sq hs,av_sub,av_const hs]
  apply av_congr
  intro i _
  ring

variable {α : Type*} [DecidableEq α]

private theorem sum_erase_centered (U : Finset α) (b : ℕ) (g : Finset α → ℝ)
    (hg : ∑ S ∈ U.powersetCard b, g S = 0) (i : α) :
    ∑ S ∈ (U.erase i).powersetCard b, g S = - incidence (U.powersetCard b) g i := by
  apply eq_neg_of_add_eq_zero_left
  rw [powersetCard_erase_eq,sum_filter,incidence,← sum_add_distrib]
  exact (sum_congr rfl (fun S _ => by by_cases hi : i ∈ S <;> simp [hi])).trans hg

/-- Expected variance remaining after excluding one uniformly chosen point. -/
theorem variance_exclude (U : Finset α) (b : ℕ) (hb : 0 < b) (hm : b < U.card)
    (f : Finset α → ℝ) :
    let m : ℝ := U.card
    (m*(m-b-1)/((m-1)*(m-b)))*variance (U.powersetCard b) f ≤
    av U (fun i => variance ((U.erase i).powersetCard b) f) := by
  let K := U.powersetCard b
  let m : ℝ := U.card
  let D : ℝ := U.card.choose b
  let L : ℝ := (U.card-1).choose b
  let C := Cnt U.card b 1-Cnt U.card b 2
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast Nat.choose_pos hm.le
  have hL : 0 < L := by dsimp only [L]; exact_mod_cast Nat.choose_pos (show b ≤ U.card-1 by omega)
  have h1 : 1 < m := by dsimp only [m]; exact_mod_cast (show 1 < U.card by omega)
  have h2 : (b:ℝ) < m := by dsimp only [m]; exact_mod_cast hm
  obtain ⟨hc,hd⟩ := loss_counts U.card b hb hm
  change L*m = D*(m-b) at hc
  change C*(m-1) = L*b at hd
  have hC : 0 ≤ C := by
    have h : 0 ≤ C*(m-1) := hd ▸ mul_nonneg hL.le (Nat.cast_nonneg b)
    exact nonneg_of_mul_nonneg_left h (by linarith only [h1])
  let g := fun S => f S - av K f
  let V := variance K f
  let Q := ∑ i ∈ U, (incidence K g i)^2
  have hK : (K.card:ℝ)=D := by simp [K,D]
  have hg0 : ∑ S ∈ K,g S=0 := by
    simp only [g,sum_sub_distrib,sum_const,nsmul_eq_mul,av,hK]
    field_simp [hD.ne']
    ring
  have hV : av K (fun S => (g S)^2) = V := av_centered_sq (slice_ne U hm.le) f
  have hV' : ∑ S ∈ K,(g S)^2 = V*D := by
    change (∑ S ∈ K,(g S)^2)/(K.card:ℝ) = V at hV
    rwa [hK,div_eq_iff hD.ne'] at hV
  have H := incidence_bessel U b g C hC hg0 (fun u hu => linear_slice_two U b hm.le u hu)
  change Q ≤ (∑ S ∈ K,(g S)^2)*C at H
  rw [hV'] at H
  have hM : av U (fun i => (av ((U.erase i).powersetCard b) g)^2) = Q/L^2/m := by
    unfold av
    change (∑ i ∈ U, ((∑ S ∈ (U.erase i).powersetCard b, g S)/_)^2)/m = Q/L^2/m
    congr 1
    rw [show Q/L^2 = ∑ i ∈ U, (incidence K g i)^2/L^2 by rw [← sum_div]]
    apply sum_congr rfl
    intro i hi
    rw [sum_erase_centered U b g hg0,card_powersetCard,card_erase_of_mem hi,div_pow,neg_sq]
  have res : av U (fun i => variance ((U.erase i).powersetCard b) f) = V-Q/L^2/m := by
    calc
      _ = av U (fun i => variance ((U.erase i).powersetCard b) g) := by
        apply av_congr
        intro i hi
        exact (variance_shift (slice_ne _ (by rw [card_erase_of_mem hi]; omega)) f (av K f)).symm
      _ = _ := by
        unfold variance
        rw [av_sub,av_exclude U b hm,hM,hV]
  rw [res]
  exact excluded_mean_scalar m b D L C Q V h1 h2 hL hc hd H

end ManickamMiklosSinghi.SevenK
