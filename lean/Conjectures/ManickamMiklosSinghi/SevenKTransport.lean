import Conjectures.ManickamMiklosSinghi.SevenKMean
import Conjectures.ManickamMiklosSinghi.SevenKFullMoments
namespace ManickamMiklosSinghi.SevenK
open Finset

variable {α : Type*} [DecidableEq α]

def valEmb (U : Finset α) : U ↪ α := Function.Embedding.subtype _

omit [DecidableEq α] in
theorem univ_map_val (U : Finset α) :
    (univ : Finset U).map (valEmb U) = U := by
  ext i
  simp [valEmb]

omit [DecidableEq α] in
theorem slice_lift (U : Finset α) (k : ℕ) (f : Finset α → ℝ) :
    ∑ T ∈ (univ : Finset U).powersetCard k, f (T.map (valEmb U)) =
      ∑ S ∈ U.powersetCard k, f S := by
  conv_rhs => rw [← univ_map_val U, powersetCard_map]
  simp [Finset.sum_map]

omit [DecidableEq α] in
theorem lift_coord (U : Finset α) (x : α → ℝ) :
    ∑ i : U, x i = ∑ i ∈ U, x i := by
  conv_rhs => rw [← univ_map_val U,Finset.sum_map]
  rfl

/-- Variance identity for linear slice sums over an arbitrary finite ground
set, in the extensive form used by the incidence Bessel estimate. -/
theorem linear_slice_two (U : Finset α) (b : ℕ) (hb : b ≤ U.card)
    (u : α → ℝ) (hu : ∑ i ∈ U, u i = 0) :
    (∑ D ∈ U.powersetCard b, (∑ i ∈ D,u i)^2) =
      (Cnt U.card b 1-Cnt U.card b 2)*(∑ i ∈ U,(u i)^2) := by
  have hc : Fintype.card U = U.card := Fintype.card_coe _
  have h := (centered_raw_moments b (by simpa only [hc] using hb)
    (fun i : U => u i) ((lift_coord U u).trans hu)).2.1
  simp only [raw,empty_subset,ite_true,hc] at h
  rw [← slice_lift U b, ← lift_coord U (fun i => (u i)^2)]
  simpa only [sum_map,valEmb,Function.Embedding.coe_subtype] using h

end ManickamMiklosSinghi.SevenK
