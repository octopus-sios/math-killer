import Conjectures.ManickamMiklosSinghi.SevenKHolder
import Conjectures.ManickamMiklosSinghi.SevenKScalar
import Conjectures.ManickamMiklosSinghi.SevenKStats
namespace ManickamMiklosSinghi.SevenK
open Finset

/-- The entire start-density implication, from the actual averaged sample
identities. The singleton-incidence moment supplies coordinate control for
either sign without sorting or choosing a maximizing coordinate. -/
theorem start_from_moments {α : Type*} [DecidableEq α] (U : Finset α)
    (K : Finset (Finset α)) (x : α → ℝ) (Y μ : Finset α → ℝ)
    (p v w R B : ℝ) (hp : 0 < p) (hv : 4/5 ≤ v) (hR0 : 0 ≤ R)
    (hw : 0 ≤ w) (hw' : w ≤ 1/6) (hμ : ∀ j ∈ K, 0 ≤ μ j)
    (hN : ∑ i ∈ U, (x i)^2 = 1)
    (h₁ : ∑ j ∈ K, μ j * Y j = 0)
    (h₂ : ∑ j ∈ K, μ j * (Y j)^2 = p*v)
    (h₄ : ∑ j ∈ K, μ j * (Y j)^4 = (p*v)*B)
    (hB : B=3*w+(1-6*w)*(∑ i ∈ U, (x i)^4))
    (hsing : ∀ i ∈ U, (∑ j ∈ K, μ j * (if i ∈ j then Y j else 0)) = (p*v)*x i)
    (hR : ∑ j ∈ K, μ j * nonnegInd (Y j) = p*R) : 69/100 < R := by
  classical
  let V := p*v
  have hv' : 0 < v := by linarith
  have hV : 0 < V := mul_pos hp hv'
  let m := ∑ j ∈ K, μ j * positive (Y j)
  let P := ∑ j ∈ K, μ j * positive (Y j)^2
  let N := ∑ j ∈ K, μ j * negative (Y j)^2
  let P₄ := ∑ j ∈ K, μ j * positive (Y j)^4
  let N₄ := ∑ j ∈ K, μ j * negative (Y j)^4
  let a := P/V
  let s := R/v
  have hRs : R = v*s := by dsimp [s]; field_simp [hv'.ne']
  have hP : P = a*V := (div_mul_cancel₀ _ hV.ne').symm
  have hM : m = ∑ j ∈ K, μ j * negative (Y j) := parts_mean K μ Y h₁
  have hX : P+N=V := (parts_even K μ Y 1 (by decide)).trans h₂
  have hX₄ : P₄+N₄=V*B := (parts_even K μ Y 2 (by decide)).trans h₄
  have hVB : 0 ≤ V*B := by
    rw [← h₄]
    exact sum_nonneg fun j hj => mul_nonneg (hμ j hj) (by positivity)
  have hN' : N=(1-a)*V := by linarith only [hP,hX]
  have hcs := sign_cs K μ Y hμ
  rw [hR] at hcs
  change m^2 ≤ p*R*P at hcs
  have hpos := interp_124 K μ (fun j => positive (Y j)) hμ (fun j _ => le_max_right _ _)
  have hneg := interp_124 K μ (fun j => negative (Y j)) hμ (fun j _ => le_max_right _ _)
  change P^3 ≤ m^2*P₄ at hpos
  rw [← hM] at hneg
  change N^3 ≤ m^2*N₄ at hneg
  have hm' : a^3+(1-a)^3 ≤ a*s*B := by
    have hh : (a^3+(1-a)^3)*V^3 ≤ (a*s*B)*V^3 := calc
      _ = P^3+N^3 := by rw [hP,hN']; ring
      _ ≤ m^2*P₄ + m^2*N₄ := add_le_add hpos hneg
      _ = m^2*(V*B) := by rw [← mul_add,hX₄]
      _ ≤ (p*R*P)*(V*B) := mul_le_mul_of_nonneg_right hcs hVB
      _ = _ := by rw [hP,hRs]; dsimp [V]; ring
    exact le_of_mul_le_mul_right hh (pow_pos hV 3)
  have hP0 : 0 ≤ P := sum_nonneg fun j hj => mul_nonneg (hμ j hj) (sq_nonneg _)
  have ha0 : 0 ≤ a := div_nonneg hP0 hV.le
  have ha : 0 < a := lt_of_le_of_ne ha0 (by rintro he; rw [← he] at hm'; norm_num at hm')
  have hC (i) (hi : i ∈ U) : (V*x i)^2 ≤ m^2 := by
    have h1 : V*x i ≤ m := by
      rw [← hsing i hi]
      apply sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (hμ j hj)
      split_ifs <;> first | exact le_max_left _ _ | exact le_max_right _ _
    have h2 : -(V*x i) ≤ m := by
      rw [← hsing i hi,hM,← sum_neg_distrib]
      apply sum_le_sum
      intro j hj
      rw [← mul_neg]
      apply mul_le_mul_of_nonneg_left _ (hμ j hj)
      unfold negative
      split_ifs
      · exact le_max_left _ _
      · rw [neg_zero]; exact le_max_right _ _
    nlinarith only [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hS : (∑ i ∈ U, (x i)^4) ≤ s*a := by
    have hh : V^2*(∑ i ∈ U, (x i)^4) ≤ V^2*(s*a) := calc
      _ ≤ m^2*(∑ i ∈ U, (x i)^2) := by
        rw [Finset.mul_sum,Finset.mul_sum]
        apply sum_le_sum
        intro i hi
        nlinarith only [mul_le_mul_of_nonneg_right (hC i hi) (sq_nonneg (x i))]
      _ = m^2 := by rw [hN,mul_one]
      _ ≤ p*R*P := hcs
      _ = _ := by rw [hP,hRs]; dsimp [V]; ring
    exact le_of_mul_le_mul_left hh (pow_pos hV 2)
  have hBw : B ≤ 3*w+(1-6*w)*(s*a) := by
    rw [hB]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hS (show 0 ≤ 1-6*w by linarith only [hw']))
  exact density_start_scalar a w s R v B ha (div_nonneg hR0 hv'.le) hw hw' hv hRs hBw hm'

end ManickamMiklosSinghi.SevenK
