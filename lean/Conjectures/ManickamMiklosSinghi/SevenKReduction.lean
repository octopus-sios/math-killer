import Mathlib
import Conjectures.ManickamMiklosSinghi.Foundation

namespace ManickamMiklosSinghi

open Finset
open scoped BigOperators

noncomputable section


namespace SevenK

theorem mms_one (n : ℕ) (hn : 0 < n) : MMSHolds n 1 := by
  classical
  intro x hx
  have hn' : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  have he : ∃ i : Fin n, 0 ≤ x i := by
    by_contra! hh
    have hneg := Finset.sum_neg (fun i (_ : i ∈ (univ : Finset (Fin n))) => hh i) hn'
    linarith
  obtain ⟨i,hi⟩ := he
  simp only [Nat.sub_self,Nat.choose_zero_right]
  apply Finset.card_pos.mpr
  exact ⟨{i},mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,by simp⟩,by simpa using hi⟩⟩

private theorem star_le_slice (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (n-1).choose (k-1) ≤ n.choose k := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨v,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [Nat.choose_succ_succ]
  simp

/-- Reduction to an exactly centered list on the Euclidean unit sphere.
The sizes and indexed family are unchanged; constant lists are handled here. -/
theorem mms_of_centered_unit {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (h : ∀ x : Fin n → ℝ, ∑ i, x i = 0 → ∑ i, (x i)^2 = 1 →
      (n-1).choose (k-1) ≤ (nonnegKSubsets n k x).card) : MMSHolds n k := by
  classical
  intro x hx
  let a := (∑ i, x i)/(n:ℝ)
  let y := fun i => x i-a
  let q := ∑ i, (y i)^2
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have ha : 0 ≤ a := div_nonneg hx (Nat.cast_nonneg _)
  have hya : ∑ i, y i = 0 := by
    simp [y,sum_sub_distrib,a,nsmul_eq_mul, hn0] <;> field_simp [hn0] <;> ring
  have hq : 0 ≤ q := Finset.sum_nonneg (fun i _ => sq_nonneg (y i))
  by_cases hq0 : q=0
  · have hy0 := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ (univ : Finset (Fin n))) =>
        sq_nonneg (y i))).mp hq0
    have hx0 (i : Fin n) : 0 ≤ x i := by
      have hy := hy0 i (mem_univ _)
      have hz : y i=0 := by nlinarith only [hy,sq_nonneg (y i)]
      dsimp only [y] at hz
      linarith
    have he : nonnegKSubsets n k x = (univ : Finset (Fin n)).powersetCard k := by
      ext S
      simp only [nonnegKSubsets,good,mem_filter,and_iff_left_iff_imp]
      intro _
      exact sum_nonneg fun i _ => hx0 i
    rw [he,card_powersetCard,card_univ,Fintype.card_fin]
    exact star_le_slice n k hn hk
  let t := Real.sqrt q
  have ht : 0 < t := Real.sqrt_pos.mpr (lt_of_le_of_ne hq (Ne.symm hq0))
  have ht2 : t^2=q := Real.sq_sqrt hq
  let z := fun i => y i/t
  have hz : ∑ i, z i = 0 := by simpa [z,← Finset.sum_div,hya]
  have hzz : ∑ i, (z i)^2 = 1 := by
    simp only [z,div_pow,← Finset.sum_div]
    change q/t^2=1
    rw [ht2,div_self hq0]
  apply (h z hz hzz).trans (card_le_card ?_)
  intro S hS
  obtain ⟨hK,hgood⟩ := mem_filter.mp hS
  refine mem_filter.mpr ⟨hK,?_⟩
  have hcomp : ∀ i, (z i)*t ≤ x i := by
    intro i
    dsimp only [z,y]
    rw [div_mul_cancel₀ _ ht.ne']
    linarith
  have hh := mul_nonneg hgood ht.le
  rw [Finset.sum_mul] at hh
  exact hh.trans (sum_le_sum fun i _ => hcomp i)

end SevenK
end
end ManickamMiklosSinghi
