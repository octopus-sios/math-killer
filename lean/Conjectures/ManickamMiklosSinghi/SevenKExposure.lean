import Mathlib

/-! Purely finite double-counting primitives for the disjoint coupling. -/
namespace ManickamMiklosSinghi.SevenK
open Finset

variable {α : Type*} [DecidableEq α]

private theorem restrict_self {T U : Finset α} (h : T ⊆ U) :
    U.filter (fun i => i ∈ T)=T := by
  ext i
  exact ⟨fun hi => (mem_filter.mp hi).2,fun hi => mem_filter.mpr ⟨h hi,hi⟩⟩

noncomputable def incidence (K : Finset (Finset α)) (f : Finset α → ℝ) (i : α) :=
  ∑ S ∈ K, if i ∈ S then f S else 0

/-- Transposition of the point-to-set incidence matrix in sum notation. -/
theorem incidence_duality (U : Finset α) (K : Finset (Finset α)) (hK : ∀ S ∈ K, S ⊆ U)
    (f : Finset α → ℝ) (x : α → ℝ) :
    ∑ i ∈ U, x i * incidence K f i = ∑ S ∈ K, f S * (∑ i ∈ S, x i) := by
  classical
  simp only [incidence,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [mul_ite,mul_zero]
  rw [← Finset.sum_filter,restrict_self (hK S hS)]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Bessel-type incidence estimate for a centered function, derived using
only the variance identity for a linear slice sum (no spectral theorem). -/
theorem incidence_bessel (U : Finset α) (k : ℕ) (f : Finset α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h0 : ∑ S ∈ U.powersetCard k, f S = 0)
    (hV : ∀ u : α → ℝ, ∑ i ∈ U, u i = 0 →
      (∑ S ∈ U.powersetCard k, (∑ i ∈ S, u i)^2) = C*(∑ i ∈ U, (u i)^2)) :
    ∑ i ∈ U, (incidence (U.powersetCard k) f i)^2 ≤
      (∑ S ∈ U.powersetCard k, (f S)^2)*C := by
  classical
  let K := U.powersetCard k
  let u := incidence K f
  let A := ∑ i ∈ U, (u i)^2
  have he (S) (hS : S ∈ K) : S ⊆ U := (mem_powersetCard.mp hS).1
  have hc (S) (hS : S ∈ K) : S.card=k := (mem_powersetCard.mp hS).2
  have hu : ∑ i ∈ U, u i = 0 := calc
    _ = ∑ i ∈ U, (1:ℝ)*incidence K f i := by simp [u]
    _ = ∑ S ∈ K, f S * (∑ _i ∈ S, (1:ℝ)) := incidence_duality U K he f _
    _ = ∑ S ∈ K, f S * (k:ℝ) := by
      apply Finset.sum_congr rfl
      intro S hS
      simp [hc S hS]
    _ = 0 := by rw [← Finset.sum_mul]; change (∑ S ∈ U.powersetCard k, f S)*(k:ℝ)=0
                rw [h0,zero_mul]
  have hd : A = ∑ S ∈ K, f S * (∑ i ∈ S,u i) := by
    simpa only [A,pow_two,u] using incidence_duality U K he f u
  have hh := Finset.sum_mul_sq_le_sq_mul_sq K f (fun S => ∑ i ∈ S,u i)
  rw [← hd,hV u hu] at hh
  have hA : 0 ≤ A := sum_nonneg (fun i _ => sq_nonneg (u i))
  change A ≤ (∑ S ∈ K, (f S)^2)*C
  rcases hA.eq_or_lt with ha | ha
  · rw [← ha]
    exact mul_nonneg (sum_nonneg (fun S _ => sq_nonneg _)) hC
  · have h' : A*A ≤ ((∑ S ∈ K, (f S)^2)*C)*A := by nlinarith only [hh]
    exact le_of_mul_le_mul_right h' ha

/-- Erasing i restricts the slice to precisely those sets excluding i. -/
theorem powersetCard_erase_eq (U : Finset α) (b : ℕ) (i : α) :
    (U.erase i).powersetCard b = (U.powersetCard b).filter (fun S => i ∉ S) := by
  ext S
  simp only [mem_powersetCard,mem_filter]
  constructor
  · rintro ⟨h,hc⟩
    exact ⟨⟨fun j hj => (mem_erase.mp (h hj)).2,hc⟩,fun hi => (mem_erase.mp (h hi)).1 rfl⟩
  · rintro ⟨⟨h,hc⟩,hn⟩
    refine ⟨fun j hj => mem_erase.mpr ⟨?_,h hj⟩,hc⟩
    rintro rfl
    exact hn hj

/-- Extensive form of the first-element exposure identity on the slice. -/
theorem sum_insert_slice (U : Finset α) (i : α) (a : ℕ) (hi : i ∈ U)
    (F : Finset α → ℝ) :
    ∑ T ∈ (U.erase i).powersetCard a, F (insert i T) =
    ∑ S ∈ (U.powersetCard (a+1)).filter (fun S => i ∈ S), F S := by
  classical
  have hnot (T) (hT : T ∈ (U.erase i).powersetCard a) : i ∉ T :=
    fun h => (mem_erase.mp ((mem_powersetCard.mp hT).1 h)).1 rfl
  apply Finset.sum_bij (fun T _ => insert i T)
  · intro T hT
    obtain ⟨hTU,hc⟩ := mem_powersetCard.mp hT
    refine mem_filter.mpr ⟨mem_powersetCard.mpr ⟨insert_subset hi
      (fun j hj => (mem_erase.mp (hTU hj)).2),?_⟩,mem_insert_self _ _⟩
    rw [card_insert_of_notMem (hnot T hT),hc]
  · intro A hA B hB he
    simpa [hnot A hA,hnot B hB] using congrArg (fun T : Finset α => T.erase i) he
  · intro S hS
    obtain ⟨hS',hiS⟩ := mem_filter.mp hS
    obtain ⟨hSU,hSc⟩ := mem_powersetCard.mp hS'
    refine ⟨S.erase i,mem_powersetCard.mpr ⟨?_,?_⟩,insert_erase hiS⟩
    · intro j hj
      exact mem_erase.mpr ⟨(mem_erase.mp hj).1,hSU (mem_erase.mp hj).2⟩
    · rw [card_erase_of_mem hiS,hSc]; omega
  · intro _ _
    rfl

theorem exposure_sum (U : Finset α) (a : ℕ) (F : Finset α → ℝ) :
    ∑ i ∈ U, ∑ T ∈ (U.erase i).powersetCard a, F (insert i T) =
    ((a:ℝ)+1)*(∑ S ∈ U.powersetCard (a+1), F S) := by
  classical
  calc
    _ = ∑ i ∈ U, ∑ S ∈ (U.powersetCard (a+1)).filter (fun S => i ∈ S), F S :=
      Finset.sum_congr rfl (fun i hi => sum_insert_slice U i a hi F)
    _ = _ := by
      simp only [Finset.sum_filter]
      rw [Finset.sum_comm,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_filter,restrict_self (mem_powersetCard.mp hS).1]
      simp [(mem_powersetCard.mp hS).2,nsmul_eq_mul]

/-- Count one excluded point, keeping an arbitrary score on the b-set. -/
theorem exclusion_sum (U : Finset α) (b : ℕ) (hb : b ≤ U.card) (F : Finset α → ℝ) :
    ∑ i ∈ U, ∑ D ∈ (U.erase i).powersetCard b, F D =
    ((U.card:ℝ)-b)*(∑ D ∈ U.powersetCard b, F D) := by
  classical
  simp_rw [powersetCard_erase_eq,Finset.sum_filter]
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [← Finset.sum_filter]
  have hF : U.filter (fun i => i ∉ S) = U \ S := by ext i; simp
  rw [hF]
  simp [nsmul_eq_mul,card_sdiff_of_subset (mem_powersetCard.mp hS).1,
    (mem_powersetCard.mp hS).2,Nat.cast_sub hb]

end ManickamMiklosSinghi.SevenK
