import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-! Slice moments via conditional recursion. Incidence of t in a sampled k-set
is counted by taking the complement of that set, including when t.card > k. -/
namespace ManickamMiklosSinghi.SevenK

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Unnormalised m-th moment on the k-slice with all of t imposed. -/
noncomputable def raw (k : ℕ) (x : α → ℝ) (m : ℕ) (t : Finset α) : ℝ :=
  ∑ S ∈ (univ : Finset α).powersetCard k, if t ⊆ S then (∑ i ∈ S, x i)^m else 0

def Cnt (n k j : ℕ) : ℝ := ((n-j).choose (n-k) : ℕ)

theorem raw_zero (k : ℕ) (hk : k ≤ Fintype.card α) (x : α → ℝ) (t : Finset α) :
    raw k x 0 t = Cnt (Fintype.card α) k t.card := by
  classical
  let K := (univ : Finset α).powersetCard k
  have H : (K.filter fun S => t ⊆ S).card =
      (tᶜ.powersetCard (Fintype.card α-k)).card := by
    apply Finset.card_bij (fun S _ => Sᶜ)
    · intro S hS
      obtain ⟨hK,ht⟩ := mem_filter.mp hS
      refine mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro i hi
        exact mem_compl.mpr (fun h => mem_compl.mp hi (ht h))
      · rw [card_compl,(mem_powersetCard.mp hK).2]
    · intro A hA B hB he
      simpa using congrArg (fun S : Finset α => Sᶜ) he
    · intro B hB
      obtain ⟨hBt,hBk⟩ := mem_powersetCard.mp hB
      refine ⟨Bᶜ,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,?_⟩,?_⟩,by simp⟩
      · rw [card_compl,hBk]
        omega
      · intro i hi
        exact mem_compl.mpr fun h => mem_compl.mp (hBt h) hi
  rw [card_powersetCard,card_compl] at H
  unfold raw
  simp only [pow_zero, ← Finset.sum_filter, sum_const, nsmul_eq_mul,mul_one]
  exact congrArg Nat.cast H

/-- Multiplying by the sampled sum exposes one further inclusion constraint. -/
theorem raw_succ (k : ℕ) (x : α → ℝ) (m : ℕ) (t : Finset α) :
    raw k x (m+1) t = (∑ i ∈ t, x i)*raw k x m t +
      ∑ i ∈ tᶜ, x i * raw k x m (insert i t) := by
  classical
  let K := (univ : Finset α).powersetCard k
  have he : raw k x (m+1) t = ∑ i, x i * raw k x m (insert i t) := by
    unfold raw
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S _
    by_cases ht : t ⊆ S
    · simp only [ht,ite_true,insert_subset_iff,and_true,pow_succ,mul_ite,mul_zero]
      rw [← Finset.sum_filter]
      simp [← Finset.sum_mul, mul_comm]
    · simp [ht,insert_subset_iff]
  rw [he,← Finset.sum_add_sum_compl t (fun i => x i * raw k x m (insert i t))]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [insert_eq_of_mem hi]

/-- Partial power sums over a specified set and its complement. -/
noncomputable def ps (x : α → ℝ) (j : ℕ) (t : Finset α) := ∑ i ∈ t, (x i)^j

theorem ps_compl (x : α → ℝ) (j : ℕ) (t : Finset α) :
    ps x j tᶜ = ps x j univ - ps x j t := by
  have h := Finset.sum_add_sum_compl t (fun i => (x i)^j)
  dsimp [ps]
  linarith

noncomputable def diff (d : ℕ → ℝ) (r : ℕ) := d r-d (r+1)
noncomputable def diff₂ (d : ℕ → ℝ) (r : ℕ) := diff d r - diff d (r+1)

/-- Conditional first moment without a normalization of the squared norm. -/
theorem raw_one (k : ℕ) (hk : k ≤ Fintype.card α) (x : α → ℝ) (hx : ∑ i, x i = 0)
    (t : Finset α) :
    raw k x 1 t = diff (Cnt (Fintype.card α) k) t.card * ps x 1 t := by
  classical
  let d := Cnt (Fintype.card α) k
  rw [raw_succ k x 0 t,raw_zero k hk]
  have he : ∑ i ∈ tᶜ, x i * raw k x 0 (insert i t) =
      (∑ i ∈ tᶜ, x i)*d (t.card+1) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [raw_zero k hk, card_insert_of_notMem (mem_compl.mp hi)]
  rw [he]
  have hc := Finset.sum_add_sum_compl t x
  simp only [ps,pow_one,diff]
  dsimp [d] at *
  linear_combination (Cnt (Fintype.card α) k (t.card+1))*(hc.trans hx)

theorem raw_two (k : ℕ) (hk : k ≤ Fintype.card α) (x : α → ℝ) (hx : ∑ i, x i = 0)
    (t : Finset α) :
    let d := Cnt (Fintype.card α) k
    raw k x 2 t = diff₂ d t.card*(ps x 1 t)^2 + diff d (t.card+1)*ps x 2 tᶜ := by
  classical
  dsimp only
  let d := Cnt (Fintype.card α) k
  rw [raw_succ k x 1 t,raw_one k hk x hx]
  have he : ∑ i ∈ tᶜ, x i * raw k x 1 (insert i t) =
      diff d (t.card+1)*ps x 2 tᶜ +
      (diff d (t.card+1)*ps x 1 t)*(∑ i ∈ tᶜ, x i) := by
    simp only [ps,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hf := mem_compl.mp hi
    rw [raw_one k hk x hx,card_insert_of_notMem hf]
    simp only [ps,sum_insert hf,pow_one,d, ← Finset.mul_sum]
    ring
  rw [he]
  have hc := (Finset.sum_add_sum_compl t x).trans hx
  simp only [diff₂,ps,pow_one,d]
  linear_combination (diff (Cnt (Fintype.card α) k) (t.card+1) * (∑ i ∈ t, x i))*hc

end ManickamMiklosSinghi.SevenK

namespace ManickamMiklosSinghi.SevenK
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem ps_insert_compl (x : α → ℝ) (j : ℕ) (t : Finset α) {i : α} (hi : i ∉ t) :
    ps x j (insert i t)ᶜ = ps x j tᶜ - (x i)^j := by
  rw [ps_compl,ps_compl]
  simp only [ps,Finset.sum_insert hi]
  ring

omit [Fintype α] [DecidableEq α] in
private theorem ps_lin3 (x : α → ℝ) (s : Finset α) (A B C : ℝ) :
    ∑ i ∈ s, (A*x i+B*(x i)^2+C*(x i)^3) =
    A*ps x 1 s+B*ps x 2 s+C*ps x 3 s := by
  simp only [ps,pow_one,Finset.sum_add_distrib,Finset.mul_sum]

theorem raw_three (k : ℕ) (hk : k ≤ Fintype.card α) (x : α → ℝ) (hx : ∑ i, x i = 0)
    (t : Finset α) :
    let d := Cnt (Fintype.card α) k
    let r := t.card
    raw k x 3 t = (diff₂ d r-diff₂ d (r+1))*(ps x 1 t)^3 +
      (diff d (r+1)+2*diff₂ d (r+1)-diff d (r+2))*ps x 1 t*ps x 2 tᶜ +
      (diff₂ d (r+1)-diff d (r+2))*ps x 3 tᶜ := by
  classical
  dsimp only
  let d := Cnt (Fintype.card α) k
  let A := ps x 1 t
  let B := ps x 2 tᶜ
  let X := diff₂ d (t.card+1)
  let Z := diff d (t.card+2)
  rw [raw_succ k x 2 t,raw_two k hk x hx]
  have he : ∑ i ∈ tᶜ, x i * raw k x 2 (insert i t) =
      (X*A^2+Z*B)*ps x 1 tᶜ + (2*X*A)*ps x 2 tᶜ + (X-Z)*ps x 3 tᶜ := by
    rw [← ps_lin3]
    apply Finset.sum_congr rfl
    intro i hi
    have hnot := mem_compl.mp hi
    rw [raw_two k hk x hx,card_insert_of_notMem hnot,ps_insert_compl x 2 t hnot]
    have hA : ps x 1 (insert i t) = x i+A := by simp [ps,A,hnot]
    rw [hA]
    change x i*(X*(x i+A)^2+Z*(B-(x i)^2)) = _
    ring
  rw [he,ps_compl x 1 t]
  have h0 : ps x 1 univ = 0 := by simpa [ps] using hx
  rw [h0]
  dsimp [A,B,X,Z,d]
  simp only [ps,pow_one]
  ring

/-- All four unnormalized slice moments for an arbitrary (not necessarily
unit-norm) centered population. No member of the k-slice is enumerated. -/
theorem centered_raw_moments (k : ℕ) (hk : k ≤ Fintype.card α) (x : α → ℝ)
    (hx : ∑ i, x i = 0) :
    let d := Cnt (Fintype.card α) k
    raw k x 1 ∅ = 0 ∧
    raw k x 2 ∅ = (d 1-d 2)*(∑ i, (x i)^2) ∧
    raw k x 3 ∅ = (d 1-3*d 2+2*d 3)*(∑ i, (x i)^3) ∧
    raw k x 4 ∅ = 3*(d 2-2*d 3+d 4)*(∑ i, (x i)^2)^2 +
      (d 1-7*d 2+12*d 3-6*d 4)*(∑ i, (x i)^4) := by
  classical
  dsimp only
  refine ⟨?_,?_,?_,?_⟩
  · simp [raw_one k hk x hx,ps]
  · simp [raw_two k hk x hx,ps,diff]
  · simp [raw_three k hk x hx,ps,diff₂,diff]
    left; ring
  · let d := Cnt (Fintype.card α) k
    let A := diff₂ d 1-diff₂ d 2
    let B := diff d 2+2*diff₂ d 2-diff d 3
    let C := diff₂ d 2-diff d 3
    let Q := ∑ i, (x i)^2
    let T := ∑ i, (x i)^3
    rw [raw_succ k x 3 ∅]
    simp only [Finset.sum_empty,zero_mul,zero_add,compl_empty,insert_empty_eq]
    have h₁ : ∑ i, x i * raw k x 3 {i} =
        ∑ i, ((A-B-C)*(x i)^4+(B*Q)*(x i)^2+(C*T)*x i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [raw_three k hk x hx,ps_compl,ps_compl]
      simp only [card_singleton,ps,sum_singleton,pow_one]
      change x i*(A*(x i)^3+B*(x i)*(Q-(x i)^2)+C*(T-(x i)^3)) = _
      ring
    rw [h₁,Finset.sum_add_distrib,Finset.sum_add_distrib,
      ← Finset.mul_sum,← Finset.mul_sum,← Finset.mul_sum,hx]
    dsimp [A,B,C,d,Q,T,diff₂,diff]
    ring
end ManickamMiklosSinghi.SevenK
