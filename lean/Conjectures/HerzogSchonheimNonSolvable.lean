import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod

/-!
The finite counting step of the relative-index criterion. The `U i` are
the quotient images of non-universal parts; at each quotient point of
`A`, the local block sizes add up to the size `n` of a fibre. Distinct
global block sizes force distinct (local size, image size) pairs.
The group-theoretic reduction and the classification are in the written proof.
-/

namespace HerzogSchonheimNonSolvable

/-- Area of a filled set of fibres is bounded by the product of the two
distinct size sums. No disjointness of the projected sets is assumed. -/
theorem filled_fiber_capacity {ι α : Type*} [DecidableEq α]
    (I : Finset ι) (A : Finset α) (U : ι → Finset α) (s : ι → ℕ)
    (L H : Finset ℕ) (n : ℕ)
    (inside : ∀ i ∈ I, U i ⊆ A)
    (filled : ∀ a ∈ A, (∑ i ∈ I, if a ∈ U i then s i else 0) = n)
    (localSize : ∀ i ∈ I, s i ∈ L)
    (imageSize : ∀ i ∈ I, (U i).card ∈ H)
    (distinct : Set.InjOn (fun i => s i * (U i).card) (I : Set ι)) :
    n * A.card ≤ (∑ l ∈ L, l) * (∑ h ∈ H, h) := by
  classical
  let P : ι → ℕ × ℕ := fun i => (s i, (U i).card)
  have inj : Set.InjOn P (I : Set ι) := by
    intro i hi j hj hij
    exact distinct hi hj (congrArg (fun x : ℕ × ℕ => x.1 * x.2) hij)
  have sub : I.image P ⊆ L ×ˢ H := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_product.mpr ⟨localSize i hi, imageSize i hi⟩
  have row (i : ι) (hi : i ∈ I) :
      (∑ a ∈ A, if a ∈ U i then s i else 0) = s i * (U i).card := by
    have hf : A.filter (fun a => a ∈ U i) = U i := by
      ext a
      exact Finset.mem_filter.trans ⟨And.right, fun h => ⟨inside i hi h, h⟩⟩
    rw [← Finset.sum_filter, hf]
    simp [Nat.mul_comm]
  calc
    n * A.card = ∑ _a ∈ A, n := by simp [Nat.mul_comm]
    _ = ∑ a ∈ A, ∑ i ∈ I, if a ∈ U i then s i else 0 :=
      Finset.sum_congr rfl (fun a ha => (filled a ha).symm)
    _ = ∑ i ∈ I, ∑ a ∈ A, if a ∈ U i then s i else 0 := Finset.sum_comm
    _ = ∑ i ∈ I, s i * (U i).card := Finset.sum_congr rfl row
    _ = ∑ x ∈ I.image P, x.1 * x.2 := by
      rw [Finset.sum_image inj]
    _ ≤ ∑ x ∈ L ×ˢ H, x.1 * x.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _)
    _ = (∑ l ∈ L, l) * (∑ h ∈ H, h) := by
      simp [Finset.sum_product, Finset.sum_mul, Finset.mul_sum] <;> exact Finset.sum_comm

end HerzogSchonheimNonSolvable
