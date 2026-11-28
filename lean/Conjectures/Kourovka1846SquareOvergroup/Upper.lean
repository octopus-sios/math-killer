import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Simultaneous square roots in the swap extension

The extra bit records whether multiplication interchanges the two factors.
The diagonal embedding works for noncommutative groups as well.
-/

namespace Kourovka1846

universe u

/-- Two copies of the base group, extended by the involution that swaps them. -/
structure SwapHost (G : Type u) where
  swapped : Bool
  left : G
  right : G

namespace SwapHost

variable {G : Type u} [Group G]

private def prod : SwapHost G → SwapHost G → SwapHost G
  | ⟨false, a, b⟩, ⟨j, c, d⟩ => ⟨j, a * c, b * d⟩
  | ⟨true, a, b⟩, ⟨j, c, d⟩ => ⟨!j, a * d, b * c⟩

private def inv : SwapHost G → SwapHost G
  | ⟨false, a, b⟩ => ⟨false, a⁻¹, b⁻¹⟩
  | ⟨true, a, b⟩ => ⟨true, b⁻¹, a⁻¹⟩

instance : Group (SwapHost G) where
  mul := prod
  one := ⟨false, 1, 1⟩
  inv := inv
  mul_assoc := by
    intro x y z
    change prod (prod x y) z = prod x (prod y z)
    obtain ⟨i, a, b⟩ := x
    obtain ⟨j, c, d⟩ := y
    obtain ⟨k, e, f⟩ := z
    cases i <;> cases j <;> cases k <;> simp [prod, mul_assoc]
  one_mul := by change ∀ x, prod ⟨false, 1, 1⟩ x = x; rintro ⟨i, a, b⟩; simp [prod]
  mul_one := by change ∀ x, prod x ⟨false, 1, 1⟩ = x; rintro ⟨i, a, b⟩; cases i <;> simp [prod]
  inv_mul_cancel := by change ∀ x, prod (inv x) x = ⟨false, 1, 1⟩; rintro ⟨i, a, b⟩; cases i <;> simp [prod, inv]

private def coords (A : Type u) : SwapHost A ≃ Bool × A × A :=
  ⟨fun x => (x.swapped, x.left, x.right), fun x => ⟨x.1, x.2.1, x.2.2⟩,
    fun _ => rfl, fun _ => rfl⟩

instance {A : Type u} [Fintype A] : Fintype (SwapHost A) :=
  Fintype.ofEquiv _ (coords A).symm

theorem card (G : Type u) [Fintype G] :
    Fintype.card (SwapHost G) = 2 * (Fintype.card G) ^ 2 := by
  rw [Fintype.card_congr (coords G)]
  simp [Fintype.card_prod, pow_two]

/-- Embed on the diagonal in the unswapped coset. -/
def diagonal : G →* SwapHost G where
  toFun a := ⟨false, a, a⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem diagonal_injective : Function.Injective (diagonal (G := G)) := by
  intro x y h
  exact congrArg (SwapHost.left (G := G)) h

theorem diagonal_square (g : G) : ∃ h : SwapHost G, h ^ 2 = diagonal g := by
  refine ⟨⟨true, g, 1⟩, ?_⟩
  rw [pow_two]
  change (⟨false, g * 1, 1 * g⟩ : SwapHost G) = ⟨false, g, g⟩
  simp

end SwapHost

/-- The uniform upper bound from Kourovka Notebook Problem 18.46, with exact
host cardinality and a single embedding for all the square-root equations. -/
theorem square_overgroup_upper (G : Type u) [Group G] [Fintype G] :
    ∃ (H : Type u) (_ : Group H) (_ : Fintype H) (ι : G →* H),
      Function.Injective ι ∧ (∀ g : G, ∃ h : H, h ^ 2 = ι g) ∧
      Fintype.card H = 2 * (Fintype.card G) ^ 2 :=
  ⟨SwapHost G, inferInstance, inferInstance, SwapHost.diagonal,
    SwapHost.diagonal_injective, SwapHost.diagonal_square, SwapHost.card G⟩

end Kourovka1846

