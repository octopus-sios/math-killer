import Mathlib.GroupTheory.Perm.Basic

/-!
# The permutation obstruction in Kourovka 18.46

One four-cycle and one two-cycle, with arbitrary fixed points, has no square
root in the full permutation group. The reduction from arbitrary small hosts
to such permutation groups uses CFSG and is not formalized here.
-/

namespace Kourovka1846

/-- A unique orbit of least period two prevents a square root. -/
theorem not_square_of_unique_pair {X : Type*} (g : Equiv.Perm X) (a b : X)
    (hab : a ≠ b) (ha : g a = b) (hb : g b = a)
    (onlyPair : ∀ t, g (g t) = t → g t ≠ t → t = a ∨ t = b) :
    ¬ ∃ h : Equiv.Perm X, h ^ 2 = g := by
  rintro ⟨h, hs⟩
  have sq (x : X) : h (h x) = g x := by
    change (h * h) x = g x
    rw [← pow_two, hs]
  have comm (x : X) : g (h x) = h (g x) := by
    rw [← sq (h x), ← sq x]
  have period : g (g (h a)) = h a := by rw [comm a, comm (g a), ha, hb]
  have moved : g (h a) ≠ h a := by
    rw [comm a, ha]
    exact fun e => hab (h.injective e).symm
  have hh : h (h a) = b := (sq a).trans ha
  rcases onlyPair (h a) period moved with e | e
  · rw [e, e] at hh
    exact hab hh
  · rw [e] at hh
    exact hab (h.injective (e.trans hh.symm))

private def turn : Equiv.Perm (Bool × Bool) where
  toFun p := (p.2, !p.1)
  invFun p := (!p.2, p.1)
  left_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl
  right_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

private def flip : Equiv.Perm Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv := by intro a; cases a <;> rfl
  right_inv := by intro a; cases a <;> rfl

/-- A four-cycle and a two-cycle, extended by fixed points. -/
def witness (X : Type*) : Equiv.Perm ((Bool × Bool) ⊕ (Bool ⊕ X)) :=
  turn.sumCongr (flip.sumCongr (Equiv.refl X))

theorem witness_not_square (X : Type*) :
    ¬ ∃ h : Equiv.Perm ((Bool × Bool) ⊕ (Bool ⊕ X)), h ^ 2 = witness X := by
  apply not_square_of_unique_pair (witness X) (.inr (.inl false)) (.inr (.inl true))
    (by intro he; cases he) rfl rfl
  intro t
  rcases t with ⟨a, b⟩ | (b | x)
  · cases a <;> cases b <;> intro he <;> cases he
  · cases b
    · exact fun _ _ => Or.inl rfl
    · exact fun _ _ => Or.inr rfl
  · exact fun _ hm => (hm rfl).elim

end Kourovka1846
