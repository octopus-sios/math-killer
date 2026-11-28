import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace TaoForbidden
set_option maxHeartbeats 30000000
set_option maxRecDepth 64000
def expEntry : Fin 6 → Fin 6 → Nat := ![![0,0,0,0,0,0],
 ![0,0,1,1,2,2],
 ![0,1,0,2,2,1],
 ![0,1,2,0,1,2],
 ![0,2,2,1,0,1],
 ![0,2,1,2,1,0]]
def hit (i k j l : Fin 6) : Prop := (expEntry i j + expEntry k l) % 3 = (expEntry i l + expEntry k j) % 3
instance (i k j l : Fin 6) : Decidable (hit i k j l) := by unfold hit; infer_instance
def distinct6 (a b c d e f : Fin 6) : Prop := a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ a ≠ f ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧ b ≠ f ∧ c ≠ d ∧ c ≠ e ∧ c ≠ f ∧ d ≠ e ∧ d ≠ f ∧ e ≠ f
def onezero (a b c d e f : Fin 6) : Prop := hit 0 1 a b ∨ hit 0 2 a c ∨ hit 0 3 a d ∨ hit 0 4 a e ∨ hit 0 5 a f ∨ hit 1 2 b c ∨ hit 1 3 b d ∨ hit 1 4 b e ∨ hit 1 5 b f ∨ hit 2 3 c d ∨ hit 2 4 c e ∨ hit 2 5 c f ∨ hit 3 4 d e ∨ hit 3 5 d f ∨ hit 4 5 e f
instance (a b c d e f : Fin 6) : Decidable (distinct6 a b c d e f) := by unfold distinct6; infer_instance
instance (a b c d e f : Fin 6) : Decidable (onezero a b c d e f) := by unfold onezero; infer_instance
private theorem tab0 : ∀ b c d e f : Fin 6, distinct6 0 b c d e f → onezero 0 b c d e f := by decide +kernel
private theorem tab1 : ∀ b c d e f : Fin 6, distinct6 1 b c d e f → onezero 1 b c d e f := by decide +kernel
private theorem tab2 : ∀ b c d e f : Fin 6, distinct6 2 b c d e f → onezero 2 b c d e f := by decide +kernel
private theorem tab3 : ∀ b c d e f : Fin 6, distinct6 3 b c d e f → onezero 3 b c d e f := by decide +kernel
private theorem tab4 : ∀ b c d e f : Fin 6, distinct6 4 b c d e f → onezero 4 b c d e f := by decide +kernel
private theorem tab5 : ∀ b c d e f : Fin 6, distinct6 5 b c d e f → onezero 5 b c d e f := by decide +kernel
theorem tuple_obstruct (a b c d e f : Fin 6) : distinct6 a b c d e f → onezero a b c d e f := by
  fin_cases a
  · exact tab0 b c d e f
  · exact tab1 b c d e f
  · exact tab2 b c d e f
  · exact tab3 b c d e f
  · exact tab4 b c d e f
  · exact tab5 b c d e f
theorem every_permutation (p : Equiv.Perm (Fin 6)) : ∃ i k : Fin 6, i < k ∧ hit i k (p i) (p k) := by
  have hd : distinct6 (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) := by
    norm_num [distinct6, p.injective.ne_iff]
  have h := tuple_obstruct (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) hd
  unfold onezero at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact ⟨0, 1, by decide, h⟩
  · exact ⟨0, 2, by decide, h⟩
  · exact ⟨0, 3, by decide, h⟩
  · exact ⟨0, 4, by decide, h⟩
  · exact ⟨0, 5, by decide, h⟩
  · exact ⟨1, 2, by decide, h⟩
  · exact ⟨1, 3, by decide, h⟩
  · exact ⟨1, 4, by decide, h⟩
  · exact ⟨1, 5, by decide, h⟩
  · exact ⟨2, 3, by decide, h⟩
  · exact ⟨2, 4, by decide, h⟩
  · exact ⟨2, 5, by decide, h⟩
  · exact ⟨3, 4, by decide, h⟩
  · exact ⟨3, 5, by decide, h⟩
  · exact ⟨4, 5, by decide, h⟩
end TaoForbidden
