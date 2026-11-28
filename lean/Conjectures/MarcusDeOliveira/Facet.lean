import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxHeartbeats 3500000
namespace MOCFacet
open Matrix
open scoped Matrix BigOperators
abbrev I4 := Fin 4
abbrev M4 := Matrix I4 I4 ℚ

def minor2 (A : M4) (i j k : I4) : ℚ := A 0 j * A i k - A 0 k * A i j

/-- tr(S) + Q₀₁ − Q₁₀ with the pair representatives 01,02,03. -/
def facet (A : M4) : ℚ :=
  (A 0 0 ^ 2 + A 1 1 ^ 2 + A 2 2 ^ 2 + A 3 3 ^ 2) + (minor2 A 1 0 2)^2 + (minor2 A 1 1 3)^2 -
  ((minor2 A 2 0 1)^2 + (minor2 A 2 2 3)^2)

def witness : M4 := (1/7 : ℚ) •
    (Matrix.of ![![1,-4,-4,-4], ![4,1,-4,4], ![4,4,1,-4], ![4,-4,4,1]])

theorem special_orthogonal : witness * witness.transpose = 1 ∧ witness.det = 1 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [witness, Matrix.of_apply, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]
  · rw [Matrix.det_succ_row_zero]
    norm_num [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove, witness, Matrix.of_apply]

theorem facet_breach : facet witness = -316/2401 := by
  norm_num [facet,witness,Matrix.of_apply,minor2,Fin.sum_univ_succ]

/-- Kernel-decided finite table in rational coordinates, including every
labeled row permutation. Distinctness alone certifies bijectivity here. -/
theorem permutations_nonnegative (p : Equiv.Perm I4) : 0 ≤ facet (p.permMatrix ℚ) := by
  let A (r : I4 → I4) : M4 := fun i j => if r i=j then 1 else 0
  have chk : ∀ a b c d : I4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      0 ≤ facet (A ![a,b,c,d]) := by
    intro a b c d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
      norm_num [A,facet,minor2,Fin.sum_univ_succ]
  have ht : (p.permMatrix ℚ) = A ![p 0,p 1,p 2,p 3] := by
    ext i j; fin_cases i <;> simp [A,PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_def] <;> split <;> simp_all
  rw [ht]
  exact chk _ _ _ _ (p.injective.ne (by decide : (0:I4) ≠ 1)) (p.injective.ne (by decide : (0:I4) ≠ 2)) (p.injective.ne (by decide : (0:I4) ≠ 3)) (p.injective.ne (by decide : (1:I4) ≠ 2)) (p.injective.ne (by decide : (1:I4) ≠ 3)) (p.injective.ne (by decide : (2:I4) ≠ 3))

end MOCFacet
