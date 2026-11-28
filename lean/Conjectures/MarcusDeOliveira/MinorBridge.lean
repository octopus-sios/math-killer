import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! All compound marginals follow from a spectrum-independent determinant
identity by testing two complementary-rank orthogonal projections. -/
noncomputable section
namespace MOCMinorBridge
open Matrix Complex
open scoped Matrix BigOperators

variable {m n α κ : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype α] [DecidableEq α] [Fintype κ]

private def p₀ : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks (0 : Matrix m m ℂ) (0 : Matrix m n ℂ) (0 : Matrix n m ℂ) (1 : Matrix n n ℂ)
private def p₁ : Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks (1 : Matrix m m ℂ) (0 : Matrix m n ℂ) (0 : Matrix n m ℂ) (0 : Matrix n n ℂ)

private theorem block (U : Matrix (m ⊕ n) (m ⊕ n) ℂ) :
    (p₀ + U * p₁ * Uᴴ).det = (normSq U.toBlocks₁₁.det : ℂ) := by
  have aux (A : Matrix m m ℂ) (B : Matrix m n ℂ) (C : Matrix n m ℂ) (D : Matrix n n ℂ) :
      (p₀ + fromBlocks A B C D * p₁ * (fromBlocks A B C D)ᴴ).det = (normSq A.det : ℂ) := by
    let S := fromBlocks A (0 : Matrix m n ℂ) C (1 : Matrix n n ℂ)
    have eqn : p₀ + fromBlocks A B C D * p₁ * (fromBlocks A B C D)ᴴ = S*Sᴴ := by
      simp [p₀,p₁,S,fromBlocks_conjTranspose,fromBlocks_multiply,fromBlocks_add,add_comm]
    rw [eqn,det_mul,det_conjTranspose]
    simp [S,det_fromBlocks_zero₁₂,Complex.star_def,Complex.mul_conj]
  simpa only [fromBlocks_toBlocks] using aux U.toBlocks₁₁ U.toBlocks₁₂ U.toBlocks₂₁ U.toBlocks₂₂

private def a₀ (e : m ⊕ n ≃ α) (i : α) : ℂ := Sum.elim (fun _ => 0) (fun _ => 1) (e.symm i)
private def b₁ (f : m ⊕ n ≃ α) (j : α) : ℂ := Sum.elim (fun _ => 1) (fun _ => 0) (f.symm j)

/-- The energy of the selected minor; e and f independently order the row
and column indices. Their first summands are the selected sets. -/
def energy (U : Matrix α α ℂ) (e f : m ⊕ n ≃ α) : ℝ :=
  normSq (U.submatrix e f).toBlocks₁₁.det

private theorem projection (U : Matrix α α ℂ) (e f : m ⊕ n ≃ α) :
    (diagonal (a₀ e) + U*diagonal (b₁ f)*Uᴴ).det = (energy U e f : ℂ) := by
  have hA : (diagonal (a₀ e)).submatrix e e = p₀ := by
    rw [submatrix_diagonal_equiv]
    ext i j; cases i <;> cases j <;>
      simp [a₀,p₀,diagonal_apply,Matrix.one_apply,Function.comp_apply]
  have hB : (diagonal (b₁ f)).submatrix f f = p₁ := by
    rw [submatrix_diagonal_equiv]
    ext i j; cases i <;> cases j <;>
      simp [b₁,p₁,diagonal_apply,Matrix.one_apply,Function.comp_apply]
  have he : (diagonal (a₀ e) + U*diagonal (b₁ f)*Uᴴ).submatrix e e =
      p₀ + U.submatrix e f * p₁ * (U.submatrix e f)ᴴ := by
    change (diagonal (a₀ e)).submatrix e e + (U*diagonal (b₁ f)*Uᴴ).submatrix e e = _
    rw [hA,← hB,conjTranspose_submatrix,submatrix_mul_equiv,submatrix_mul_equiv]
  have hh := congrArg Matrix.det he
  simpa only [det_submatrix_equiv_self,block,energy] using hh

private theorem perm_diag (p : Equiv.Perm α) (a b : α → ℂ) :
    (diagonal a + p.permMatrix ℂ * diagonal b * (p.permMatrix ℂ)ᴴ).det =
      ∏ i, (a i+b (p i)) := by
  let P := p.permMatrix ℂ
  have hp : P*Pᴴ = 1 := by
    ext i j
    by_cases h : i = j
    · subst j; simp [P,Matrix.mul_apply,Matrix.conjTranspose_apply,PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply,Option.mem_def,ite_mul,Equiv.symm_apply_eq,Matrix.one_apply]
    · have hp' := p.injective.ne h
      simp [P,Matrix.mul_apply,Matrix.conjTranspose_apply,PEquiv.toMatrix_apply,
        Equiv.toPEquiv_apply,Option.mem_def,ite_mul,Equiv.symm_apply_eq,h,hp',Ne.symm hp',Matrix.one_apply]
  have he : P*diagonal b = diagonal (b ∘ p)*P := by
    ext i j
    by_cases h : p i = j <;> simp [P,Matrix.mul_diagonal,Matrix.diagonal_mul,
      PEquiv.toMatrix_apply,Equiv.toPEquiv_apply,Option.mem_def,h]
  change (diagonal a + P*diagonal b*Pᴴ).det = _
  rw [he,Matrix.mul_assoc,hp,mul_one,diagonal_add,det_diagonal] <;> rfl

/-- A *single* spectral law forces *every* minor-square marginal of that
same law. This does not follow from pointwise membership with weights allowed
to vary with a,b. No unitary hypothesis is needed for the extraction. -/
theorem all_minors (U : Matrix α α ℂ) (w : κ → ℝ) (p : κ → Equiv.Perm α)
    (law : ∀ a b : α → ℂ, (diagonal a + U * diagonal b * Uᴴ).det =
      ∑ k, w k • ∏ i, (a i + b (p k i))) (e f : m ⊕ n ≃ α) :
    energy U e f = ∑ k, w k * energy ((p k).permMatrix ℂ) e f := by
  have h := law (a₀ e) (b₁ f)
  rw [projection] at h
  have hh (k : κ) : ∏ i, (a₀ e i+b₁ f (p k i)) = (energy ((p k).permMatrix ℂ) e f : ℂ) :=
    (perm_diag (p k) _ _).symm.trans (projection _ _ _)
  simp_rw [hh] at h
  apply Complex.ofReal_injective
  simpa [Complex.real_smul] using h

end MOCMinorBridge
