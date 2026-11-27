import Mathlib.LinearAlgebra.Matrix.Permanent
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Cycle estimate used in the order-four proof of Yuan--Parrilo's sphere inequality.
The statement here concerns actual permanents, not the remaining analytic estimates. -/
namespace YuanParriloPermanentSphere
open scoped BigOperators

private theorem expandFirst {R : Type*} [CommSemiring R] {m : ℕ}
    (M : Matrix (Fin (m+2)) (Fin (m+2)) R) :
    M.permanent = ∑ j, M j 0 * (M.submatrix j.succAbove Fin.succ).permanent := by
  classical
  rw [Matrix.permanent, ← Equiv.Perm.decomposeFin'.symm.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.permanent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Fin.prod_univ_succ]
  simp [Matrix.submatrix]

private theorem expand2 (M : Matrix (Fin 2) (Fin 2) ℝ) :
    M.permanent = M 0 0 * (M.submatrix (0 : Fin 2).succAbove Fin.succ).permanent
        + M 1 0 * (M.submatrix (1 : Fin 2).succAbove Fin.succ).permanent :=
  (expandFirst (m := 0) M).trans (Fin.sum_univ_two _)

private theorem expand3 (M : Matrix (Fin 3) (Fin 3) ℝ) :
    M.permanent = M 0 0 * (M.submatrix (0 : Fin 3).succAbove Fin.succ).permanent
        + M 1 0 * (M.submatrix (1 : Fin 3).succAbove Fin.succ).permanent
        + M 2 0 * (M.submatrix (2 : Fin 3).succAbove Fin.succ).permanent :=
  (expandFirst (m := 1) M).trans (Fin.sum_univ_three _)

private theorem expand4 (M : Matrix (Fin 4) (Fin 4) ℝ) :
    M.permanent = M 0 0 * (M.submatrix (0 : Fin 4).succAbove Fin.succ).permanent
        + M 1 0 * (M.submatrix (1 : Fin 4).succAbove Fin.succ).permanent
        + M 2 0 * (M.submatrix (2 : Fin 4).succAbove Fin.succ).permanent
        + M 3 0 * (M.submatrix (3 : Fin 4).succAbove Fin.succ).permanent :=
  (expandFirst (m := 2) M).trans (Fin.sum_univ_four _)

private def edges (a A b B c C : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, a, b, c; a, 1, C, B; b, C, 1, A; c, B, A, 1]

private theorem edge_expansion (a A b B c C : ℝ) :
    (edges a A b B c C).permanent =
      1 + (a^2+A^2+b^2+B^2+c^2+C^2)
        + 2*(a*b*C+a*B*c+A*b*c+A*B*C)
        + (a*A+b*B+c*C)^2 := by
  simp only [expand4, expand3, expand2, Matrix.permanent_unique]
  change (1 * (1 * (1 * 1 + A * A) + C * (C * 1 + A * B) + B * (C * A + 1 * B)) + a * (a * (1 * 1 + A * A) + C * (b * 1 + A * c) + B * (b * A + 1 * c)) + b * (a * (C * 1 + A * B) + 1 * (b * 1 + A * c) + B * (b * B + C * c)) + c * (a * (C * A + 1 * B) + 1 * (b * A + 1 * c) + C * (b * B + C * c))) = _
  ring

private theorem edge_estimate (a A b B c C s : ℝ)
    (ha : 0 ≤ a) (hA : 0 ≤ A) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hc : 0 ≤ c) (hC : 0 ≤ C)
    (haA : a+A ≤ s) (hbB : b+B ≤ s) (hcC : c+C ≤ s)
    (hs : s+s^2 ≤ 1) :
    (edges a A b B c C).permanent ≤ (1+s)^2 := by
  have hs0 : 0 ≤ s := by linarith
  have pa := mul_self_le_mul_self (by positivity : 0 ≤ a+A) haA
  have pb := mul_self_le_mul_self (by positivity : 0 ≤ b+B) hbB
  have pc := mul_self_le_mul_self (by positivity : 0 ≤ c+C) hcC
  let p := a*A+b*B+c*C
  have hp0 : 0 ≤ p := by dsimp [p]; positivity
  have hp : p ≤ 2 := by
    dsimp [p]
    nlinarith [sq_nonneg (a-A), sq_nonneg (b-B), sq_nonneg (c-C)]
  have hq := mul_nonneg hp0 (sub_nonneg.mpr hp)
  have h3 : (a+A)*(b+B)*(c+C) ≤ s*s*s :=
    mul_le_mul (mul_le_mul haA hbB (by positivity) hs0) hcC (by positivity) (by positivity)
  have hT : a*b*C+a*B*c+A*b*c+A*B*C ≤ (a+A)*(b+B)*(c+C) := by
    nlinarith [mul_nonneg (mul_nonneg ha hb) hc, mul_nonneg (mul_nonneg ha hB) hC,
      mul_nonneg (mul_nonneg hA hb) hC, mul_nonneg (mul_nonneg hA hB) hc]
  rw [edge_expansion]
  dsimp [p] at hq
  nlinarith [mul_nonneg hs0 (sub_nonneg.mpr hs)]

/-- With unit diagonal and symmetric entrywise norms, any complex matrix of order four
satisfies a matching bound when its three complementary pairs of magnitudes have small sums.
No positivity assumption on the matrix is needed. -/
theorem permanent_four_matching (M : Matrix (Fin 4) (Fin 4) ℂ) {s : ℝ}
    (diag : ∀ i, ‖M i i‖ = 1)
    (symm : ∀ i j, ‖M i j‖ = ‖M j i‖)
    (h₁ : ‖M 0 1‖ + ‖M 2 3‖ ≤ s)
    (h₂ : ‖M 0 2‖ + ‖M 1 3‖ ≤ s)
    (h₃ : ‖M 0 3‖ + ‖M 1 2‖ ≤ s)
    (hs : s+s^2 ≤ 1) :
    ‖M.permanent‖ ≤ (1+s)^2 := by
  let N : Matrix (Fin 4) (Fin 4) ℝ := fun i j => ‖M i j‖
  have hN : N = edges ‖M 0 1‖ ‖M 2 3‖ ‖M 0 2‖ ‖M 1 3‖ ‖M 0 3‖ ‖M 1 2‖ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [N, edges, diag] <;> apply symm
  calc
    ‖M.permanent‖ ≤ ∑ σ : Equiv.Perm (Fin 4), ‖∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ = N.permanent := by simp [Matrix.permanent, N, norm_prod]
    _ ≤ (1+s)^2 := by
      rw [hN]
      exact edge_estimate _ _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _)
        (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) h₁ h₂ h₃ hs

end YuanParriloPermanentSphere
