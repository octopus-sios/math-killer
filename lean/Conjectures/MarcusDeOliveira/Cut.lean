import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Complex Matrix
open scoped ComplexConjugate Matrix
noncomputable section
namespace MOCCut
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Purely algebraic cut recovery. No pseudoinverse, spectral projection or
hypothesis that D is invertible is needed. P can be any commuting projector
(or even an arbitrary matrix). -/
theorem recover_cut (A D P : Matrix ι ι ℂ) (c : ℂ) (hc : c ≠ 0)
    (had : Commute A D) (hd : Commute P D) (hm : Commute P (A*D))
    (he : Commute P (A^2*D-c • A)) : Commute P A := by
  have hsq : Commute P (A^2*D) := by
    change P * (A^2*D) = (A^2*D) * P
    calc P * (A^2*D) = P*(A*(A*D)) := by simp only [pow_two,mul_assoc]
         _ = P*(A*(D*A)) := congrArg (fun Z => P*(A*Z)) had.eq
         _ = P*(A*D)*A := by simp only [mul_assoc]
         _ = (A*D)*P*A := by rw [hm.eq]
         _ = A*((D*P)*A) := by simp only [mul_assoc]
         _ = A*((P*D)*A) := by rw [hd.eq]
         _ = A*(P*(A*D)) := by simp only [mul_assoc,had.eq]
         _ = (A^2*D)*P := by rw [hm.eq]; simp only [pow_two,mul_assoc]
  have hs : Commute P (c • A) := by simpa using hsq.sub_right he
  change P*(c • A) = (c • A)*P at hs
  rw [Matrix.mul_smul,Matrix.smul_mul] at hs
  have h := congrArg (fun M : Matrix ι ι ℂ => c⁻¹ • M) hs
  change P*A = A*P
  simpa [smul_smul,hc] using h

end MOCCut
