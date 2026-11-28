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
namespace MOCDisplacement

private theorem slope_polynomial (x y X Y : ℝ) (hy : y ≠ 0) (hY : Y ≠ 0) :
    let z := Complex.mk x y
    let w := Complex.mk X Y
    let d : ℂ := (1/y-1/Y : ℝ)
    let p : ℂ := (x/y-X/Y : ℝ)
    let q : ℂ := ((x*x+y*y)/y - (X*X+Y*Y)/Y : ℝ)
    q - (star z + w)*p + (star z*w)*d = 0 ∧
    q - (z + star w)*p + (z*star w)*d = 0 := by
  dsimp only
  constructor <;> apply Complex.ext <;>
    simp [Complex.star_def, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im] <;> field_simp [hy,hY] <;> ring

/-- The actual elimination of the two off-diagonal matrix equations. Entries
are complex; no cancellation of a general complex eigenvalue difference out
of a conjugate pair is used. -/
theorem slopes (z w E G D : ℂ) (hz : z.im ≠ 0) (hw : w.im ≠ 0)
    (hne : z.im ≠ w.im)
    (h₁ : E+(star z + w)*G + (star z*w)*D = 0)
    (h₂ : E+(z + star w)*G + (z*star w)*D = 0) :
    ∃ K : ℂ, D = ((1/z.im-1/w.im : ℝ) : ℂ)*K ∧
      G = -((z.re/z.im-w.re/w.im : ℝ) : ℂ)*K ∧
      E = (((z.re*z.re+z.im*z.im)/z.im-(w.re*w.re+w.im*w.im)/w.im : ℝ) : ℂ)*K := by
  let d : ℂ := (1/z.im-1/w.im : ℝ)
  let p : ℂ := (z.re/z.im-w.re/w.im : ℝ)
  let q : ℂ := ((z.re*z.re+z.im*z.im)/z.im-(w.re*w.re+w.im*w.im)/w.im : ℝ)
  have hdreal : (1/z.im-1/w.im : ℝ) ≠ 0 := by
    intro h
    field_simp [hz,hw] at h
    apply hne
    linarith
  have hd : d ≠ 0 := by dsimp only [d]; exact_mod_cast hdreal
  let K := D / d
  have hD : D=d*K := by dsimp [K]; field_simp
  refine ⟨K,hD,?_⟩
  obtain ⟨p1,p2⟩ := slope_polynomial z.re z.im w.re w.im hz hw
  change q - (star z+w)*p + (star z*w)*d = 0 at p1
  change q - (z+star w)*p + (z*star w)*d = 0 at p2
  have hcoef : star z+w - (z+star w) ≠ 0 := by
    intro hc
    have h := congrArg Complex.im hc
    simp [Complex.star_def] at h
    exact hne (by linarith)
  rw [hD] at h₁ h₂
  have hzprod : (star z+w - (z+star w))*(G+p*K) = 0 := by
    linear_combination h₁ - h₂ - K*p1 + K*p2
  have hG : G = -p*K := by
    have := (mul_eq_zero.mp hzprod).resolve_left hcoef
    linear_combination this
  refine ⟨hG,?_⟩
  rw [hG] at h₁
  linear_combination h₁ - K*p1

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
/-- Every real-slope pencil of I,D,AD,A²D−cA commutes with D,
including the specific pencil isolating the exceptional point. -/
theorem commuting_star (A D : Matrix ι ι ℂ) (h : Commute A D) (c s t v w : ℂ) :
    Commute D (s • (1 : Matrix ι ι ℂ) + t • D + v • (A*D) + w • (A^2*D-c • A)) := by
  have h₂ : Commute D (A*D) := h.symm.mul_right (Commute.refl D)
  have h₃ : Commute D (A^2*D) := (h.symm.pow_right 2).mul_right (Commute.refl D)
  exact ((((Commute.one_right D).smul_right s).add_right ((Commute.refl D).smul_right t)).add_right
    (h₂.smul_right v)).add_right ((h₃.sub_right (h.symm.smul_right c)).smul_right w)

end MOCDisplacement
