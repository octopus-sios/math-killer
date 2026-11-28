import Conjectures.MarcusDeOliveira.Displacement
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Ring

/-! Matrix-level displacement from the Hermitian stationarity commutator.
There is no assumption about the unknown second displacement (AD) or E. -/
noncomputable section
namespace MOCStationary
open Matrix Complex
open scoped Matrix BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
abbrev Mat (ι : Type*) := Matrix ι ι ℂ

def D (s : ℂ) (R : Mat ι) := (s/2) • R + (star s/2) • Rᴴ

private theorem two_sandwiches (H R : Mat ι) (s : ℂ) (h₁ : R*H=1) (h₂ : H*R=1) :
    Hᴴ*D s R*H = (s/2) • Hᴴ + (star s/2) • H ∧
    H*D s R*Hᴴ = (s/2) • Hᴴ + (star s/2) • H := by
  have h₃ : Hᴴ*Rᴴ=1 := by simpa using congrArg Matrix.conjTranspose h₁
  have h₄ : Rᴴ*Hᴴ=1 := by simpa using congrArg Matrix.conjTranspose h₂
  constructor
  · simp only [D,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul]
    rw [h₃,one_mul,Matrix.mul_assoc,h₁,mul_one]
  · simp only [D,mul_add,add_mul,Matrix.mul_smul,Matrix.smul_mul]
    rw [h₂,one_mul,Matrix.mul_assoc,h₄,mul_one]

private theorem offdiag (A T : Mat ι) (u v : ι → ℂ) (p q : ℂ) (hc : Commute A T)
    (hs : (A+diagonal u)*T*(A+diagonal v) = p • (A+diagonal u) + q • (A+diagonal v))
    (i j : ι) (hij : i ≠ j) :
    (A^2*T-(p+q) • A) i j + (u i+v j)*(A*T) i j + (u i*v j)*T i j = 0 := by
  have hh := congrArg (fun M : Mat ι => M i j) hs
  have hA : A*T*A=A^2*T := by rw [mul_assoc,← hc.eq,pow_two,mul_assoc]
  have hd : diagonal u*T*A = diagonal u*(A*T) := by rw [mul_assoc,← hc.eq]
  simp [mul_add,add_mul,hA,hd,Matrix.mul_diagonal,Matrix.diagonal_mul,Matrix.diagonal_apply,hij] at hh
  simp only [Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  linear_combination hh

private theorem mean_real (s : ℂ) : s/2 + star s/2 = (s.re : ℂ) := by
  apply Complex.ext <;> simp [Complex.star_def,Complex.add_re,Complex.add_im] <;> ring

/-- From the two-sided inverse of H=A+diag b and the stationarity condition
[A,D]=0 to the actual three displacement slopes. Works in arbitrary order.
Only the two chosen imaginary parts need to be nonzero and different. -/
theorem stationary_entries (A R : Mat ι) (b : ι → ℂ) (s : ℂ) (ha : A.IsHermitian)
    (h₁ : R*(A+diagonal b)=1) (h₂ : (A+diagonal b)*R=1) (hc : Commute A (D s R))
    (i j : ι) (hi : (b i).im ≠ 0) (hj : (b j).im ≠ 0) (hy : (b i).im ≠ (b j).im) :
    ∃ K : ℂ, D s R i j = ((1/(b i).im-1/(b j).im : ℝ) : ℂ)*K ∧
      (A*D s R) i j = -(((b i).re/(b i).im-(b j).re/(b j).im : ℝ) : ℂ)*K ∧
      (A^2*D s R-(s.re : ℂ) • A) i j =
        ((((b i).re*(b i).re+(b i).im*(b i).im)/(b i).im-
          ((b j).re*(b j).re+(b j).im*(b j).im)/(b j).im : ℝ) : ℂ)*K := by
  have hij : i ≠ j := by intro h; subst j; exact hy rfl
  let bb (k : ι) := star (b k)
  have ht : (A+diagonal b)ᴴ = A+diagonal bb := by
    rw [Matrix.conjTranspose_add,ha.eq]
    congr 1
    ext i j
    by_cases h : i=j <;> simp [bb,Matrix.conjTranspose_apply,Matrix.diagonal_apply,h,eq_comm]
  obtain ⟨one,two⟩ := two_sandwiches _ _ s h₁ h₂
  rw [ht] at one two
  have eq1 := offdiag A (D s R) bb b (s/2) (star s/2) hc one i j hij
  have eq2 := offdiag A (D s R) b bb (star s/2) (s/2) hc (two.trans (add_comm _ _)) i j hij
  rw [mean_real s] at eq1
  rw [add_comm (star s/2) (s/2),mean_real s] at eq2
  exact MOCDisplacement.slopes _ _ _ _ _ hi hj hy eq1 eq2
end MOCStationary
