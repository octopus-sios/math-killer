import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Matrix
open scoped Matrix BigOperators
noncomputable section
namespace MOCProjective
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def value (a b : ι → ℂ) (U : Matrix ι ι ℂ) : ℂ :=
  (diagonal a + U*diagonal b*Uᴴ).det

def vertex (a b : ι → ℂ) (p : Equiv.Perm ι) : ℂ := ∏ i, (a i + b (p i))

def MOC (a b : ι → ℂ) (U : Matrix ι ι ℂ) : Prop :=
  value a b U ∈ convexHull ℝ (Set.range (vertex a b))

private theorem pencil (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : Uᴴ*U=1) :
    value a b U * U.det = (Matrix.of fun i j => (a i + b j)*U i j).det := by
  rw [value, ← det_mul, add_mul, Matrix.mul_assoc (U*diagonal b), hU, mul_one]
  congr 1
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, add_mul, mul_comm] <;> ring

/-- A separable rescaling of the sum table rescales the determinant and all
vertices by *one* scalar. Real convex-hull membership is therefore invariant. -/
theorem scale_table (a b a' b' l r : ι → ℂ) (U : Matrix ι ι ℂ) (hU : Uᴴ*U=1)
    (hl : ∀ i, l i ≠ 0) (hr : ∀ j, r j ≠ 0)
    (hs : ∀ i j, a' i+b' j = l i*(a i+b j)*r j) :
    MOC a' b' U ↔ MOC a b U := by
  classical
  let k := (∏ i, l i) * ∏ j, r j
  have hk : k ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hl i)
      (Finset.prod_ne_zero_iff.mpr fun j _ => hr j)
  let L : ℂ →ₗ[ℝ] ℂ :=
    { toFun := (k * ·)
      map_add' := fun x y => mul_add k x y
      map_smul' := by intro t x; simp [Complex.real_smul] <;> ring }
  have hv (p : Equiv.Perm ι) : vertex a' b' p = L (vertex a b p) := by
    change (∏ i, (a' i+b' (p i))) = k * ∏ i, (a i + b (p i))
    simp_rw [hs, Finset.prod_mul_distrib]
    rw [Equiv.prod_comp p r]
    dsimp [k] <;> ring
  have hu0 : U.det ≠ 0 := by
    have h := congrArg Matrix.det hU
    rw [det_mul, det_one] at h
    intro hz; simp [hz] at h
  have he : (Matrix.of fun i j => (a' i+b' j)*U i j) =
      diagonal l * (Matrix.of fun i j => (a i+b j)*U i j) * diagonal r := by
    ext i j
    simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hs] <;> ring
  have hd : value a' b' U = L (value a b U) := by
    change value a' b' U = k * value a b U
    apply mul_right_cancel₀ hu0
    rw [mul_assoc, pencil a' b' U hU, pencil a b U hU, he, det_mul, det_mul,
      det_diagonal, det_diagonal]
    dsimp [k] <;> ring
  have hrange : Set.range (vertex a' b') = L '' Set.range (vertex a b) := by
    ext z
    constructor
    · rintro ⟨p,rfl⟩; exact ⟨_,⟨p,rfl⟩,(hv p).symm⟩
    · rintro ⟨_,⟨p,rfl⟩,rfl⟩; exact ⟨p,hv p⟩
  unfold MOC
  rw [hd, hrange, ← L.image_convexHull]
  constructor
  · rintro ⟨z,hz,heq⟩
    have hez : z = value a b U := mul_left_cancel₀ hk heq
    simpa [hez] using hz
  · exact fun h => ⟨_,h,rfl⟩

/-- Exact PGL₂ invariance away from poles, in the sum convention (f(a),−f(−b)).
No reality, distinctness, invertibility of A+B, or spectral genericity hypotheses. -/
theorem mobius (a b : ι → ℂ) (U : Matrix ι ι ℂ) (hU : Uᴴ*U=1)
    (p q r s : ℂ) (hΔ : p*s-q*r ≠ 0)
    (ha : ∀ i, r*a i+s ≠ 0) (hb : ∀ j, s-r*b j ≠ 0) :
    MOC (fun i => (p*a i+q)/(r*a i+s))
      (fun j => (p*b j-q)/(s-r*b j)) U ↔ MOC a b U := by
  apply scale_table a b _ _ (fun i => (p*s-q*r)/(r*a i+s)) (fun j => (s-r*b j)⁻¹) U hU
  · exact fun i => div_ne_zero hΔ (ha i)
  · exact fun j => inv_ne_zero (hb j)
  · intro i j
    try dsimp only
    rw [div_add_div _ _ (ha i) (hb j)]
    simp only [div_eq_mul_inv, mul_inv_rev] <;> ring

end MOCProjective
