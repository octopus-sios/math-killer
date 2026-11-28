import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open Matrix Complex
open scoped Matrix ComplexConjugate BigOperators

open Matrix Finset
open scoped BigOperators

namespace MOCTransport

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Linear cost of a transport plan. -/
noncomputable def charge (C : n → n → ℂ) (M : Matrix n n ℝ) : ℂ :=
  ∑ i, ∑ j, M i j • C i j

private theorem charge_perm (C : n → n → ℂ) (p : Equiv.Perm n) :
    charge C (p.permMatrix ℝ) = ∑ i, C i (p i) := by
  classical
  simp [charge, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, ite_smul]

/-- Scaled Birkhoff on the one-forbidden-entry face. Missing mass goes to zero.
The costs are arbitrary; the support restriction is proved, not assumed. -/
theorem face (C : n → n → ℂ) (M : Matrix n n ℝ) (r c : n) (s : ℝ)
    (hs : 0 ≤ s) (hs' : s ≤ 1) (hM : ∀ i j, 0 ≤ M i j)
    (hr : ∀ i, ∑ j, M i j = s) (hc : ∀ j, ∑ i, M i j = s) (hz : M r c = 0)
    (K : Set ℂ) (hK : Convex ℝ K) (h0 : 0 ∈ K)
    (hp : ∀ p : Equiv.Perm n, p r ≠ c → (∑ i, C i (p i)) ∈ K) :
    charge C M ∈ K := by
  classical
  obtain ⟨N,hN,rfl⟩ := (exists_mem_doublyStochastic_eq_smul_iff hs).2 ⟨hM,hr,hc⟩
  by_cases hsz : s = 0
  · simpa [hsz, charge] using h0
  obtain ⟨w,hw,hw1,hwN⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hN
  have hNrc : N r c = 0 := (mul_eq_zero.mp hz).resolve_left hsz
  have hcoord (i j : n) : ∑ p : Equiv.Perm n, w p * (p.permMatrix ℝ i j) = N i j := by
    simpa [Matrix.sum_apply, Matrix.smul_apply] using congrArg (fun A : Matrix n n ℝ => A i j) hwN
  have hterm := hcoord r c
  rw [hNrc, sum_eq_zero_iff_of_nonneg (fun p _ => mul_nonneg (hw p)
      (nonneg_of_mem_doublyStochastic permMatrix_mem_doublyStochastic))] at hterm
  have hgood (p : Equiv.Perm n) (hnz : w p ≠ 0) : p r ≠ c := by
    intro hp'
    have hh := hterm p (mem_univ p)
    exact hnz (by simpa [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def,hp'] using hh)
  let z (p : Equiv.Perm n) : ℂ := if w p = 0 then 0 else charge C (p.permMatrix ℝ)
  have hzK (p : Equiv.Perm n) : z p ∈ K := by
    by_cases hh : w p = 0
    · simpa [z, hh] using h0
    · simpa [z, hh, charge_perm] using hp p (hgood p hh)
  have hmix : (∑ p, w p • z p) ∈ K :=
    hK.sum_mem (fun p _ => hw p) hw1 (fun p _ => hzK p)
  have hu (p : Equiv.Perm n) : w p • z p = w p • charge C (p.permMatrix ℝ) := by
    by_cases h : w p = 0 <;> simp [h, z]
  have hlin : charge C N = ∑ p, w p • z p := by
    simp_rw [hu, charge, ← hcoord, sum_smul, smul_sum, mul_smul]
    conv_rhs => rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_comm]
  have hscaled : charge C (s • N) = s • charge C N := by
    simp [charge, smul_sum, Matrix.smul_apply, mul_smul]
  rw [hscaled, hlin]
  simpa using hK hmix h0 hs (sub_nonneg.mpr hs') (show s + (1-s) = 1 by ring)

end MOCTransport
noncomputable section

namespace MOCCollision

abbrev I4 := Fin 4
abbrev Mat := Matrix I4 I4 ℂ

set_option maxRecDepth 5000
set_option maxHeartbeats 4500000

/-- Leibniz expansion cached once for four-by-four matrices. -/
theorem det_four {R : Type*} [CommRing R] (M : Matrix I4 I4 R) :
    M.det = M 0 0 * M 1 1 * M 2 2 * M 3 3
    - M 0 0 * M 1 1 * M 2 3 * M 3 2
    - M 0 0 * M 1 2 * M 2 1 * M 3 3
    + M 0 0 * M 1 2 * M 2 3 * M 3 1
    + M 0 0 * M 1 3 * M 2 1 * M 3 2
    - M 0 0 * M 1 3 * M 2 2 * M 3 1
    - M 0 1 * M 1 0 * M 2 2 * M 3 3
    + M 0 1 * M 1 0 * M 2 3 * M 3 2
    + M 0 1 * M 1 2 * M 2 0 * M 3 3
    - M 0 1 * M 1 2 * M 2 3 * M 3 0
    - M 0 1 * M 1 3 * M 2 0 * M 3 2
    + M 0 1 * M 1 3 * M 2 2 * M 3 0
    + M 0 2 * M 1 0 * M 2 1 * M 3 3
    - M 0 2 * M 1 0 * M 2 3 * M 3 1
    - M 0 2 * M 1 1 * M 2 0 * M 3 3
    + M 0 2 * M 1 1 * M 2 3 * M 3 0
    + M 0 2 * M 1 3 * M 2 0 * M 3 1
    - M 0 2 * M 1 3 * M 2 1 * M 3 0
    - M 0 3 * M 1 0 * M 2 1 * M 3 2
    + M 0 3 * M 1 0 * M 2 2 * M 3 1
    + M 0 3 * M 1 1 * M 2 0 * M 3 2
    - M 0 3 * M 1 1 * M 2 2 * M 3 0
    - M 0 3 * M 1 2 * M 2 0 * M 3 1
    + M 0 3 * M 1 2 * M 2 1 * M 3 0 := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.submatrix_apply, Fin.succAbove] <;> ring

def lo : I4 → I4 := ![0,2,1,1]
def hi : I4 → I4 := ![0,3,3,2]

def wedge (u : Mat) (i k l : I4) : ℂ := u 0 k * u i l - u 0 l * u i k

noncomputable def T (u : Mat) (i j : I4) : ℝ :=
  if i = 0 then (if j = 0 then 0 else normSq (u 0 j))
  else if j = 0 then normSq (u i 0) else normSq (wedge u i (lo j) (hi j))

def costs (a b : I4 → ℂ) (i j : I4) : ℂ :=
  if i = 0 then (if j = 0 then 0 else a 1*a 2*a 3*b j)
  else if j = 0 then b 1*b 2*b 3*a i else a (lo i)*a (hi i)*b (lo j)*b (hi j)

def oneMask (u : Mat) (i j : I4) : Mat := fun r c =>
  if r = i then (if c = j then u r j else 0) else u r c

def twoMask (u : Mat) (i k l : I4) : Mat := fun r c =>
  if r = 0 ∨ r = i then (if c = k then u r k else 0) + (if c = l then u r l else 0)
  else u r c

private theorem gram (u : Mat) (hu : u*uᴴ = 1) (r c : I4) :
    ∑ j, u r j * star (u c j) = (1 : Mat) r c := by
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply] using congrFun (congrFun hu r) c

private theorem norm_cast (z : ℂ) : (normSq z : ℂ) = z * star z := by
  simpa [Complex.star_def] using (Complex.mul_conj z).symm

private theorem cancel_det (u v : Mat) (hu : u*uᴴ = 1) (z : ℂ) (hv : (v*uᴴ).det=z) :
    v.det = z * u.det := by
  have hh := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_one] at hh
  rw [← hv, Matrix.det_mul, mul_assoc, mul_comm uᴴ.det, hh, mul_one]

theorem oneMask_det (u : Mat) (hu : u*uᴴ = 1) (i j : I4) :
    (oneMask u i j).det = (normSq (u i j) : ℂ) * u.det := by
  apply cancel_det _ _ hu
  have he : oneMask u i j * uᴴ = fun r c =>
      if r = i then u r j * star (u c j) else (1 : Mat) r c := by
    ext r c
    by_cases h : r = i
    · simp [Matrix.mul_apply, oneMask, h, ite_mul, Matrix.conjTranspose_apply]
    · simpa [Matrix.mul_apply, oneMask, h, Matrix.conjTranspose_apply] using gram u hu r c
  rw [det_four, he, norm_cast]
  fin_cases i <;> norm_num [Matrix.one_apply]

theorem twoMask_det (u : Mat) (hu : u*uᴴ = 1) {i : I4} (hi0 : i ≠ 0) (k l : I4) :
    (twoMask u i k l).det = (normSq (wedge u i k l) : ℂ) * u.det := by
  apply cancel_det _ _ hu
  have he : twoMask u i k l * uᴴ = fun r c =>
      if r = 0 ∨ r = i then u r k * star (u c k) + u r l * star (u c l)
      else (1 : Mat) r c := by
    ext r c
    by_cases h : r = 0 ∨ r = i
    · simp [Matrix.mul_apply, twoMask, h, add_mul, Finset.sum_add_distrib, ite_mul,
            Matrix.conjTranspose_apply]
    · simpa [Matrix.mul_apply, twoMask, h, Matrix.conjTranspose_apply] using gram u hu r c
  rw [det_four, he, norm_cast]
  fin_cases i <;> norm_num [Matrix.one_apply, wedge, star_sub, star_mul] at * <;> ring

private def masked (u : Mat) (i j : I4) : Mat :=
  if i = 0 ∨ j = 0 then oneMask u i j else twoMask u i (lo j) (hi j)

/-- Homogeneous before using any unitary equations. Each of the 15 terms
groups exactly the determinant permutations with the prescribed A/B choices. -/
theorem expansion_masked (a b : I4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0) (u : Mat) :
    (Matrix.of fun i j => (a i + b j) * u i j).det =
      ∑ i, ∑ j, costs a b i j * (masked u i j).det := by
  simp [det_four, Matrix.of_apply, Fin.sum_univ_succ, costs, masked, lo, hi, oneMask, twoMask, ha, hb]
  <;> ring

/-- Polynomial determinant expansion in all collision transport coefficients. -/
theorem expansion (a b : I4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (u : Mat) (hu : u*uᴴ = 1) (hu' : uᴴ*u = 1) :
    (diagonal a + u*diagonal b*uᴴ).det =
      ∑ i, ∑ j, (T u i j : ℂ) * costs a b i j := by
  have h0 : u.det ≠ 0 := by
    have h := congrArg Matrix.det hu
    rw [det_mul, det_one] at h
    exact left_ne_zero_of_mul (by rw [h]; exact one_ne_zero)
  have hp : (diagonal a + u*diagonal b*uᴴ)*u = Matrix.of fun i j => (a i+b j)*u i j := by
    rw [add_mul, Matrix.mul_assoc (u*diagonal b), hu', mul_one]
    ext i j
    simp [Matrix.of_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, add_mul, mul_comm] <;> ring
  apply mul_right_cancel₀ h0
  rw [← det_mul, hp, expansion_masked a b ha hb, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  by_cases ih : i = 0 <;> by_cases jh : j = 0
  · simp [ih, jh, costs, T]
  · simp [masked, ih, jh, oneMask_det u hu, T] <;> ring
  · simp [masked, ih, jh, oneMask_det u hu, T] <;> ring
  · simp [masked, ih, jh, twoMask_det u hu ih, T] <;> ring

private def dot (x y : I4 → ℂ) : ℂ := ∑ t, x t * star (y t)
private def en (z : ℂ) : ℂ := z * star z
private theorem cast_energy (z : ℂ) : (normSq z : ℂ) = en z := by
  simpa [en, Complex.star_def] using (Complex.mul_conj z).symm

private theorem gr (u : Mat) (hu : u*uᴴ = 1) (i k : I4) :
    dot (u i) (u k) = if i=k then 1 else 0 := by
  simpa [dot, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    using congrFun (congrFun hu i) k

private theorem gc (u : Mat) (hu' : uᴴ*u = 1) (j l : I4) :
    dot (fun r => u r j) (fun r => u r l) = if j=l then 1 else 0 := by
  simpa [dot, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, mul_comm,
    eq_comm] using congrFun (congrFun hu' l) j

private theorem rGram (x y : I4 → ℂ) (xx : dot x x = 1) (yy : dot y y = 1)
    (xy : dot x y = 0) (yx : dot y x = 0) :
    en (y 0) + (en (x 2*y 3-x 3*y 2) +
    (en (x 1*y 3-x 3*y 1) + en (x 1*y 2-x 2*y 1))) = 1 - en (x 0) := by
  calc _ = en (y 0) + (dot x x-en (x 0))*(dot y y-en (y 0)) -
      (dot x y-x 0*star (y 0))*(dot y x-y 0*star (x 0)) := by
        simp [en, dot, Fin.sum_univ_succ, star_sub, star_mul] <;> ring
       _ = _ := by rw [xx,yy,xy,yx]; unfold en; ring

private theorem cGram (x y : I4 → ℂ) (xx : dot x x = 1) (yy : dot y y = 1)
    (xy : dot x y = 0) (yx : dot y x = 0) :
    en (x 0*y 1-y 0*x 1) + (en (x 0*y 2-y 0*x 2) +
      en (x 0*y 3-y 0*x 3)) = en (x 0) + en (y 0) := by
  calc _ = en (x 0)*dot y y + en (y 0)*dot x x -
      x 0*star (y 0)*dot y x - y 0*star (x 0)*dot x y := by
        simp [en, dot, Fin.sum_univ_succ, star_sub, star_mul] <;> ring
       _ = _ := by rw [xx,yy,xy,yx]; ring

theorem T_nonneg (u : Mat) (i j : I4) : 0 ≤ T u i j := by
  unfold T
  split <;> split <;> first | exact le_rfl | exact normSq_nonneg _

theorem T_rows (u : Mat) (hu : u*uᴴ = 1) (i : I4) :
    ∑ j, T u i j = 1 - normSq (u 0 0) := by
  have r0 := gr u hu 0 0
  simp [dot, Fin.sum_univ_succ] at r0
  apply Complex.ofReal_injective
  by_cases h : i = 0
  · subst i
    simp [Fin.sum_univ_succ,T, cast_energy, en]
    linear_combination r0
  · have rr := rGram (u 0) (u i) (by simpa using gr u hu 0 0)
          (by simpa using gr u hu i i) (by simpa [Ne.symm h] using gr u hu 0 i)
          (by simpa [h] using gr u hu i 0)
    simpa [Fin.sum_univ_succ,T,h,wedge,lo,hi,cast_energy,add_assoc] using rr

theorem T_cols (u : Mat) (hu : u*uᴴ = 1) (hu' : uᴴ*u = 1) (j : I4) :
    ∑ i, T u i j = 1 - normSq (u 0 0) := by
  have c0 := gc u hu' 0 0
  simp [dot, Fin.sum_univ_succ] at c0
  apply Complex.ofReal_injective
  by_cases h : j = 0
  · subst j
    simp [Fin.sum_univ_succ,T, cast_energy, en]
    linear_combination c0
  · have hkl : lo j ≠ hi j := by fin_cases j <;> first | contradiction | decide
    have cc := cGram (fun r => u r (lo j)) (fun r => u r (hi j))
          (by simpa using gc u hu' (lo j) (lo j)) (by simpa using gc u hu' (hi j) (hi j))
          (by simpa [hkl] using gc u hu' (lo j) (hi j))
          (by simpa [Ne.symm hkl] using gc u hu' (hi j) (lo j))
    have r0 := gr u hu 0 0
    simp [dot,Fin.sum_univ_succ] at r0
    fin_cases j <;> first | contradiction | (simp [Fin.sum_univ_succ,T,wedge,lo,hi,cast_energy,en] at cc ⊢ <;>
      first | linear_combination cc + r0 | linear_combination r0 | linear_combination cc)

theorem T_mass_bounds (u : Mat) (hu : u*uᴴ=1) :
    0 ≤ 1-normSq (u 0 0) ∧ 1-normSq (u 0 0) ≤ 1 :=
  ⟨T_rows u hu 0 ▸ Finset.sum_nonneg (fun j _ => T_nonneg u 0 j),
    sub_le_self _ (normSq_nonneg _)⟩

def vertex (a b : I4 → ℂ) (p : Equiv.Perm I4) : ℂ := ∏ i, (a i + b (p i))

def polygon (a b : I4 → ℂ) : Set ℂ := convexHull ℝ (Set.range (vertex a b))

/-- Enumerates *images* only. The finite closed check does not inspect real
or complex numbers and uses kernel reduction rather than native decision. -/
private theorem tuple_cases (p : Equiv.Perm I4) (hp : p 0 ≠ 0) :
    (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 2 ∧ p 3 = 3) ∨
        (p 0 = 1 ∧ p 1 = 0 ∧ p 2 = 3 ∧ p 3 = 2) ∨
        (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 0 ∧ p 3 = 3) ∨
        (p 0 = 1 ∧ p 1 = 2 ∧ p 2 = 3 ∧ p 3 = 0) ∨
        (p 0 = 1 ∧ p 1 = 3 ∧ p 2 = 0 ∧ p 3 = 2) ∨
        (p 0 = 1 ∧ p 1 = 3 ∧ p 2 = 2 ∧ p 3 = 0) ∨
        (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 1 ∧ p 3 = 3) ∨
        (p 0 = 2 ∧ p 1 = 0 ∧ p 2 = 3 ∧ p 3 = 1) ∨
        (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 0 ∧ p 3 = 3) ∨
        (p 0 = 2 ∧ p 1 = 1 ∧ p 2 = 3 ∧ p 3 = 0) ∨
        (p 0 = 2 ∧ p 1 = 3 ∧ p 2 = 0 ∧ p 3 = 1) ∨
        (p 0 = 2 ∧ p 1 = 3 ∧ p 2 = 1 ∧ p 3 = 0) ∨
        (p 0 = 3 ∧ p 1 = 0 ∧ p 2 = 1 ∧ p 3 = 2) ∨
        (p 0 = 3 ∧ p 1 = 0 ∧ p 2 = 2 ∧ p 3 = 1) ∨
        (p 0 = 3 ∧ p 1 = 1 ∧ p 2 = 0 ∧ p 3 = 2) ∨
        (p 0 = 3 ∧ p 1 = 1 ∧ p 2 = 2 ∧ p 3 = 0) ∨
        (p 0 = 3 ∧ p 1 = 2 ∧ p 2 = 0 ∧ p 3 = 1) ∨
        (p 0 = 3 ∧ p 1 = 2 ∧ p 2 = 1 ∧ p 3 = 0) := by
  have table : ∀ x y z t : I4, x ≠ 0 → x ≠ y → x ≠ z → x ≠ t → y ≠ z → y ≠ t → z ≠ t → 
        (x = 1 ∧ y = 0 ∧ z = 2 ∧ t = 3) ∨
        (x = 1 ∧ y = 0 ∧ z = 3 ∧ t = 2) ∨
        (x = 1 ∧ y = 2 ∧ z = 0 ∧ t = 3) ∨
        (x = 1 ∧ y = 2 ∧ z = 3 ∧ t = 0) ∨
        (x = 1 ∧ y = 3 ∧ z = 0 ∧ t = 2) ∨
        (x = 1 ∧ y = 3 ∧ z = 2 ∧ t = 0) ∨
        (x = 2 ∧ y = 0 ∧ z = 1 ∧ t = 3) ∨
        (x = 2 ∧ y = 0 ∧ z = 3 ∧ t = 1) ∨
        (x = 2 ∧ y = 1 ∧ z = 0 ∧ t = 3) ∨
        (x = 2 ∧ y = 1 ∧ z = 3 ∧ t = 0) ∨
        (x = 2 ∧ y = 3 ∧ z = 0 ∧ t = 1) ∨
        (x = 2 ∧ y = 3 ∧ z = 1 ∧ t = 0) ∨
        (x = 3 ∧ y = 0 ∧ z = 1 ∧ t = 2) ∨
        (x = 3 ∧ y = 0 ∧ z = 2 ∧ t = 1) ∨
        (x = 3 ∧ y = 1 ∧ z = 0 ∧ t = 2) ∨
        (x = 3 ∧ y = 1 ∧ z = 2 ∧ t = 0) ∨
        (x = 3 ∧ y = 2 ∧ z = 0 ∧ t = 1) ∨
        (x = 3 ∧ y = 2 ∧ z = 1 ∧ t = 0) := by
    intro x y z t
    fin_cases x <;> fin_cases y <;> fin_cases z <;> fin_cases t <;> norm_num
  exact table _ _ _ _ hp (p.injective.ne (by decide : (0 : I4) ≠ 1)) (p.injective.ne (by decide : (0 : I4) ≠ 2)) (p.injective.ne (by decide : (0 : I4) ≠ 3)) (p.injective.ne (by decide : (1 : I4) ≠ 2)) (p.injective.ne (by decide : (1 : I4) ≠ 3)) (p.injective.ne (by decide : (2 : I4) ≠ 3))

/-- Reversing the two surviving interior assignments converts transport
permutation cost into a genuine permutation determinant, without division. -/
theorem permutation_cost (a b : I4 → ℂ) (ha : a 0 = 0) (hb : b 0 = 0)
    (p : Equiv.Perm I4) (hp : p 0 ≠ 0) :
    (∑ i, costs a b i (p i)) ∈ polygon a b := by
  apply subset_convexHull
  rcases tuple_cases p hp with ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩ | ⟨h0,h1,h2,h3⟩
  · refine ⟨(Equiv.swap (2 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (2 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 2).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 2).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (2 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (2 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 2).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 2).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (2 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (2 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 2).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 3).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring
  · refine ⟨(Equiv.swap (1 : I4) 2).trans p, ?_⟩
    norm_num [vertex, Fin.prod_univ_succ, Fin.sum_univ_succ, costs, lo, hi,
      Equiv.swap_apply_def, h0,h1,h2,h3, ha,hb] <;> ring

theorem at_origin (a b : I4 → ℂ) (ha : a 0=0) (hb : b 0=0) (u : Mat)
    (hu : u*uᴴ=1) (hu' : uᴴ*u=1) :
    (diagonal a + u*diagonal b*uᴴ).det ∈ polygon a b := by
  rw [expansion a b ha hb u hu hu']
  have h0 : (0 : ℂ) ∈ polygon a b := by
    apply subset_convexHull
    refine ⟨1,?_⟩
    simp [vertex, Fin.prod_univ_succ, ha,hb]
  obtain ⟨hs,hs'⟩ := T_mass_bounds u hu
  have hh := MOCTransport.face (costs a b) (T u) 0 0 _ hs hs' (T_nonneg u)
      (T_rows u hu) (T_cols u hu hu') (by simp [T]) (polygon a b) (convex_convexHull _ _) h0
      (permutation_cost a b ha hb)
  simpa [MOCTransport.charge, Complex.real_smul] using hh

private theorem pencil_eq (a b : I4 → ℂ) (u : Mat) (hu' : uᴴ*u=1) :
    (diagonal a + u*diagonal b*uᴴ)*u = Matrix.of fun i j => (a i+b j)*u i j := by
  rw [add_mul, Matrix.mul_assoc (u*diagonal b), hu', mul_one]
  ext i j
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply, add_mul, mul_comm] <;> ring

/-- The full order-four cross-spectral collision theorem, in eigenframe
coordinates. Includes zero/repeated eigenvalues, arbitrary distinguished
indices, arbitrary relative complex unitary, and either spectral shape. -/
theorem collision (a b : Fin 4 → ℂ) (u : Matrix (Fin 4) (Fin 4) ℂ)
    (hu : u*uᴴ=1) (hu' : uᴴ*u=1) {i j : Fin 4} (h : a i+b j=0) :
    (diagonal a + u*diagonal b*uᴴ).det ∈
      convexHull ℝ (Set.range (fun p : Equiv.Perm (Fin 4) => ∏ k, (a k+b (p k)))) := by
  classical
  let e := Equiv.swap 0 i
  let f := Equiv.swap 0 j
  let v := u.submatrix e f
  let x (k : I4) := a (e k) - a i
  let y (k : I4) := b (f k) + a i
  have hx : x 0=0 := by simp [x,e]
  have hy : y 0=0 := by simpa [y,f,add_comm] using h
  have hv : v*vᴴ=1 := by
    dsimp [v]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, hu, submatrix_one_equiv]
  have hv' : vᴴ*v=1 := by
    dsimp [v]
    rw [conjTranspose_submatrix, submatrix_mul_equiv, hu', submatrix_one_equiv]
  have hsum (k t : I4) : x k+y t=a (e k)+b (f t) := by dsimp [x,y];ring
  have hmat : diagonal x + v*diagonal y*vᴴ =
      (diagonal a + u*diagonal b*uᴴ).submatrix e e := by
    have H₁ := pencil_eq x y v hv'
    have H₂ := congrArg (fun M : Mat => M.submatrix e f) (pencil_eq a b u hu')
    have He : (diagonal x + v*diagonal y*vᴴ)*v =
        (diagonal a + u*diagonal b*uᴴ).submatrix e e * v := by
      rw [H₁]
      change _ = (diagonal a + u*diagonal b*uᴴ).submatrix e e * u.submatrix e f
      rw [submatrix_mul_equiv, H₂]
      ext k t
      simp [v, hsum]
    have := congrArg (fun M : Mat => M*vᴴ) He
    simpa [Matrix.mul_assoc,hv] using this
  have goal0 := at_origin x y hx hy v hv hv'
  rw [hmat,det_submatrix_equiv_self] at goal0
  apply convexHull_mono _ goal0
  rintro _ ⟨p,rfl⟩
  refine ⟨(e.symm.trans p).trans f,?_⟩
  unfold vertex
  simpa only [Equiv.trans_apply,Equiv.symm_apply_apply,hsum] using
    (Equiv.prod_comp e (fun k => a k + b (((e.symm.trans p).trans f) k))).symm


end MOCCollision
