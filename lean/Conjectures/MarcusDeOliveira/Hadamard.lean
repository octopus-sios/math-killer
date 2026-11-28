import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open Matrix Finset
open scoped Matrix BigOperators
noncomputable section
namespace MOCKlein

abbrev I4 := Fin 4
abbrev I3 := Fin 3
abbrev M4 := Matrix I4 I4 ℝ
abbrev M3 := Matrix I3 I3 ℝ

/-- Addition in the regular Klein group, with its four labeled elements. -/
def addV : Matrix I4 I4 I4 := Matrix.of ![![0,1,2,3],![1,0,3,2],![2,3,0,1],![3,2,1,0]]

private theorem invol (k x : I4) : addV k (addV k x) = x := by decide +revert
private theorem diff (k x y : I4) : addV (addV k x) (addV k y) = addV x y := by fin_cases k <;> fin_cases x <;> fin_cases y <;> rfl

def translation (k : I4) : Equiv.Perm I4 :=
  ⟨addV k,addV k,invol k,invol k⟩

def lift (p : Equiv.Perm I3) : Equiv.Perm I4 where
  toFun := Fin.cases 0 (fun r => (p r).succ)
  invFun := Fin.cases 0 (fun r => (p.symm r).succ)
  left_inv x := by refine Fin.cases ?_ (fun r => ?_) x <;> simp
  right_inv x := by refine Fin.cases ?_ (fun r => ?_) x <;> simp

/-- The image of the pair {0,i+1} has Klein difference j+1 precisely
when it belongs to the j-th partition into complementary pairs. -/
def quotientTable (p : Equiv.Perm I4) : M3 := fun i j =>
  if addV (p 0) (p i.succ) = j.succ then 1 else 0

def vertex (p : Equiv.Perm I4) : M4 × M3 := (p.permMatrix ℝ,quotientTable p)
def Pi4 := convexHull ℝ (Set.range vertex)
def flat : M4 := fun _ _ => 1/4

private theorem q_coset (p : Equiv.Perm I3) (k : I4) :
    quotientTable ((lift p).trans (translation k)) = p.permMatrix ℝ := by
  ext i j
  change (if addV (addV k _) (addV k _) = j.succ then _ else _) = _
  rw [diff]
  have hz (x : I4) : addV 0 x = x := by fin_cases x <;> rfl
  change (if addV 0 (p i).succ = j.succ then (1 : ℝ) else 0) = _
  rw [hz]
  by_cases hp : p i = j <;> simp [hp, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def]

/-- Exact matrix-section identity: no classification of complex Hadamard
matrices is necessary, and every bistochastic Q (not just the actually
attainable ones) is covered. -/
theorem section_flat (Q : M3) (hQ : Q ∈ doublyStochastic ℝ I3) : (flat,Q) ∈ Pi4 := by
  classical
  have hconv : Convex ℝ Pi4 := convex_convexHull _ _
  have onecoset (p : Equiv.Perm I3) : (flat,p.permMatrix ℝ) ∈ Pi4 := by
    let z (k : I4) := vertex ((lift p).trans (translation k))
    have hz (k : I4) : z k ∈ Pi4 := subset_convexHull ℝ _ ⟨_,rfl⟩
    have e : ∑ k : I4, (1/4 : ℝ) • z k = (flat,p.permMatrix ℝ) := by
      apply Prod.ext
      · ext i j
        simp [z,vertex, Fin.sum_univ_succ,flat, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply,
          Option.mem_def, translation, Matrix.smul_apply]
        generalize lift p i = t
        fin_cases t <;> fin_cases j <;> norm_num [addV,Matrix.of_apply]
      · ext i j
        by_cases he : p i = j <;> norm_num [z,vertex,Fin.sum_univ_succ,q_coset,Matrix.smul_apply,Equiv.toPEquiv_apply,he]
    rw [← e]
    apply hconv.sum_mem (fun _ _ => by norm_num) _ (fun k _ => hz k)
    norm_num [Fin.sum_univ_succ]
  obtain ⟨w,hw,hw1,heq⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hQ
  have e : ∑ p : Equiv.Perm I3, w p • (flat,p.permMatrix ℝ) = (flat,Q) := by
    apply Prod.ext
    · simp [Prod.fst_sum, ← Finset.sum_smul,hw1]
    · simpa [Prod.snd_sum] using heq
  rw [← e]
  exact hconv.sum_mem (fun p _ => hw p) hw1 (fun p _ => onecoset p)

end MOCKlein
namespace MOCKlein
open Complex Matrix
open scoped Matrix BigOperators

abbrev Mat := Matrix I4 I4 ℂ
private def lo : I3 → I4 := ![2,1,1]
private def hi : I3 → I4 := ![3,3,2]
def wedge (u : Mat) (i k l : I4) : ℂ := u 0 k*u i l - u 0 l*u i k

/-- Sum of squared minors for a pair of complementary column pairs. -/
def compoundQ (u : Mat) (i j : I3) : ℝ :=
  normSq (wedge u i.succ 0 j.succ) + normSq (wedge u i.succ (lo j) (hi j))

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

private theorem cGram (x y : I4 → ℂ) (xx : dot x x = 1) (yy : dot y y = 1)
    (xy : dot x y = 0) (yx : dot y x = 0) :
    en (x 0*y 1-y 0*x 1) + (en (x 0*y 2-y 0*x 2) +
      en (x 0*y 3-y 0*x 3)) = en (x 0) + en (y 0) := by
  calc _ = en (x 0)*dot y y + en (y 0)*dot x x -
      x 0*star (y 0)*dot y x - y 0*star (x 0)*dot x y := by
        simp [en, dot, Fin.sum_univ_succ, star_sub, star_mul] <;> ring
       _ = _ := by rw [xx,yy,xy,yx]; ring


private theorem six (x y : I4 → ℂ) (xx : dot x x = 1) (yy : dot y y = 1)
    (xy : dot x y = 0) (yx : dot y x = 0) :
    en (x 0*y 1-x 1*y 0) + en (x 2*y 3-x 3*y 2) +
    (en (x 0*y 2-x 2*y 0) + en (x 1*y 3-x 3*y 1)) +
    (en (x 0*y 3-x 3*y 0) + en (x 1*y 2-x 2*y 1)) = 1 := by
  calc _ = dot x x*dot y y - dot x y*dot y x := by
        simp [en,dot, Fin.sum_univ_succ,star_sub,star_mul] <;> ring
       _ = _ := by rw [xx,yy,xy,yx]; ring

theorem compound_bistochastic (u : Mat) (hu : u*uᴴ=1) (hu' : uᴴ*u=1) :
    compoundQ u ∈ doublyStochastic ℝ I3 := by
  refine mem_doublyStochastic_iff_sum.mpr ⟨fun i j => add_nonneg (normSq_nonneg _) (normSq_nonneg _),?_,?_⟩
  · intro i
    have hn : i.succ ≠ 0 := Fin.succ_ne_zero _
    have hs := six (u 0) (u i.succ) (by simpa using gr u hu 0 0)
      (by simpa using gr u hu i.succ i.succ) (by simpa [Ne.symm hn] using gr u hu 0 i.succ)
      (by simpa [hn] using gr u hu i.succ 0)
    apply Complex.ofReal_injective
    simpa [Fin.sum_univ_succ,compoundQ,lo,hi,cast_energy,wedge,add_assoc] using hs
  · intro j
    have cc (k l : I4) (hkl : k ≠ l) := cGram (fun r => u r k) (fun r => u r l)
      (by simpa using gc u hu' k k) (by simpa using gc u hu' l l)
      (by simpa [hkl] using gc u hu' k l) (by simpa [Ne.symm hkl] using gc u hu' l k)
    have h₁ := cc 0 j.succ (Ne.symm (Fin.succ_ne_zero _))
    have h₂ := cc (lo j) (hi j) (by fin_cases j <;> decide)
    have h₃ := gr u hu 0 0
    simp [dot,Fin.sum_univ_succ] at h₃
    apply Complex.ofReal_injective
    fin_cases j <;>
      simp [compoundQ,lo,hi,wedge,cast_energy,en,Fin.sum_univ_succ] at h₁ h₂ ⊢ <;>
      linear_combination h₁+h₂+h₃

/-- Actual Hadamard safety in the compound polytope for arbitrary complex
unitary U with squared entry moduli 1/4. No parametrization of U is assumed. -/
theorem hadamard (u : Mat) (hu : u*uᴴ=1) (hu' : uᴴ*u=1)
    (h : ∀ i j, normSq (u i j) = 1/4) :
    (Matrix.of (fun i j => normSq (u i j)),compoundQ u) ∈ Pi4 := by
  have hs : Matrix.of (fun i j => normSq (u i j)) = flat := by ext i j; exact h i j
  rw [hs]
  exact section_flat _ (compound_bistochastic u hu hu')

end MOCKlein

