import Conjectures.MarcusDeOliveira.Matching
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp

/-! From the positive gap polynomials to a determinant theorem. The 24
signed Leibniz terms, after multiplication by the common Cauchy denominator,
are nine-factor signed gap products. The bucket lemmas compare the same
spectral monomials coefficientwise to the 14 positive matching weights. -/
open Matrix MOCMatching
open scoped Matrix BigOperators
noncomputable section
namespace MOCCauchy
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000

abbrev I4 := Fin 4
abbrev Mat := Matrix I4 I4 ℂ
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


private def R (es : List E) : P 6 := es.foldr timesGap (oneP 6)
private theorem ev_prod (es : List E) (g) :
    ev 6 (R es) g = (es.map (gap · g)).prod := by
  unfold R
  induction es <;> simp [ev_gap, ev_one, *]

/-- Signed distances λ_t−h_i in the interlacing order, with infinity row
representing the center (its denominator is 1). -/
def den (g : Nat → ℝ) (i j : I4) : ℝ :=
  if i=3 then 1 else if 2*j.val < 2*i.val+1 then -gap (2*j.val,2*i.val+1) g
  else gap (2*i.val+1,2*j.val) g

private def clearD (g : Nat → ℝ) : ℂ :=
  (gap (0,1) g : ℂ) * (gap (1,2) g : ℂ) * (gap (1,4) g : ℂ) * (gap (1,6) g : ℂ) * (gap (0,3) g : ℂ) * (gap (2,3) g : ℂ) * (gap (3,4) g : ℂ) * (gap (3,6) g : ℂ) * (gap (0,5) g : ℂ) * (gap (2,5) g : ℂ) * (gap (4,5) g : ℂ) * (gap (5,6) g : ℂ)

private def sc (l r : I4 → ℂ) : ℂ :=
  l 0*l 1*l 2*l 3*(r 0*r 1*r 2*r 3)

private def zval (a b : I4 → ℂ) (j k l m : I4) :=
  (a 0+b j)*(a 1+b k)*(a 2+b l)*(a 3+b m)
private def cv (p : P 6) (g : Nat → ℝ) : ℂ := (ev 6 p g : ℝ)
private theorem cv_add (p q : P 6) (g) :
    cv (addP 6 p q) g = cv p g + cv q g := by simp [cv,ev_add]
private def raw0 : P 6 := R [(1,2),(1,4),(1,6),(0,3),(3,4),(3,6),(0,5),(2,5),(5,6)]
private def raw1 : P 6 := R [(1,2),(1,4),(1,6),(0,3),(3,4),(3,6),(0,5),(2,5),(4,5)]
private def raw2 : P 6 := R [(1,2),(1,4),(1,6),(0,3),(2,3),(3,6),(0,5),(4,5),(5,6)]
private def raw3 : P 6 := R [(1,2),(1,4),(1,6),(0,3),(2,3),(3,6),(0,5),(2,5),(4,5)]
private def raw4 : P 6 := R [(1,2),(1,4),(1,6),(0,3),(2,3),(3,4),(0,5),(4,5),(5,6)]
private def raw5 : P 6 := R [(1,2),(1,4),(1,6),(0,3),(2,3),(3,4),(0,5),(2,5),(5,6)]
private def raw6 : P 6 := R [(0,1),(1,4),(1,6),(2,3),(3,4),(3,6),(0,5),(2,5),(5,6)]
private def raw7 : P 6 := R [(0,1),(1,4),(1,6),(2,3),(3,4),(3,6),(0,5),(2,5),(4,5)]
private def raw8 : P 6 := R [(0,1),(1,4),(1,6),(0,3),(2,3),(3,6),(2,5),(4,5),(5,6)]
private def raw9 : P 6 := R [(0,1),(1,4),(1,6),(0,3),(2,3),(3,6),(0,5),(2,5),(4,5)]
private def raw10 : P 6 := R [(0,1),(1,4),(1,6),(0,3),(2,3),(3,4),(2,5),(4,5),(5,6)]
private def raw11 : P 6 := R [(0,1),(1,4),(1,6),(0,3),(2,3),(3,4),(0,5),(2,5),(5,6)]
private def raw12 : P 6 := R [(0,1),(1,2),(1,6),(2,3),(3,4),(3,6),(0,5),(4,5),(5,6)]
private def raw13 : P 6 := R [(0,1),(1,2),(1,6),(2,3),(3,4),(3,6),(0,5),(2,5),(4,5)]
private def raw14 : P 6 := R [(0,1),(1,2),(1,6),(0,3),(3,4),(3,6),(2,5),(4,5),(5,6)]
private def raw15 : P 6 := R [(0,1),(1,2),(1,6),(0,3),(3,4),(3,6),(0,5),(2,5),(4,5)]
private def raw16 : P 6 := R [(0,1),(1,2),(1,6),(0,3),(2,3),(3,4),(2,5),(4,5),(5,6)]
private def raw17 : P 6 := R [(0,1),(1,2),(1,6),(0,3),(2,3),(3,4),(0,5),(4,5),(5,6)]
private def raw18 : P 6 := R [(0,1),(1,2),(1,4),(2,3),(3,4),(3,6),(0,5),(4,5),(5,6)]
private def raw19 : P 6 := R [(0,1),(1,2),(1,4),(2,3),(3,4),(3,6),(0,5),(2,5),(5,6)]
private def raw20 : P 6 := R [(0,1),(1,2),(1,4),(0,3),(3,4),(3,6),(2,5),(4,5),(5,6)]
private def raw21 : P 6 := R [(0,1),(1,2),(1,4),(0,3),(3,4),(3,6),(0,5),(2,5),(5,6)]
private def raw22 : P 6 := R [(0,1),(1,2),(1,4),(0,3),(2,3),(3,6),(2,5),(4,5),(5,6)]
private def raw23 : P 6 := R [(0,1),(1,2),(1,4),(0,3),(2,3),(3,6),(0,5),(4,5),(5,6)]
private theorem bucket15 (g) : cv raw16 g + cv raw23 g = cv raw17 g + cv raw22 g + cv w13 g := by
  have h : (addP 6 raw16 (raw23)) = (addP 6 raw17 (addP 6 raw22 (w13))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket23 (g) : cv raw18 g + cv raw21 g + cv raw23 g = cv raw19 g + cv raw20 g + cv raw22 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw18 (addP 6 raw21 (raw23))) = (addP 6 raw19 (addP 6 raw20 (addP 6 raw22 (addP 6 w12 (w13))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket27 (g) : cv raw11 g + cv raw21 g = cv raw10 g + cv raw20 g + cv w10 g + cv w12 g := by
  have h : (addP 6 raw11 (raw21)) = (addP 6 raw10 (addP 6 raw20 (addP 6 w10 (w12)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket29 (g) : cv raw5 g + cv raw11 g + cv raw16 g = cv raw4 g + cv raw10 g + cv raw17 g + cv w4 g + cv w10 g := by
  have h : (addP 6 raw5 (addP 6 raw11 (raw16))) = (addP 6 raw4 (addP 6 raw10 (addP 6 raw17 (addP 6 w4 (w10))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket30 (g) : cv raw5 g + cv raw18 g = cv raw4 g + cv raw19 g + cv w4 g := by
  have h : (addP 6 raw5 (raw18)) = (addP 6 raw4 (addP 6 raw19 (w4))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket39 (g) : cv raw15 g + cv raw21 g = cv raw13 g + cv raw19 g + cv w11 g + cv w12 g := by
  have h : (addP 6 raw15 (raw21)) = (addP 6 raw13 (addP 6 raw19 (addP 6 w11 (w12)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket43 (g) : cv raw9 g + cv raw11 g + cv raw15 g + cv raw21 g + cv raw23 g = cv raw17 g + cv w9 g + cv w10 g + cv w11 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw9 (addP 6 raw11 (addP 6 raw15 (addP 6 raw21 (raw23))))) = (addP 6 raw17 (addP 6 w9 (addP 6 w10 (addP 6 w11 (addP 6 w12 (w13)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket45 (g) : cv raw3 g + cv raw5 g + cv raw9 g + cv raw11 g = cv w3 g + cv w4 g + cv w9 g + cv w10 g := by
  have h : (addP 6 raw3 (addP 6 raw5 (addP 6 raw9 (raw11)))) = (addP 6 w3 (addP 6 w4 (addP 6 w9 (w10)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket46 (g) : cv raw3 g + cv raw5 g + cv raw16 g = cv raw13 g + cv raw19 g + cv raw22 g + cv w3 g + cv w4 g := by
  have h : (addP 6 raw3 (addP 6 raw5 (raw16))) = (addP 6 raw13 (addP 6 raw19 (addP 6 raw22 (addP 6 w3 (w4))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket51 (g) : cv raw7 g + cv raw9 g + cv raw18 g + cv raw23 g = cv w6 g + cv w9 g + cv w13 g := by
  have h : (addP 6 raw7 (addP 6 raw9 (addP 6 raw18 (raw23)))) = (addP 6 w6 (addP 6 w9 (w13))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket53 (g) : cv raw1 g + cv raw3 g + cv raw7 g + cv raw9 g + cv raw15 g = cv raw13 g + cv w1 g + cv w3 g + cv w6 g + cv w9 g + cv w11 g := by
  have h : (addP 6 raw1 (addP 6 raw3 (addP 6 raw7 (addP 6 raw9 (raw15))))) = (addP 6 raw13 (addP 6 w1 (addP 6 w3 (addP 6 w6 (addP 6 w9 (w11)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket54 (g) : cv raw1 g + cv raw3 g = cv raw20 g + cv raw22 g + cv w1 g + cv w3 g := by
  have h : (addP 6 raw1 (raw3)) = (addP 6 raw20 (addP 6 raw22 (addP 6 w1 (w3)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket57 (g) : cv raw1 g + cv raw15 g = cv raw4 g + cv raw17 g + cv w1 g + cv w11 g := by
  have h : (addP 6 raw1 (raw15)) = (addP 6 raw4 (addP 6 raw17 (addP 6 w1 (w11)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket58 (g) : cv raw1 g + cv raw7 g + cv raw18 g = cv raw4 g + cv raw10 g + cv raw20 g + cv w1 g + cv w6 g := by
  have h : (addP 6 raw1 (addP 6 raw7 (raw18))) = (addP 6 raw4 (addP 6 raw10 (addP 6 raw20 (addP 6 w1 (w6))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket60 (g) : cv raw7 g + cv raw16 g = cv raw10 g + cv raw13 g + cv w6 g := by
  have h : (addP 6 raw7 (raw16)) = (addP 6 raw10 (addP 6 raw13 (w6))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket71 (g) : cv raw14 g + cv raw15 g + cv raw16 g = cv raw12 g + cv raw13 g + cv raw17 g + cv w8 g + cv w11 g := by
  have h : (addP 6 raw14 (addP 6 raw15 (raw16))) = (addP 6 raw12 (addP 6 raw13 (addP 6 raw17 (addP 6 w8 (w11))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket75 (g) : cv raw8 g + cv raw9 g + cv raw14 g + cv raw15 g = cv w7 g + cv w8 g + cv w9 g + cv w11 g := by
  have h : (addP 6 raw8 (addP 6 raw9 (addP 6 raw14 (raw15)))) = (addP 6 w7 (addP 6 w8 (addP 6 w9 (w11)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket77 (g) : cv raw2 g + cv raw3 g + cv raw8 g + cv raw9 g + cv raw23 g = cv raw22 g + cv w2 g + cv w3 g + cv w7 g + cv w9 g + cv w13 g := by
  have h : (addP 6 raw2 (addP 6 raw3 (addP 6 raw8 (addP 6 raw9 (raw23))))) = (addP 6 raw22 (addP 6 w2 (addP 6 w3 (addP 6 w7 (addP 6 w9 (w13)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket78 (g) : cv raw2 g + cv raw3 g = cv raw12 g + cv raw13 g + cv w2 g + cv w3 g := by
  have h : (addP 6 raw2 (raw3)) = (addP 6 raw12 (addP 6 raw13 (addP 6 w2 (w3)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket83 (g) : cv raw6 g + cv raw7 g + cv raw8 g + cv raw9 g + cv raw11 g = cv raw10 g + cv w5 g + cv w6 g + cv w7 g + cv w9 g + cv w10 g := by
  have h : (addP 6 raw6 (addP 6 raw7 (addP 6 raw8 (addP 6 raw9 (raw11))))) = (addP 6 raw10 (addP 6 w5 (addP 6 w6 (addP 6 w7 (addP 6 w9 (w10)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket85 (g) : cv raw0 g + cv raw1 g + cv raw2 g + cv raw3 g + cv raw5 g + cv raw6 g + cv raw7 g + cv raw8 g + cv raw9 g + cv raw11 g + cv raw14 g + cv raw15 g + cv raw16 g + cv raw18 g + cv raw21 g + cv raw23 g = cv raw4 g + cv raw10 g + cv raw12 g + cv raw13 g + cv raw17 g + cv raw19 g + cv raw20 g + cv raw22 g + cv w0 g + cv w1 g + cv w2 g + cv w3 g + cv w4 g + cv w5 g + cv w6 g + cv w7 g + cv w8 g + cv w9 g + cv w10 g + cv w11 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw2 (addP 6 raw3 (addP 6 raw5 (addP 6 raw6 (addP 6 raw7 (addP 6 raw8 (addP 6 raw9 (addP 6 raw11 (addP 6 raw14 (addP 6 raw15 (addP 6 raw16 (addP 6 raw18 (addP 6 raw21 (raw23)))))))))))))))) = (addP 6 raw4 (addP 6 raw10 (addP 6 raw12 (addP 6 raw13 (addP 6 raw17 (addP 6 raw19 (addP 6 raw20 (addP 6 raw22 (addP 6 w0 (addP 6 w1 (addP 6 w2 (addP 6 w3 (addP 6 w4 (addP 6 w5 (addP 6 w6 (addP 6 w7 (addP 6 w8 (addP 6 w9 (addP 6 w10 (addP 6 w11 (addP 6 w12 (w13)))))))))))))))))))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket86 (g) : cv raw0 g + cv raw1 g + cv raw2 g + cv raw3 g + cv raw5 g = cv raw4 g + cv w0 g + cv w1 g + cv w2 g + cv w3 g + cv w4 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw2 (addP 6 raw3 (raw5))))) = (addP 6 raw4 (addP 6 w0 (addP 6 w1 (addP 6 w2 (addP 6 w3 (w4)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket89 (g) : cv raw0 g + cv raw1 g + cv raw14 g + cv raw15 g + cv raw21 g = cv raw20 g + cv w0 g + cv w1 g + cv w8 g + cv w11 g + cv w12 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw14 (addP 6 raw15 (raw21))))) = (addP 6 raw20 (addP 6 w0 (addP 6 w1 (addP 6 w8 (addP 6 w11 (w12)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket90 (g) : cv raw0 g + cv raw1 g + cv raw6 g + cv raw7 g = cv w0 g + cv w1 g + cv w5 g + cv w6 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw6 (raw7)))) = (addP 6 w0 (addP 6 w1 (addP 6 w5 (w6)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket92 (g) : cv raw6 g + cv raw7 g + cv raw18 g = cv raw12 g + cv raw13 g + cv raw19 g + cv w5 g + cv w6 g := by
  have h : (addP 6 raw6 (addP 6 raw7 (raw18))) = (addP 6 raw12 (addP 6 raw13 (addP 6 raw19 (addP 6 w5 (w6))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket99 (g) : cv raw6 g + cv raw11 g = cv raw12 g + cv raw17 g + cv w5 g + cv w10 g := by
  have h : (addP 6 raw6 (raw11)) = (addP 6 raw12 (addP 6 raw17 (addP 6 w5 (w10)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket101 (g) : cv raw0 g + cv raw5 g + cv raw6 g + cv raw11 g + cv raw21 g = cv raw19 g + cv w0 g + cv w4 g + cv w5 g + cv w10 g + cv w12 g := by
  have h : (addP 6 raw0 (addP 6 raw5 (addP 6 raw6 (addP 6 raw11 (raw21))))) = (addP 6 raw19 (addP 6 w0 (addP 6 w4 (addP 6 w5 (addP 6 w10 (w12)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket102 (g) : cv raw0 g + cv raw5 g + cv raw14 g + cv raw16 g = cv w0 g + cv w4 g + cv w8 g := by
  have h : (addP 6 raw0 (addP 6 raw5 (addP 6 raw14 (raw16)))) = (addP 6 w0 (addP 6 w4 (w8))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket105 (g) : cv raw0 g + cv raw2 g + cv raw21 g + cv raw23 g = cv w0 g + cv w2 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw0 (addP 6 raw2 (addP 6 raw21 (raw23)))) = (addP 6 w0 (addP 6 w2 (addP 6 w12 (w13)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket106 (g) : cv raw0 g + cv raw2 g + cv raw6 g + cv raw8 g + cv raw14 g = cv raw12 g + cv w0 g + cv w2 g + cv w5 g + cv w7 g + cv w8 g := by
  have h : (addP 6 raw0 (addP 6 raw2 (addP 6 raw6 (addP 6 raw8 (raw14))))) = (addP 6 raw12 (addP 6 w0 (addP 6 w2 (addP 6 w5 (addP 6 w7 (w8)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket108 (g) : cv raw6 g + cv raw8 g = cv raw19 g + cv raw22 g + cv w5 g + cv w7 g := by
  have h : (addP 6 raw6 (raw8)) = (addP 6 raw19 (addP 6 raw22 (addP 6 w5 (w7)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket113 (g) : cv raw2 g + cv raw18 g + cv raw23 g = cv raw4 g + cv raw12 g + cv raw17 g + cv w2 g + cv w13 g := by
  have h : (addP 6 raw2 (addP 6 raw18 (raw23))) = (addP 6 raw4 (addP 6 raw12 (addP 6 raw17 (addP 6 w2 (w13))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket114 (g) : cv raw2 g + cv raw8 g = cv raw4 g + cv raw10 g + cv w2 g + cv w7 g := by
  have h : (addP 6 raw2 (raw8)) = (addP 6 raw4 (addP 6 raw10 (addP 6 w2 (w7)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket116 (g) : cv raw8 g + cv raw14 g + cv raw16 g = cv raw10 g + cv raw20 g + cv raw22 g + cv w7 g + cv w8 g := by
  have h : (addP 6 raw8 (addP 6 raw14 (raw16))) = (addP 6 raw10 (addP 6 raw20 (addP 6 raw22 (addP 6 w7 (w8))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket120 (g) : cv raw14 g + cv raw18 g = cv raw12 g + cv raw20 g + cv w8 g := by
  have h : (addP 6 raw14 (raw18)) = (addP 6 raw12 (addP 6 raw20 (w8))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket135 (g) : cv raw14 g + cv raw18 g = cv raw12 g + cv raw20 g + cv w8 g := by
  have h : (addP 6 raw14 (raw18)) = (addP 6 raw12 (addP 6 raw20 (w8))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket139 (g) : cv raw8 g + cv raw14 g + cv raw16 g = cv raw10 g + cv raw20 g + cv raw22 g + cv w7 g + cv w8 g := by
  have h : (addP 6 raw8 (addP 6 raw14 (raw16))) = (addP 6 raw10 (addP 6 raw20 (addP 6 raw22 (addP 6 w7 (w8))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket141 (g) : cv raw2 g + cv raw8 g = cv raw4 g + cv raw10 g + cv w2 g + cv w7 g := by
  have h : (addP 6 raw2 (raw8)) = (addP 6 raw4 (addP 6 raw10 (addP 6 w2 (w7)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket142 (g) : cv raw2 g + cv raw18 g + cv raw23 g = cv raw4 g + cv raw12 g + cv raw17 g + cv w2 g + cv w13 g := by
  have h : (addP 6 raw2 (addP 6 raw18 (raw23))) = (addP 6 raw4 (addP 6 raw12 (addP 6 raw17 (addP 6 w2 (w13))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket147 (g) : cv raw6 g + cv raw8 g = cv raw19 g + cv raw22 g + cv w5 g + cv w7 g := by
  have h : (addP 6 raw6 (raw8)) = (addP 6 raw19 (addP 6 raw22 (addP 6 w5 (w7)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket149 (g) : cv raw0 g + cv raw2 g + cv raw6 g + cv raw8 g + cv raw14 g = cv raw12 g + cv w0 g + cv w2 g + cv w5 g + cv w7 g + cv w8 g := by
  have h : (addP 6 raw0 (addP 6 raw2 (addP 6 raw6 (addP 6 raw8 (raw14))))) = (addP 6 raw12 (addP 6 w0 (addP 6 w2 (addP 6 w5 (addP 6 w7 (w8)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket150 (g) : cv raw0 g + cv raw2 g + cv raw21 g + cv raw23 g = cv w0 g + cv w2 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw0 (addP 6 raw2 (addP 6 raw21 (raw23)))) = (addP 6 w0 (addP 6 w2 (addP 6 w12 (w13)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket153 (g) : cv raw0 g + cv raw5 g + cv raw14 g + cv raw16 g = cv w0 g + cv w4 g + cv w8 g := by
  have h : (addP 6 raw0 (addP 6 raw5 (addP 6 raw14 (raw16)))) = (addP 6 w0 (addP 6 w4 (w8))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket154 (g) : cv raw0 g + cv raw5 g + cv raw6 g + cv raw11 g + cv raw21 g = cv raw19 g + cv w0 g + cv w4 g + cv w5 g + cv w10 g + cv w12 g := by
  have h : (addP 6 raw0 (addP 6 raw5 (addP 6 raw6 (addP 6 raw11 (raw21))))) = (addP 6 raw19 (addP 6 w0 (addP 6 w4 (addP 6 w5 (addP 6 w10 (w12)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket156 (g) : cv raw6 g + cv raw11 g = cv raw12 g + cv raw17 g + cv w5 g + cv w10 g := by
  have h : (addP 6 raw6 (raw11)) = (addP 6 raw12 (addP 6 raw17 (addP 6 w5 (w10)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket163 (g) : cv raw6 g + cv raw7 g + cv raw18 g = cv raw12 g + cv raw13 g + cv raw19 g + cv w5 g + cv w6 g := by
  have h : (addP 6 raw6 (addP 6 raw7 (raw18))) = (addP 6 raw12 (addP 6 raw13 (addP 6 raw19 (addP 6 w5 (w6))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket165 (g) : cv raw0 g + cv raw1 g + cv raw6 g + cv raw7 g = cv w0 g + cv w1 g + cv w5 g + cv w6 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw6 (raw7)))) = (addP 6 w0 (addP 6 w1 (addP 6 w5 (w6)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket166 (g) : cv raw0 g + cv raw1 g + cv raw14 g + cv raw15 g + cv raw21 g = cv raw20 g + cv w0 g + cv w1 g + cv w8 g + cv w11 g + cv w12 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw14 (addP 6 raw15 (raw21))))) = (addP 6 raw20 (addP 6 w0 (addP 6 w1 (addP 6 w8 (addP 6 w11 (w12)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket169 (g) : cv raw0 g + cv raw1 g + cv raw2 g + cv raw3 g + cv raw5 g = cv raw4 g + cv w0 g + cv w1 g + cv w2 g + cv w3 g + cv w4 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw2 (addP 6 raw3 (raw5))))) = (addP 6 raw4 (addP 6 w0 (addP 6 w1 (addP 6 w2 (addP 6 w3 (w4)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket170 (g) : cv raw0 g + cv raw1 g + cv raw2 g + cv raw3 g + cv raw5 g + cv raw6 g + cv raw7 g + cv raw8 g + cv raw9 g + cv raw11 g + cv raw14 g + cv raw15 g + cv raw16 g + cv raw18 g + cv raw21 g + cv raw23 g = cv raw4 g + cv raw10 g + cv raw12 g + cv raw13 g + cv raw17 g + cv raw19 g + cv raw20 g + cv raw22 g + cv w0 g + cv w1 g + cv w2 g + cv w3 g + cv w4 g + cv w5 g + cv w6 g + cv w7 g + cv w8 g + cv w9 g + cv w10 g + cv w11 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw0 (addP 6 raw1 (addP 6 raw2 (addP 6 raw3 (addP 6 raw5 (addP 6 raw6 (addP 6 raw7 (addP 6 raw8 (addP 6 raw9 (addP 6 raw11 (addP 6 raw14 (addP 6 raw15 (addP 6 raw16 (addP 6 raw18 (addP 6 raw21 (raw23)))))))))))))))) = (addP 6 raw4 (addP 6 raw10 (addP 6 raw12 (addP 6 raw13 (addP 6 raw17 (addP 6 raw19 (addP 6 raw20 (addP 6 raw22 (addP 6 w0 (addP 6 w1 (addP 6 w2 (addP 6 w3 (addP 6 w4 (addP 6 w5 (addP 6 w6 (addP 6 w7 (addP 6 w8 (addP 6 w9 (addP 6 w10 (addP 6 w11 (addP 6 w12 (w13)))))))))))))))))))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket172 (g) : cv raw6 g + cv raw7 g + cv raw8 g + cv raw9 g + cv raw11 g = cv raw10 g + cv w5 g + cv w6 g + cv w7 g + cv w9 g + cv w10 g := by
  have h : (addP 6 raw6 (addP 6 raw7 (addP 6 raw8 (addP 6 raw9 (raw11))))) = (addP 6 raw10 (addP 6 w5 (addP 6 w6 (addP 6 w7 (addP 6 w9 (w10)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket177 (g) : cv raw2 g + cv raw3 g = cv raw12 g + cv raw13 g + cv w2 g + cv w3 g := by
  have h : (addP 6 raw2 (raw3)) = (addP 6 raw12 (addP 6 raw13 (addP 6 w2 (w3)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket178 (g) : cv raw2 g + cv raw3 g + cv raw8 g + cv raw9 g + cv raw23 g = cv raw22 g + cv w2 g + cv w3 g + cv w7 g + cv w9 g + cv w13 g := by
  have h : (addP 6 raw2 (addP 6 raw3 (addP 6 raw8 (addP 6 raw9 (raw23))))) = (addP 6 raw22 (addP 6 w2 (addP 6 w3 (addP 6 w7 (addP 6 w9 (w13)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket180 (g) : cv raw8 g + cv raw9 g + cv raw14 g + cv raw15 g = cv w7 g + cv w8 g + cv w9 g + cv w11 g := by
  have h : (addP 6 raw8 (addP 6 raw9 (addP 6 raw14 (raw15)))) = (addP 6 w7 (addP 6 w8 (addP 6 w9 (w11)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket184 (g) : cv raw14 g + cv raw15 g + cv raw16 g = cv raw12 g + cv raw13 g + cv raw17 g + cv w8 g + cv w11 g := by
  have h : (addP 6 raw14 (addP 6 raw15 (raw16))) = (addP 6 raw12 (addP 6 raw13 (addP 6 raw17 (addP 6 w8 (w11))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket195 (g) : cv raw7 g + cv raw16 g = cv raw10 g + cv raw13 g + cv w6 g := by
  have h : (addP 6 raw7 (raw16)) = (addP 6 raw10 (addP 6 raw13 (w6))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket197 (g) : cv raw1 g + cv raw7 g + cv raw18 g = cv raw4 g + cv raw10 g + cv raw20 g + cv w1 g + cv w6 g := by
  have h : (addP 6 raw1 (addP 6 raw7 (raw18))) = (addP 6 raw4 (addP 6 raw10 (addP 6 raw20 (addP 6 w1 (w6))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket198 (g) : cv raw1 g + cv raw15 g = cv raw4 g + cv raw17 g + cv w1 g + cv w11 g := by
  have h : (addP 6 raw1 (raw15)) = (addP 6 raw4 (addP 6 raw17 (addP 6 w1 (w11)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket201 (g) : cv raw1 g + cv raw3 g = cv raw20 g + cv raw22 g + cv w1 g + cv w3 g := by
  have h : (addP 6 raw1 (raw3)) = (addP 6 raw20 (addP 6 raw22 (addP 6 w1 (w3)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket202 (g) : cv raw1 g + cv raw3 g + cv raw7 g + cv raw9 g + cv raw15 g = cv raw13 g + cv w1 g + cv w3 g + cv w6 g + cv w9 g + cv w11 g := by
  have h : (addP 6 raw1 (addP 6 raw3 (addP 6 raw7 (addP 6 raw9 (raw15))))) = (addP 6 raw13 (addP 6 w1 (addP 6 w3 (addP 6 w6 (addP 6 w9 (w11)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket204 (g) : cv raw7 g + cv raw9 g + cv raw18 g + cv raw23 g = cv w6 g + cv w9 g + cv w13 g := by
  have h : (addP 6 raw7 (addP 6 raw9 (addP 6 raw18 (raw23)))) = (addP 6 w6 (addP 6 w9 (w13))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket209 (g) : cv raw3 g + cv raw5 g + cv raw16 g = cv raw13 g + cv raw19 g + cv raw22 g + cv w3 g + cv w4 g := by
  have h : (addP 6 raw3 (addP 6 raw5 (raw16))) = (addP 6 raw13 (addP 6 raw19 (addP 6 raw22 (addP 6 w3 (w4))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket210 (g) : cv raw3 g + cv raw5 g + cv raw9 g + cv raw11 g = cv w3 g + cv w4 g + cv w9 g + cv w10 g := by
  have h : (addP 6 raw3 (addP 6 raw5 (addP 6 raw9 (raw11)))) = (addP 6 w3 (addP 6 w4 (addP 6 w9 (w10)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket212 (g) : cv raw9 g + cv raw11 g + cv raw15 g + cv raw21 g + cv raw23 g = cv raw17 g + cv w9 g + cv w10 g + cv w11 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw9 (addP 6 raw11 (addP 6 raw15 (addP 6 raw21 (raw23))))) = (addP 6 raw17 (addP 6 w9 (addP 6 w10 (addP 6 w11 (addP 6 w12 (w13)))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket216 (g) : cv raw15 g + cv raw21 g = cv raw13 g + cv raw19 g + cv w11 g + cv w12 g := by
  have h : (addP 6 raw15 (raw21)) = (addP 6 raw13 (addP 6 raw19 (addP 6 w11 (w12)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket225 (g) : cv raw5 g + cv raw18 g = cv raw4 g + cv raw19 g + cv w4 g := by
  have h : (addP 6 raw5 (raw18)) = (addP 6 raw4 (addP 6 raw19 (w4))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket226 (g) : cv raw5 g + cv raw11 g + cv raw16 g = cv raw4 g + cv raw10 g + cv raw17 g + cv w4 g + cv w10 g := by
  have h : (addP 6 raw5 (addP 6 raw11 (raw16))) = (addP 6 raw4 (addP 6 raw10 (addP 6 raw17 (addP 6 w4 (w10))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket228 (g) : cv raw11 g + cv raw21 g = cv raw10 g + cv raw20 g + cv w10 g + cv w12 g := by
  have h : (addP 6 raw11 (raw21)) = (addP 6 raw10 (addP 6 raw20 (addP 6 w10 (w12)))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket232 (g) : cv raw18 g + cv raw21 g + cv raw23 g = cv raw19 g + cv raw20 g + cv raw22 g + cv w12 g + cv w13 g := by
  have h : (addP 6 raw18 (addP 6 raw21 (raw23))) = (addP 6 raw19 (addP 6 raw20 (addP 6 raw22 (addP 6 w12 (w13))))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private theorem bucket240 (g) : cv raw16 g + cv raw23 g = cv raw17 g + cv raw22 g + cv w13 g := by
  have h : (addP 6 raw16 (raw23)) = (addP 6 raw17 (addP 6 raw22 (w13))) := rfl
  simpa only [cv_add,add_assoc] using congrArg (fun x => cv x g) h
private def rawExpr (g) (a b : I4 → ℂ) := (0 : ℂ)
    + cv raw0 g * zval a b 0 1 2 3
    + cv raw1 g * zval a b 0 1 3 2
    + cv raw2 g * zval a b 0 2 1 3
    + cv raw3 g * zval a b 0 2 3 1
    - cv raw4 g * zval a b 0 3 1 2
    + cv raw5 g * zval a b 0 3 2 1
    + cv raw6 g * zval a b 1 0 2 3
    + cv raw7 g * zval a b 1 0 3 2
    + cv raw8 g * zval a b 1 2 0 3
    + cv raw9 g * zval a b 1 2 3 0
    - cv raw10 g * zval a b 1 3 0 2
    + cv raw11 g * zval a b 1 3 2 0
    - cv raw12 g * zval a b 2 0 1 3
    - cv raw13 g * zval a b 2 0 3 1
    + cv raw14 g * zval a b 2 1 0 3
    + cv raw15 g * zval a b 2 1 3 0
    + cv raw16 g * zval a b 2 3 0 1
    - cv raw17 g * zval a b 2 3 1 0
    + cv raw18 g * zval a b 3 0 1 2
    - cv raw19 g * zval a b 3 0 2 1
    - cv raw20 g * zval a b 3 1 0 2
    + cv raw21 g * zval a b 3 1 2 0
    - cv raw22 g * zval a b 3 2 0 1
    + cv raw23 g * zval a b 3 2 1 0
private def lawExpr (g) (a b : I4 → ℂ) := cv w0 g * zval a b 0 1 2 3
    + cv w1 g * zval a b 0 1 3 2
    + cv w2 g * zval a b 0 2 1 3
    + cv w3 g * zval a b 0 2 3 1
    + cv w4 g * zval a b 0 3 2 1
    + cv w5 g * zval a b 1 0 2 3
    + cv w6 g * zval a b 1 0 3 2
    + cv w7 g * zval a b 1 2 0 3
    + cv w8 g * zval a b 2 1 0 3
    + cv w9 g * zval a b 1 2 3 0
    + cv w10 g * zval a b 1 3 2 0
    + cv w11 g * zval a b 2 1 3 0
    + cv w12 g * zval a b 3 1 2 0
    + cv w13 g * zval a b 3 2 1 0
private theorem transfer (g) (a b : I4 → ℂ) : rawExpr g a b = lawExpr g a b := by
  unfold rawExpr lawExpr zval
  linear_combination
    (b 0) * (a 0) * (b 1) * (a 1) * (bucket15 g)
    + (b 0) * (a 0) * (b 1) * (b 2) * (bucket23 g)
    + (b 0) * (a 0) * (a 1) * (b 2) * (bucket27 g)
    + (b 0) * (b 1) * (a 1) * (b 2) * (bucket29 g)
    + (a 0) * (b 1) * (a 1) * (b 2) * (bucket30 g)
    + (b 0) * (a 0) * (b 1) * (a 2) * (bucket39 g)
    + (b 0) * (a 0) * (a 1) * (a 2) * (bucket43 g)
    + (b 0) * (b 1) * (a 1) * (a 2) * (bucket45 g)
    + (a 0) * (b 1) * (a 1) * (a 2) * (bucket46 g)
    + (b 0) * (a 0) * (b 2) * (a 2) * (bucket51 g)
    + (b 0) * (b 1) * (b 2) * (a 2) * (bucket53 g)
    + (a 0) * (b 1) * (b 2) * (a 2) * (bucket54 g)
    + (b 0) * (a 1) * (b 2) * (a 2) * (bucket57 g)
    + (a 0) * (a 1) * (b 2) * (a 2) * (bucket58 g)
    + (b 1) * (a 1) * (b 2) * (a 2) * (bucket60 g)
    + (b 0) * (a 0) * (b 1) * (b 3) * (bucket71 g)
    + (b 0) * (a 0) * (a 1) * (b 3) * (bucket75 g)
    + (b 0) * (b 1) * (a 1) * (b 3) * (bucket77 g)
    + (a 0) * (b 1) * (a 1) * (b 3) * (bucket78 g)
    + (b 0) * (a 0) * (b 2) * (b 3) * (bucket83 g)
    + (b 0) * (b 1) * (b 2) * (b 3) * (bucket85 g)
    + (a 0) * (b 1) * (b 2) * (b 3) * (bucket86 g)
    + (b 0) * (a 1) * (b 2) * (b 3) * (bucket89 g)
    + (a 0) * (a 1) * (b 2) * (b 3) * (bucket90 g)
    + (b 1) * (a 1) * (b 2) * (b 3) * (bucket92 g)
    + (b 0) * (a 0) * (a 2) * (b 3) * (bucket99 g)
    + (b 0) * (b 1) * (a 2) * (b 3) * (bucket101 g)
    + (a 0) * (b 1) * (a 2) * (b 3) * (bucket102 g)
    + (b 0) * (a 1) * (a 2) * (b 3) * (bucket105 g)
    + (a 0) * (a 1) * (a 2) * (b 3) * (bucket106 g)
    + (b 1) * (a 1) * (a 2) * (b 3) * (bucket108 g)
    + (b 0) * (b 2) * (a 2) * (b 3) * (bucket113 g)
    + (a 0) * (b 2) * (a 2) * (b 3) * (bucket114 g)
    + (b 1) * (b 2) * (a 2) * (b 3) * (bucket116 g)
    + (a 1) * (b 2) * (a 2) * (b 3) * (bucket120 g)
    + (b 0) * (a 0) * (b 1) * (a 3) * (bucket135 g)
    + (b 0) * (a 0) * (a 1) * (a 3) * (bucket139 g)
    + (b 0) * (b 1) * (a 1) * (a 3) * (bucket141 g)
    + (a 0) * (b 1) * (a 1) * (a 3) * (bucket142 g)
    + (b 0) * (a 0) * (b 2) * (a 3) * (bucket147 g)
    + (b 0) * (b 1) * (b 2) * (a 3) * (bucket149 g)
    + (a 0) * (b 1) * (b 2) * (a 3) * (bucket150 g)
    + (b 0) * (a 1) * (b 2) * (a 3) * (bucket153 g)
    + (a 0) * (a 1) * (b 2) * (a 3) * (bucket154 g)
    + (b 1) * (a 1) * (b 2) * (a 3) * (bucket156 g)
    + (b 0) * (a 0) * (a 2) * (a 3) * (bucket163 g)
    + (b 0) * (b 1) * (a 2) * (a 3) * (bucket165 g)
    + (a 0) * (b 1) * (a 2) * (a 3) * (bucket166 g)
    + (b 0) * (a 1) * (a 2) * (a 3) * (bucket169 g)
    + (a 0) * (a 1) * (a 2) * (a 3) * (bucket170 g)
    + (b 1) * (a 1) * (a 2) * (a 3) * (bucket172 g)
    + (b 0) * (b 2) * (a 2) * (a 3) * (bucket177 g)
    + (a 0) * (b 2) * (a 2) * (a 3) * (bucket178 g)
    + (b 1) * (b 2) * (a 2) * (a 3) * (bucket180 g)
    + (a 1) * (b 2) * (a 2) * (a 3) * (bucket184 g)
    + (b 0) * (a 0) * (b 3) * (a 3) * (bucket195 g)
    + (b 0) * (b 1) * (b 3) * (a 3) * (bucket197 g)
    + (a 0) * (b 1) * (b 3) * (a 3) * (bucket198 g)
    + (b 0) * (a 1) * (b 3) * (a 3) * (bucket201 g)
    + (a 0) * (a 1) * (b 3) * (a 3) * (bucket202 g)
    + (b 1) * (a 1) * (b 3) * (a 3) * (bucket204 g)
    + (b 0) * (b 2) * (b 3) * (a 3) * (bucket209 g)
    + (a 0) * (b 2) * (b 3) * (a 3) * (bucket210 g)
    + (b 1) * (b 2) * (b 3) * (a 3) * (bucket212 g)
    + (a 1) * (b 2) * (b 3) * (a 3) * (bucket216 g)
    + (b 0) * (a 2) * (b 3) * (a 3) * (bucket225 g)
    + (a 0) * (a 2) * (b 3) * (a 3) * (bucket226 g)
    + (b 1) * (a 2) * (b 3) * (a 3) * (bucket228 g)
    + (a 1) * (a 2) * (b 3) * (a 3) * (bucket232 g)
    + (b 2) * (a 2) * (b 3) * (a 3) * (bucket240 g)
private theorem clear0 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 0 * u 1 1 * u 2 2 * u 3 3) = -(sc l r) * cv raw0 g := by
  have h0 : (-(gap (0,1) g : ℂ)) * u 0 0 = l 0*r 0 := by
    simpa [den] using h (0 : I4) 0
  have h1 : (-(gap (2,3) g : ℂ)) * u 1 1 = l 1*r 1 := by
    simpa [den] using h (1 : I4) 1
  have h2 : (-(gap (4,5) g : ℂ)) * u 2 2 = l 2*r 2 := by
    simpa [den] using h (2 : I4) 2
  have h3 : ((1 : ℂ)) * u 3 3 = l 3*r 3 := by
    simpa [den] using h (3 : I4) 3
  calc _ = (-1 : ℂ) * ((-(gap (0,1) g : ℂ))*u 0 0) * ((-(gap (2,3) g : ℂ))*u 1 1) * ((-(gap (4,5) g : ℂ))*u 2 2) * (((1 : ℂ))*u 3 3) * cv raw0 g := by
              simp [clearD,cv,raw0,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear1 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 0 * u 1 1 * u 2 3 * u 3 2) = (sc l r) * cv raw1 g := by
  have h0 : (-(gap (0,1) g : ℂ)) * u 0 0 = l 0*r 0 := by
    simpa [den] using h (0 : I4) 0
  have h1 : (-(gap (2,3) g : ℂ)) * u 1 1 = l 1*r 1 := by
    simpa [den] using h (1 : I4) 1
  have h2 : ((gap (5,6) g : ℂ)) * u 2 3 = l 2*r 3 := by
    simpa [den] using h (2 : I4) 3
  have h3 : ((1 : ℂ)) * u 3 2 = l 3*r 2 := by
    simpa [den] using h (3 : I4) 2
  calc _ = (1 : ℂ) * ((-(gap (0,1) g : ℂ))*u 0 0) * ((-(gap (2,3) g : ℂ))*u 1 1) * (((gap (5,6) g : ℂ))*u 2 3) * (((1 : ℂ))*u 3 2) * cv raw1 g := by
              simp [clearD,cv,raw1,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear2 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 0 * u 1 2 * u 2 1 * u 3 3) = (sc l r) * cv raw2 g := by
  have h0 : (-(gap (0,1) g : ℂ)) * u 0 0 = l 0*r 0 := by
    simpa [den] using h (0 : I4) 0
  have h1 : ((gap (3,4) g : ℂ)) * u 1 2 = l 1*r 2 := by
    simpa [den] using h (1 : I4) 2
  have h2 : (-(gap (2,5) g : ℂ)) * u 2 1 = l 2*r 1 := by
    simpa [den] using h (2 : I4) 1
  have h3 : ((1 : ℂ)) * u 3 3 = l 3*r 3 := by
    simpa [den] using h (3 : I4) 3
  calc _ = (1 : ℂ) * ((-(gap (0,1) g : ℂ))*u 0 0) * (((gap (3,4) g : ℂ))*u 1 2) * ((-(gap (2,5) g : ℂ))*u 2 1) * (((1 : ℂ))*u 3 3) * cv raw2 g := by
              simp [clearD,cv,raw2,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear3 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 0 * u 1 2 * u 2 3 * u 3 1) = -(sc l r) * cv raw3 g := by
  have h0 : (-(gap (0,1) g : ℂ)) * u 0 0 = l 0*r 0 := by
    simpa [den] using h (0 : I4) 0
  have h1 : ((gap (3,4) g : ℂ)) * u 1 2 = l 1*r 2 := by
    simpa [den] using h (1 : I4) 2
  have h2 : ((gap (5,6) g : ℂ)) * u 2 3 = l 2*r 3 := by
    simpa [den] using h (2 : I4) 3
  have h3 : ((1 : ℂ)) * u 3 1 = l 3*r 1 := by
    simpa [den] using h (3 : I4) 1
  calc _ = (-1 : ℂ) * ((-(gap (0,1) g : ℂ))*u 0 0) * (((gap (3,4) g : ℂ))*u 1 2) * (((gap (5,6) g : ℂ))*u 2 3) * (((1 : ℂ))*u 3 1) * cv raw3 g := by
              simp [clearD,cv,raw3,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear4 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 0 * u 1 3 * u 2 1 * u 3 2) = (sc l r) * cv raw4 g := by
  have h0 : (-(gap (0,1) g : ℂ)) * u 0 0 = l 0*r 0 := by
    simpa [den] using h (0 : I4) 0
  have h1 : ((gap (3,6) g : ℂ)) * u 1 3 = l 1*r 3 := by
    simpa [den] using h (1 : I4) 3
  have h2 : (-(gap (2,5) g : ℂ)) * u 2 1 = l 2*r 1 := by
    simpa [den] using h (2 : I4) 1
  have h3 : ((1 : ℂ)) * u 3 2 = l 3*r 2 := by
    simpa [den] using h (3 : I4) 2
  calc _ = (1 : ℂ) * ((-(gap (0,1) g : ℂ))*u 0 0) * (((gap (3,6) g : ℂ))*u 1 3) * ((-(gap (2,5) g : ℂ))*u 2 1) * (((1 : ℂ))*u 3 2) * cv raw4 g := by
              simp [clearD,cv,raw4,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear5 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 0 * u 1 3 * u 2 2 * u 3 1) = (sc l r) * cv raw5 g := by
  have h0 : (-(gap (0,1) g : ℂ)) * u 0 0 = l 0*r 0 := by
    simpa [den] using h (0 : I4) 0
  have h1 : ((gap (3,6) g : ℂ)) * u 1 3 = l 1*r 3 := by
    simpa [den] using h (1 : I4) 3
  have h2 : (-(gap (4,5) g : ℂ)) * u 2 2 = l 2*r 2 := by
    simpa [den] using h (2 : I4) 2
  have h3 : ((1 : ℂ)) * u 3 1 = l 3*r 1 := by
    simpa [den] using h (3 : I4) 1
  calc _ = (1 : ℂ) * ((-(gap (0,1) g : ℂ))*u 0 0) * (((gap (3,6) g : ℂ))*u 1 3) * ((-(gap (4,5) g : ℂ))*u 2 2) * (((1 : ℂ))*u 3 1) * cv raw5 g := by
              simp [clearD,cv,raw5,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear6 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 1 * u 1 0 * u 2 2 * u 3 3) = (sc l r) * cv raw6 g := by
  have h0 : ((gap (1,2) g : ℂ)) * u 0 1 = l 0*r 1 := by
    simpa [den] using h (0 : I4) 1
  have h1 : (-(gap (0,3) g : ℂ)) * u 1 0 = l 1*r 0 := by
    simpa [den] using h (1 : I4) 0
  have h2 : (-(gap (4,5) g : ℂ)) * u 2 2 = l 2*r 2 := by
    simpa [den] using h (2 : I4) 2
  have h3 : ((1 : ℂ)) * u 3 3 = l 3*r 3 := by
    simpa [den] using h (3 : I4) 3
  calc _ = (1 : ℂ) * (((gap (1,2) g : ℂ))*u 0 1) * ((-(gap (0,3) g : ℂ))*u 1 0) * ((-(gap (4,5) g : ℂ))*u 2 2) * (((1 : ℂ))*u 3 3) * cv raw6 g := by
              simp [clearD,cv,raw6,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear7 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 1 * u 1 0 * u 2 3 * u 3 2) = -(sc l r) * cv raw7 g := by
  have h0 : ((gap (1,2) g : ℂ)) * u 0 1 = l 0*r 1 := by
    simpa [den] using h (0 : I4) 1
  have h1 : (-(gap (0,3) g : ℂ)) * u 1 0 = l 1*r 0 := by
    simpa [den] using h (1 : I4) 0
  have h2 : ((gap (5,6) g : ℂ)) * u 2 3 = l 2*r 3 := by
    simpa [den] using h (2 : I4) 3
  have h3 : ((1 : ℂ)) * u 3 2 = l 3*r 2 := by
    simpa [den] using h (3 : I4) 2
  calc _ = (-1 : ℂ) * (((gap (1,2) g : ℂ))*u 0 1) * ((-(gap (0,3) g : ℂ))*u 1 0) * (((gap (5,6) g : ℂ))*u 2 3) * (((1 : ℂ))*u 3 2) * cv raw7 g := by
              simp [clearD,cv,raw7,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear8 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 1 * u 1 2 * u 2 0 * u 3 3) = -(sc l r) * cv raw8 g := by
  have h0 : ((gap (1,2) g : ℂ)) * u 0 1 = l 0*r 1 := by
    simpa [den] using h (0 : I4) 1
  have h1 : ((gap (3,4) g : ℂ)) * u 1 2 = l 1*r 2 := by
    simpa [den] using h (1 : I4) 2
  have h2 : (-(gap (0,5) g : ℂ)) * u 2 0 = l 2*r 0 := by
    simpa [den] using h (2 : I4) 0
  have h3 : ((1 : ℂ)) * u 3 3 = l 3*r 3 := by
    simpa [den] using h (3 : I4) 3
  calc _ = (-1 : ℂ) * (((gap (1,2) g : ℂ))*u 0 1) * (((gap (3,4) g : ℂ))*u 1 2) * ((-(gap (0,5) g : ℂ))*u 2 0) * (((1 : ℂ))*u 3 3) * cv raw8 g := by
              simp [clearD,cv,raw8,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear9 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 1 * u 1 2 * u 2 3 * u 3 0) = (sc l r) * cv raw9 g := by
  have h0 : ((gap (1,2) g : ℂ)) * u 0 1 = l 0*r 1 := by
    simpa [den] using h (0 : I4) 1
  have h1 : ((gap (3,4) g : ℂ)) * u 1 2 = l 1*r 2 := by
    simpa [den] using h (1 : I4) 2
  have h2 : ((gap (5,6) g : ℂ)) * u 2 3 = l 2*r 3 := by
    simpa [den] using h (2 : I4) 3
  have h3 : ((1 : ℂ)) * u 3 0 = l 3*r 0 := by
    simpa [den] using h (3 : I4) 0
  calc _ = (1 : ℂ) * (((gap (1,2) g : ℂ))*u 0 1) * (((gap (3,4) g : ℂ))*u 1 2) * (((gap (5,6) g : ℂ))*u 2 3) * (((1 : ℂ))*u 3 0) * cv raw9 g := by
              simp [clearD,cv,raw9,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear10 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 1 * u 1 3 * u 2 0 * u 3 2) = -(sc l r) * cv raw10 g := by
  have h0 : ((gap (1,2) g : ℂ)) * u 0 1 = l 0*r 1 := by
    simpa [den] using h (0 : I4) 1
  have h1 : ((gap (3,6) g : ℂ)) * u 1 3 = l 1*r 3 := by
    simpa [den] using h (1 : I4) 3
  have h2 : (-(gap (0,5) g : ℂ)) * u 2 0 = l 2*r 0 := by
    simpa [den] using h (2 : I4) 0
  have h3 : ((1 : ℂ)) * u 3 2 = l 3*r 2 := by
    simpa [den] using h (3 : I4) 2
  calc _ = (-1 : ℂ) * (((gap (1,2) g : ℂ))*u 0 1) * (((gap (3,6) g : ℂ))*u 1 3) * ((-(gap (0,5) g : ℂ))*u 2 0) * (((1 : ℂ))*u 3 2) * cv raw10 g := by
              simp [clearD,cv,raw10,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear11 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 1 * u 1 3 * u 2 2 * u 3 0) = -(sc l r) * cv raw11 g := by
  have h0 : ((gap (1,2) g : ℂ)) * u 0 1 = l 0*r 1 := by
    simpa [den] using h (0 : I4) 1
  have h1 : ((gap (3,6) g : ℂ)) * u 1 3 = l 1*r 3 := by
    simpa [den] using h (1 : I4) 3
  have h2 : (-(gap (4,5) g : ℂ)) * u 2 2 = l 2*r 2 := by
    simpa [den] using h (2 : I4) 2
  have h3 : ((1 : ℂ)) * u 3 0 = l 3*r 0 := by
    simpa [den] using h (3 : I4) 0
  calc _ = (-1 : ℂ) * (((gap (1,2) g : ℂ))*u 0 1) * (((gap (3,6) g : ℂ))*u 1 3) * ((-(gap (4,5) g : ℂ))*u 2 2) * (((1 : ℂ))*u 3 0) * cv raw11 g := by
              simp [clearD,cv,raw11,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear12 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 2 * u 1 0 * u 2 1 * u 3 3) = (sc l r) * cv raw12 g := by
  have h0 : ((gap (1,4) g : ℂ)) * u 0 2 = l 0*r 2 := by
    simpa [den] using h (0 : I4) 2
  have h1 : (-(gap (0,3) g : ℂ)) * u 1 0 = l 1*r 0 := by
    simpa [den] using h (1 : I4) 0
  have h2 : (-(gap (2,5) g : ℂ)) * u 2 1 = l 2*r 1 := by
    simpa [den] using h (2 : I4) 1
  have h3 : ((1 : ℂ)) * u 3 3 = l 3*r 3 := by
    simpa [den] using h (3 : I4) 3
  calc _ = (1 : ℂ) * (((gap (1,4) g : ℂ))*u 0 2) * ((-(gap (0,3) g : ℂ))*u 1 0) * ((-(gap (2,5) g : ℂ))*u 2 1) * (((1 : ℂ))*u 3 3) * cv raw12 g := by
              simp [clearD,cv,raw12,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear13 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 2 * u 1 0 * u 2 3 * u 3 1) = -(sc l r) * cv raw13 g := by
  have h0 : ((gap (1,4) g : ℂ)) * u 0 2 = l 0*r 2 := by
    simpa [den] using h (0 : I4) 2
  have h1 : (-(gap (0,3) g : ℂ)) * u 1 0 = l 1*r 0 := by
    simpa [den] using h (1 : I4) 0
  have h2 : ((gap (5,6) g : ℂ)) * u 2 3 = l 2*r 3 := by
    simpa [den] using h (2 : I4) 3
  have h3 : ((1 : ℂ)) * u 3 1 = l 3*r 1 := by
    simpa [den] using h (3 : I4) 1
  calc _ = (-1 : ℂ) * (((gap (1,4) g : ℂ))*u 0 2) * ((-(gap (0,3) g : ℂ))*u 1 0) * (((gap (5,6) g : ℂ))*u 2 3) * (((1 : ℂ))*u 3 1) * cv raw13 g := by
              simp [clearD,cv,raw13,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear14 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 2 * u 1 1 * u 2 0 * u 3 3) = (sc l r) * cv raw14 g := by
  have h0 : ((gap (1,4) g : ℂ)) * u 0 2 = l 0*r 2 := by
    simpa [den] using h (0 : I4) 2
  have h1 : (-(gap (2,3) g : ℂ)) * u 1 1 = l 1*r 1 := by
    simpa [den] using h (1 : I4) 1
  have h2 : (-(gap (0,5) g : ℂ)) * u 2 0 = l 2*r 0 := by
    simpa [den] using h (2 : I4) 0
  have h3 : ((1 : ℂ)) * u 3 3 = l 3*r 3 := by
    simpa [den] using h (3 : I4) 3
  calc _ = (1 : ℂ) * (((gap (1,4) g : ℂ))*u 0 2) * ((-(gap (2,3) g : ℂ))*u 1 1) * ((-(gap (0,5) g : ℂ))*u 2 0) * (((1 : ℂ))*u 3 3) * cv raw14 g := by
              simp [clearD,cv,raw14,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear15 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 2 * u 1 1 * u 2 3 * u 3 0) = -(sc l r) * cv raw15 g := by
  have h0 : ((gap (1,4) g : ℂ)) * u 0 2 = l 0*r 2 := by
    simpa [den] using h (0 : I4) 2
  have h1 : (-(gap (2,3) g : ℂ)) * u 1 1 = l 1*r 1 := by
    simpa [den] using h (1 : I4) 1
  have h2 : ((gap (5,6) g : ℂ)) * u 2 3 = l 2*r 3 := by
    simpa [den] using h (2 : I4) 3
  have h3 : ((1 : ℂ)) * u 3 0 = l 3*r 0 := by
    simpa [den] using h (3 : I4) 0
  calc _ = (-1 : ℂ) * (((gap (1,4) g : ℂ))*u 0 2) * ((-(gap (2,3) g : ℂ))*u 1 1) * (((gap (5,6) g : ℂ))*u 2 3) * (((1 : ℂ))*u 3 0) * cv raw15 g := by
              simp [clearD,cv,raw15,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear16 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 2 * u 1 3 * u 2 0 * u 3 1) = -(sc l r) * cv raw16 g := by
  have h0 : ((gap (1,4) g : ℂ)) * u 0 2 = l 0*r 2 := by
    simpa [den] using h (0 : I4) 2
  have h1 : ((gap (3,6) g : ℂ)) * u 1 3 = l 1*r 3 := by
    simpa [den] using h (1 : I4) 3
  have h2 : (-(gap (0,5) g : ℂ)) * u 2 0 = l 2*r 0 := by
    simpa [den] using h (2 : I4) 0
  have h3 : ((1 : ℂ)) * u 3 1 = l 3*r 1 := by
    simpa [den] using h (3 : I4) 1
  calc _ = (-1 : ℂ) * (((gap (1,4) g : ℂ))*u 0 2) * (((gap (3,6) g : ℂ))*u 1 3) * ((-(gap (0,5) g : ℂ))*u 2 0) * (((1 : ℂ))*u 3 1) * cv raw16 g := by
              simp [clearD,cv,raw16,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear17 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 2 * u 1 3 * u 2 1 * u 3 0) = -(sc l r) * cv raw17 g := by
  have h0 : ((gap (1,4) g : ℂ)) * u 0 2 = l 0*r 2 := by
    simpa [den] using h (0 : I4) 2
  have h1 : ((gap (3,6) g : ℂ)) * u 1 3 = l 1*r 3 := by
    simpa [den] using h (1 : I4) 3
  have h2 : (-(gap (2,5) g : ℂ)) * u 2 1 = l 2*r 1 := by
    simpa [den] using h (2 : I4) 1
  have h3 : ((1 : ℂ)) * u 3 0 = l 3*r 0 := by
    simpa [den] using h (3 : I4) 0
  calc _ = (-1 : ℂ) * (((gap (1,4) g : ℂ))*u 0 2) * (((gap (3,6) g : ℂ))*u 1 3) * ((-(gap (2,5) g : ℂ))*u 2 1) * (((1 : ℂ))*u 3 0) * cv raw17 g := by
              simp [clearD,cv,raw17,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear18 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 3 * u 1 0 * u 2 1 * u 3 2) = (sc l r) * cv raw18 g := by
  have h0 : ((gap (1,6) g : ℂ)) * u 0 3 = l 0*r 3 := by
    simpa [den] using h (0 : I4) 3
  have h1 : (-(gap (0,3) g : ℂ)) * u 1 0 = l 1*r 0 := by
    simpa [den] using h (1 : I4) 0
  have h2 : (-(gap (2,5) g : ℂ)) * u 2 1 = l 2*r 1 := by
    simpa [den] using h (2 : I4) 1
  have h3 : ((1 : ℂ)) * u 3 2 = l 3*r 2 := by
    simpa [den] using h (3 : I4) 2
  calc _ = (1 : ℂ) * (((gap (1,6) g : ℂ))*u 0 3) * ((-(gap (0,3) g : ℂ))*u 1 0) * ((-(gap (2,5) g : ℂ))*u 2 1) * (((1 : ℂ))*u 3 2) * cv raw18 g := by
              simp [clearD,cv,raw18,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear19 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 3 * u 1 0 * u 2 2 * u 3 1) = (sc l r) * cv raw19 g := by
  have h0 : ((gap (1,6) g : ℂ)) * u 0 3 = l 0*r 3 := by
    simpa [den] using h (0 : I4) 3
  have h1 : (-(gap (0,3) g : ℂ)) * u 1 0 = l 1*r 0 := by
    simpa [den] using h (1 : I4) 0
  have h2 : (-(gap (4,5) g : ℂ)) * u 2 2 = l 2*r 2 := by
    simpa [den] using h (2 : I4) 2
  have h3 : ((1 : ℂ)) * u 3 1 = l 3*r 1 := by
    simpa [den] using h (3 : I4) 1
  calc _ = (1 : ℂ) * (((gap (1,6) g : ℂ))*u 0 3) * ((-(gap (0,3) g : ℂ))*u 1 0) * ((-(gap (4,5) g : ℂ))*u 2 2) * (((1 : ℂ))*u 3 1) * cv raw19 g := by
              simp [clearD,cv,raw19,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear20 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 3 * u 1 1 * u 2 0 * u 3 2) = (sc l r) * cv raw20 g := by
  have h0 : ((gap (1,6) g : ℂ)) * u 0 3 = l 0*r 3 := by
    simpa [den] using h (0 : I4) 3
  have h1 : (-(gap (2,3) g : ℂ)) * u 1 1 = l 1*r 1 := by
    simpa [den] using h (1 : I4) 1
  have h2 : (-(gap (0,5) g : ℂ)) * u 2 0 = l 2*r 0 := by
    simpa [den] using h (2 : I4) 0
  have h3 : ((1 : ℂ)) * u 3 2 = l 3*r 2 := by
    simpa [den] using h (3 : I4) 2
  calc _ = (1 : ℂ) * (((gap (1,6) g : ℂ))*u 0 3) * ((-(gap (2,3) g : ℂ))*u 1 1) * ((-(gap (0,5) g : ℂ))*u 2 0) * (((1 : ℂ))*u 3 2) * cv raw20 g := by
              simp [clearD,cv,raw20,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear21 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 3 * u 1 1 * u 2 2 * u 3 0) = (sc l r) * cv raw21 g := by
  have h0 : ((gap (1,6) g : ℂ)) * u 0 3 = l 0*r 3 := by
    simpa [den] using h (0 : I4) 3
  have h1 : (-(gap (2,3) g : ℂ)) * u 1 1 = l 1*r 1 := by
    simpa [den] using h (1 : I4) 1
  have h2 : (-(gap (4,5) g : ℂ)) * u 2 2 = l 2*r 2 := by
    simpa [den] using h (2 : I4) 2
  have h3 : ((1 : ℂ)) * u 3 0 = l 3*r 0 := by
    simpa [den] using h (3 : I4) 0
  calc _ = (1 : ℂ) * (((gap (1,6) g : ℂ))*u 0 3) * ((-(gap (2,3) g : ℂ))*u 1 1) * ((-(gap (4,5) g : ℂ))*u 2 2) * (((1 : ℂ))*u 3 0) * cv raw21 g := by
              simp [clearD,cv,raw21,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear22 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 3 * u 1 2 * u 2 0 * u 3 1) = -(sc l r) * cv raw22 g := by
  have h0 : ((gap (1,6) g : ℂ)) * u 0 3 = l 0*r 3 := by
    simpa [den] using h (0 : I4) 3
  have h1 : ((gap (3,4) g : ℂ)) * u 1 2 = l 1*r 2 := by
    simpa [den] using h (1 : I4) 2
  have h2 : (-(gap (0,5) g : ℂ)) * u 2 0 = l 2*r 0 := by
    simpa [den] using h (2 : I4) 0
  have h3 : ((1 : ℂ)) * u 3 1 = l 3*r 1 := by
    simpa [den] using h (3 : I4) 1
  calc _ = (-1 : ℂ) * (((gap (1,6) g : ℂ))*u 0 3) * (((gap (3,4) g : ℂ))*u 1 2) * ((-(gap (0,5) g : ℂ))*u 2 0) * (((1 : ℂ))*u 3 1) * cv raw22 g := by
              simp [clearD,cv,raw22,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring
private theorem clear23 (g) (l r : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    clearD g * (u 0 3 * u 1 2 * u 2 1 * u 3 0) = -(sc l r) * cv raw23 g := by
  have h0 : ((gap (1,6) g : ℂ)) * u 0 3 = l 0*r 3 := by
    simpa [den] using h (0 : I4) 3
  have h1 : ((gap (3,4) g : ℂ)) * u 1 2 = l 1*r 2 := by
    simpa [den] using h (1 : I4) 2
  have h2 : (-(gap (2,5) g : ℂ)) * u 2 1 = l 2*r 1 := by
    simpa [den] using h (2 : I4) 1
  have h3 : ((1 : ℂ)) * u 3 0 = l 3*r 0 := by
    simpa [den] using h (3 : I4) 0
  calc _ = (-1 : ℂ) * (((gap (1,6) g : ℂ))*u 0 3) * (((gap (3,4) g : ℂ))*u 1 2) * ((-(gap (2,5) g : ℂ))*u 2 1) * (((1 : ℂ))*u 3 0) * cv raw23 g := by
              simp [clearD,cv,raw23,ev_prod] <;> ring
       _ = _ := by rw [h0,h1,h2,h3]; unfold sc; ring

private def pencil (a b : I4 → ℂ) (u : Mat) : Mat := Matrix.of fun i j => (a i+b j)*u i j
private theorem clear_pencil (g) (l r a b : I4 → ℂ) (u : Mat)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    -(clearD g) * (pencil a b u).det = sc l r * lawExpr g a b := by
  rw [← transfer,det_four]
  simp only [pencil,Matrix.of_apply,rawExpr,zval]
  linear_combination
    - (a 0 + b 0) * (a 1 + b 1) * (a 2 + b 2) * (a 3 + b 3) * (clear0 g l r u h)
    + (a 0 + b 0) * (a 1 + b 1) * (a 2 + b 3) * (a 3 + b 2) * (clear1 g l r u h)
    + (a 0 + b 0) * (a 1 + b 2) * (a 2 + b 1) * (a 3 + b 3) * (clear2 g l r u h)
    - (a 0 + b 0) * (a 1 + b 2) * (a 2 + b 3) * (a 3 + b 1) * (clear3 g l r u h)
    - (a 0 + b 0) * (a 1 + b 3) * (a 2 + b 1) * (a 3 + b 2) * (clear4 g l r u h)
    + (a 0 + b 0) * (a 1 + b 3) * (a 2 + b 2) * (a 3 + b 1) * (clear5 g l r u h)
    + (a 0 + b 1) * (a 1 + b 0) * (a 2 + b 2) * (a 3 + b 3) * (clear6 g l r u h)
    - (a 0 + b 1) * (a 1 + b 0) * (a 2 + b 3) * (a 3 + b 2) * (clear7 g l r u h)
    - (a 0 + b 1) * (a 1 + b 2) * (a 2 + b 0) * (a 3 + b 3) * (clear8 g l r u h)
    + (a 0 + b 1) * (a 1 + b 2) * (a 2 + b 3) * (a 3 + b 0) * (clear9 g l r u h)
    + (a 0 + b 1) * (a 1 + b 3) * (a 2 + b 0) * (a 3 + b 2) * (clear10 g l r u h)
    - (a 0 + b 1) * (a 1 + b 3) * (a 2 + b 2) * (a 3 + b 0) * (clear11 g l r u h)
    - (a 0 + b 2) * (a 1 + b 0) * (a 2 + b 1) * (a 3 + b 3) * (clear12 g l r u h)
    + (a 0 + b 2) * (a 1 + b 0) * (a 2 + b 3) * (a 3 + b 1) * (clear13 g l r u h)
    + (a 0 + b 2) * (a 1 + b 1) * (a 2 + b 0) * (a 3 + b 3) * (clear14 g l r u h)
    - (a 0 + b 2) * (a 1 + b 1) * (a 2 + b 3) * (a 3 + b 0) * (clear15 g l r u h)
    - (a 0 + b 2) * (a 1 + b 3) * (a 2 + b 0) * (a 3 + b 1) * (clear16 g l r u h)
    + (a 0 + b 2) * (a 1 + b 3) * (a 2 + b 1) * (a 3 + b 0) * (clear17 g l r u h)
    + (a 0 + b 3) * (a 1 + b 0) * (a 2 + b 1) * (a 3 + b 2) * (clear18 g l r u h)
    - (a 0 + b 3) * (a 1 + b 0) * (a 2 + b 2) * (a 3 + b 1) * (clear19 g l r u h)
    - (a 0 + b 3) * (a 1 + b 1) * (a 2 + b 0) * (a 3 + b 2) * (clear20 g l r u h)
    + (a 0 + b 3) * (a 1 + b 1) * (a 2 + b 2) * (a 3 + b 0) * (clear21 g l r u h)
    + (a 0 + b 3) * (a 1 + b 2) * (a 2 + b 0) * (a 3 + b 1) * (clear22 g l r u h)
    - (a 0 + b 3) * (a 1 + b 2) * (a 2 + b 1) * (a 3 + b 0) * (clear23 g l r u h)
def weight : Fin 14 → P 6 := ![w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11,w12,w13]
private def p0 : Equiv.Perm I4 := Equiv.ofBijective ![0,1,2,3] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p1 : Equiv.Perm I4 := Equiv.ofBijective ![0,1,3,2] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p2 : Equiv.Perm I4 := Equiv.ofBijective ![0,2,1,3] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p3 : Equiv.Perm I4 := Equiv.ofBijective ![0,2,3,1] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p4 : Equiv.Perm I4 := Equiv.ofBijective ![0,3,2,1] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p5 : Equiv.Perm I4 := Equiv.ofBijective ![1,0,2,3] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p6 : Equiv.Perm I4 := Equiv.ofBijective ![1,0,3,2] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p7 : Equiv.Perm I4 := Equiv.ofBijective ![1,2,0,3] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p8 : Equiv.Perm I4 := Equiv.ofBijective ![2,1,0,3] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p9 : Equiv.Perm I4 := Equiv.ofBijective ![1,2,3,0] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p10 : Equiv.Perm I4 := Equiv.ofBijective ![1,3,2,0] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p11 : Equiv.Perm I4 := Equiv.ofBijective ![2,1,3,0] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p12 : Equiv.Perm I4 := Equiv.ofBijective ![3,1,2,0] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
private def p13 : Equiv.Perm I4 := Equiv.ofBijective ![3,2,1,0] (Finite.injective_iff_bijective.mp (by
  intro i j; fin_cases i <;> fin_cases j <;> decide))
def perm : Fin 14 → Equiv.Perm I4 := ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13]
def mass (g : Nat → ℝ) := ∑ k, ev 6 (weight k) g

private theorem law_sum (g : Nat → ℝ) (a b : I4 → ℂ) :
    lawExpr g a b = ∑ k, (ev 6 (weight k) g : ℂ) * ∏ i, (a i+b (perm k i)) := by
  simp [lawExpr,weight,perm,cv,zval,p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11,p12,p13,Fin.sum_univ_succ,Fin.prod_univ_succ] <;> ring

private theorem clear_nonzero (g : Nat → ℝ) (hg : ∀ i, 0<g i) : clearD g ≠ 0 := by
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  have h3 := hg 3
  have h4 := hg 4
  have h5 := hg 5
  have ne0 : (gap (0,1) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 0 + 0)
    positivity))
  have ne1 : (gap (1,2) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 1 + 0)
    positivity))
  have ne2 : (gap (1,4) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 1 + (g 2 + (g 3 + 0)))
    positivity))
  have ne3 : (gap (1,6) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 1 + (g 2 + (g 3 + (g 4 + (g 5 + 0)))))
    positivity))
  have ne4 : (gap (0,3) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 0 + (g 1 + (g 2 + 0)))
    positivity))
  have ne5 : (gap (2,3) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 2 + 0)
    positivity))
  have ne6 : (gap (3,4) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 3 + 0)
    positivity))
  have ne7 : (gap (3,6) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 3 + (g 4 + (g 5 + 0)))
    positivity))
  have ne8 : (gap (0,5) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 0 + (g 1 + (g 2 + (g 3 + (g 4 + 0)))))
    positivity))
  have ne9 : (gap (2,5) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 2 + (g 3 + (g 4 + 0)))
    positivity))
  have ne10 : (gap (4,5) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 4 + 0)
    positivity))
  have ne11 : (gap (5,6) g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by
    change 0 < (g 5 + 0)
    positivity))
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ne0 ne1) ne2) ne3) ne4) ne5) ne6) ne7) ne8) ne9) ne10) ne11)

/-- The same 14 probabilities work simultaneously for all complex spectra:
the displayed weights depend only on the six interlacing gaps. -/
theorem arrowhead_identity (a b l r : I4 → ℂ) (g : Nat → ℝ) (hg : ∀ i, 0<g i)
    (u : Matrix (Fin 4) (Fin 4) ℂ) (hu : uᴴ*u=1)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    0 < mass g ∧ (Matrix.diagonal a + u*Matrix.diagonal b*uᴴ).det =
      ∑ k, (ev 6 (weight k) g / mass g) • (∏ i, (a i+b (perm k i))) := by
  classical
  have hp : (Matrix.diagonal a + u*Matrix.diagonal b*uᴴ)*u = pencil a b u := by
    rw [add_mul, Matrix.mul_assoc (u*Matrix.diagonal b),hu,mul_one]
    ext i j
    simp [pencil,Matrix.diagonal_mul,Matrix.mul_diagonal] <;> ring
  have h1 : pencil (fun _ => 1) (fun _ => 0) u = u := by ext; simp [pencil]
  have C := clear_pencil g l r (fun _ => 1) (fun _ => 0) u h
  rw [h1,law_sum] at C
  have C' : -(clearD g)*u.det = sc l r * (mass g : ℂ) := by simpa [mass] using C
  have hud : u.det ≠ 0 := by
    have hh := congrArg Matrix.det hu
    rw [Matrix.det_mul, Matrix.det_one] at hh
    intro hz
    simp [hz] at hh
  have hn : sc l r * (mass g : ℂ) ≠ 0 := C' ▸ mul_ne_zero (neg_ne_zero.mpr (clear_nonzero g hg)) hud
  have hn' : mass g ≠ 0 := by intro hz; simp [hz] at hn
  have hn'' : sc l r ≠ 0 := left_ne_zero_of_mul hn
  have hg' : 0 < mass g := lt_of_le_of_ne
    (Finset.sum_nonneg fun k _ => ev_nonneg 6 (weight k) g (fun i => (hg i).le)) hn'.symm
  have cc := clear_pencil g l r a b u h
  rw [← hp,Matrix.det_mul] at cc
  have D : (Matrix.diagonal a + u*Matrix.diagonal b*uᴴ).det * (mass g : ℂ) = lawExpr g a b := by
    apply mul_left_cancel₀ hn''
    linear_combination cc - (Matrix.diagonal a + u*Matrix.diagonal b*uᴴ).det * C'
  have zz : (Matrix.diagonal a + u*Matrix.diagonal b*uᴴ).det =
      ∑ k, (ev 6 (weight k) g / mass g) • (∏ i, (a i+b (perm k i))) := by
    apply mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr hn')
    rw [D,law_sum,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    simp [Complex.real_smul]
    field_simp [hn']
  exact ⟨hg',zz⟩

/-- Determinant containment for every interlacing Cauchy unitary, including
arbitrary row and column phases. The hypothesis on u is its rank-one
displacement representation, not a hypothesis about minors or convex weights. -/
theorem arrowhead (a b l r : I4 → ℂ) (g : Nat → ℝ) (hg : ∀ i, 0<g i)
    (u : Matrix (Fin 4) (Fin 4) ℂ) (hu : uᴴ*u=1)
    (h : ∀ i j, (den g i j : ℂ)*u i j = l i*r j) :
    (Matrix.diagonal a + u*Matrix.diagonal b*uᴴ).det ∈ convexHull ℝ
      (Set.range (fun p : Equiv.Perm I4 => ∏ i, (a i+b (p i)))) := by
  obtain ⟨hg',zz⟩ := arrowhead_identity a b l r g hg u hu h
  have hn' := hg'.ne'
  rw [zz]
  apply (convex_convexHull ℝ _).sum_mem
  · exact fun k _ => div_nonneg (ev_nonneg 6 _ g (fun i => (hg i).le)) hg'.le
  · simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hn'
  · exact fun k _ => subset_convexHull ℝ _ ⟨perm k,rfl⟩

end MOCCauchy
