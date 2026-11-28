import Conjectures.MarcusDeOliveira.Arrowhead
import Conjectures.MarcusDeOliveira.MinorBridge

/-! Exact law for the *actual eigenvectors* of an interlacing Hermitian
arrowhead: all 70 squared minors are reproduced by the same 14 noncrossing
permutations, and the same law reproduces every complex determinant pencil. -/
noncomputable section
namespace MOCArrowheadBasis
open Matrix MOCCauchy MOCMatching
open scoped Matrix BigOperators

private def gaps (z : Fin 7 → ℝ) (k : ℕ) : ℝ :=
  if h : k < 6 then z ⟨k+1,by omega⟩ - z ⟨k,by omega⟩ else 1

private theorem gaps_pos (z : Fin 7 → ℝ) (hz : StrictMono z) (k : ℕ) :
    0 < gaps z k := by
  unfold gaps
  split
  · apply sub_pos.mpr
    apply hz
    exact Nat.lt_succ_self k
  · exact zero_lt_one

def roots (z : Fin 7 → ℝ) : Fin 4 → ℂ := ![(z 0:ℂ),(z 2:ℂ),(z 4:ℂ),(z 6:ℂ)]
def poles (z : Fin 7 → ℝ) : Fin 4 → ℝ := ![z 1,z 3,z 5,0]
private def signed (z : Fin 7 → ℝ) (i j : Fin 4) : ℝ :=
  if i=3 then 1 else (![z 0,z 2,z 4,z 6] j) - poles z i

private theorem den_eq (z : Fin 7 → ℝ) (i j : Fin 4) : den (gaps z) i j = signed z i j := by
  fin_cases i <;> fin_cases j
  · change -((z 1 - z 0) + 0) = z 0 - z 1
    ring
  · change ((z 2 - z 1) + 0) = z 2 - z 1
    ring
  · change ((z 2 - z 1) + ((z 3 - z 2) + ((z 4 - z 3) + 0))) = z 4 - z 1
    ring
  · change ((z 2 - z 1) + ((z 3 - z 2) + ((z 4 - z 3) + ((z 5 - z 4) + ((z 6 - z 5) + 0))))) = z 6 - z 1
    ring
  · change -((z 1 - z 0) + ((z 2 - z 1) + ((z 3 - z 2) + 0))) = z 0 - z 3
    ring
  · change -((z 3 - z 2) + 0) = z 2 - z 3
    ring
  · change ((z 4 - z 3) + 0) = z 4 - z 3
    ring
  · change ((z 4 - z 3) + ((z 5 - z 4) + ((z 6 - z 5) + 0))) = z 6 - z 3
    ring
  · change -((z 1 - z 0) + ((z 2 - z 1) + ((z 3 - z 2) + ((z 4 - z 3) + ((z 5 - z 4) + 0))))) = z 0 - z 5
    ring
  · change -((z 3 - z 2) + ((z 4 - z 3) + ((z 5 - z 4) + 0))) = z 2 - z 5
    ring
  · change -((z 5 - z 4) + 0) = z 4 - z 5
    ring
  · change ((z 6 - z 5) + 0) = z 6 - z 5
    ring
  · rfl
  · rfl
  · rfl
  · rfl

/-- Rows 0,1,2 are the peripheral poles; row 3 is the center. -/
def arrow (z : Fin 7 → ℝ) (c : Fin 4 → ℂ) (d : ℝ) : Mat := Matrix.of fun i j =>
  if i=3 then (if j=3 then (d:ℂ) else star (c j))
  else if j=3 then c i else if i=j then (poles z i : ℂ) else 0

private def coupling (c : Fin 4 → ℂ) (i : Fin 4) : ℂ := if i=3 then 1 else c i

private theorem displacement (z : Fin 7 → ℝ) (c : Fin 4 → ℂ) (d : ℝ) (u : Mat)
    (heig : arrow z c d * u = u * diagonal (roots z)) (i j : Fin 4) :
    (den (gaps z) i j : ℂ) * u i j = coupling c i * u 3 j := by
  rw [den_eq]
  have H := congrFun (congrFun heig i) j
  simp only [Matrix.mul_diagonal] at H
  fin_cases i
  · simp [Matrix.mul_apply,Fin.sum_univ_succ,arrow,poles] at H
    change ((![z 0,z 2,z 4,z 6] j - z 1 : ℝ) : ℂ)*u 0 j = c 0*u 3 j
    have hr : roots z j = (![z 0,z 2,z 4,z 6] j : ℝ) := by fin_cases j <;> rfl
    rw [hr] at H
    simp only [Complex.ofReal_sub]; linear_combination -H
  · simp [Matrix.mul_apply,Fin.sum_univ_succ,arrow,poles] at H
    change ((![z 0,z 2,z 4,z 6] j - z 3 : ℝ) : ℂ)*u 1 j = c 1*u 3 j
    have hr : roots z j = (![z 0,z 2,z 4,z 6] j : ℝ) := by fin_cases j <;> rfl
    rw [hr] at H
    simp only [Complex.ofReal_sub]; linear_combination -H
  · simp [Matrix.mul_apply,Fin.sum_univ_succ,arrow,poles] at H
    change ((![z 0,z 2,z 4,z 6] j - z 5 : ℝ) : ℂ)*u 2 j = c 2*u 3 j
    have hr : roots z j = (![z 0,z 2,z 4,z 6] j : ℝ) := by fin_cases j <;> rfl
    rw [hr] at H
    simp only [Complex.ofReal_sub]; linear_combination -H
  · simp [signed,coupling]

/-- Cyclic order of nodes is root,pole,root,pole,root,pole,root,infinity. -/
def chordsOf (p : Equiv.Perm (Fin 4)) : List (ℕ × ℕ) := (List.finRange 4).map fun i =>
  (min (2*i.val+1) (2*(p i).val),max (2*i.val+1) (2*(p i).val))
def planar (p : Equiv.Perm (Fin 4)) : Bool := (chordsOf p).all fun e =>
  (chordsOf p).all fun f => !(decide (e.1<f.1 ∧ f.1<e.2 ∧ e.2<f.2))
theorem noncrossing (k : Fin 14) : planar (perm k) = true := by fin_cases k <;> rfl
theorem distinct_support : (List.ofFn fun k : Fin 14 => chordsOf (perm k)).Nodup := by decide

def prob (z : Fin 7 → ℝ) (k : Fin 14) := ev 6 (weight k) (gaps z) / mass (gaps z)

/-- A probability law independent of a,b, for every interlacing arrowhead
orthonormal eigenbasis. The statement assumes the eigenvector equation itself,
not a Vandermonde minor formula, a convex representation, or a positivity
certificate. -/
theorem eigenbasis_law (z : Fin 7 → ℝ) (hz : StrictMono z)
    (c : Fin 4 → ℂ) (d : ℝ) (u : Mat) (hu : uᴴ*u=1)
    (heig : arrow z c d * u = u * diagonal (roots z)) :
    (∀ k, 0 ≤ prob z k) ∧ (∑ k, prob z k) = 1 ∧
    ∀ a b : Fin 4 → ℂ, (diagonal a + u*diagonal b*uᴴ).det =
      ∑ k, prob z k • ∏ i, (a i+b (perm k i)) := by
  have H (a b : Fin 4 → ℂ) := arrowhead_identity a b (coupling c) (u 3) (gaps z)
    (gaps_pos z hz) u hu (displacement z c d u heig)
  have hm := (H 0 0).1
  refine ⟨(fun k => div_nonneg (ev_nonneg _ _ _ (fun i => (gaps_pos z hz i).le)) hm.le),?_,fun a b => (H a b).2⟩
  simp only [prob,div_eq_mul_inv,← Finset.sum_mul]
  exact mul_inv_cancel₀ hm.ne'

theorem eigenbasis_moc (z : Fin 7 → ℝ) (hz : StrictMono z)
    (c : Fin 4 → ℂ) (d : ℝ) (u : Mat) (hu : uᴴ*u=1)
    (heig : arrow z c d * u = u * diagonal (roots z)) (a b : Fin 4 → ℂ) :
    (diagonal a + u*diagonal b*uᴴ).det ∈ convexHull ℝ
      (Set.range (fun p : Equiv.Perm (Fin 4) => ∏ i, (a i+b (p i)))) :=
  arrowhead a b (coupling c) (u 3) (gaps z) (gaps_pos z hz) u hu
    (displacement z c d u heig)

/-- Arbitrary choices of equal-sized row and column sets (first summands
under independent orderings e and f), including the empty and full minor. -/
theorem eigenbasis_all_minors {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (z : Fin 7 → ℝ) (hz : StrictMono z) (c : Fin 4 → ℂ) (d : ℝ)
    (u : Mat) (hu : uᴴ*u=1) (heig : arrow z c d * u = u * diagonal (roots z))
    (e f : (m ⊕ n) ≃ Fin 4) :
    MOCMinorBridge.energy u e f =
      ∑ k, prob z k * MOCMinorBridge.energy ((perm k).permMatrix ℂ) e f :=
  MOCMinorBridge.all_minors _ _ _ (eigenbasis_law z hz c d u hu heig).2.2 e f

end MOCArrowheadBasis
