import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Push

/-! Accounting for a connected thrackle core in its cellular parity embedding.
The edge/vertex ratio reduction below is also valid without any embedding.
All densities and payments are rational numbers. -/
namespace ConwayThrackle
open Finset
open scoped BigOperators

section Accounting
variable {S Y : Type*} [Fintype S] [Fintype Y] [DecidableEq Y]

/-- A weighted sum over incidences with a given vertex or face. -/
def fiber (p : S → Y) (q : S → ℚ) (y : Y) : ℚ :=
  ∑ i, if p i = y then q i else 0

theorem sum_fiber (p : S → Y) (q : S → ℚ) :
    ∑ y, fiber p q y = ∑ i, q i := by
  classical
  unfold fiber
  rw [Finset.sum_comm]
  simp

theorem weighted_fiber (p : S → Y) (q : S → ℚ) (a : Y → ℚ) :
    ∑ i, a (p i) * q i = ∑ y, a y * fiber p q y := by
  classical
  simp_rw [fiber, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_ite]

/-- A branch corner of degree three earns 1; degree four earns 3/2.
Suppressing bivalent vertices does not alter the sum: their term is zero. -/
def curvature (p : S → Y) (i : S) : ℚ :=
  3 - 6 / fiber p (fun _ => 1) (p i)

theorem curvature_total (p : S → Y) (h : ∀ y, fiber p (fun _ => 1) y ≠ 0) :
    ∑ i, curvature p i = 3 * Fintype.card S - 6 * Fintype.card Y := by
  have e := weighted_fiber p (fun _ => (1:ℚ))
    (fun y => 6 / fiber p (fun _ => 1) y)
  simp only [mul_one, div_mul_cancel₀ _ (h _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at e
  simp [curvature, Finset.sum_sub_distrib, e]
  ring

/-- Cellular accounting. The two equations are the topological Euler equation and
the edge-side count, not an average face-degree assumption. The per-face inequality
is a separate, replaceable discharging obligation. -/
theorem surface_account {V F : Type*} [Fintype V] [Fintype F]
    [DecidableEq V] [DecidableEq F] (p : S → V) (f : S → F)
    (mate : S ≃ S) (pay : S → ℚ) (m χ δ h : ℚ)
    (hu : ∀ v, fiber p (fun _ => 1) v ≠ 0)
    (hEuler : (Fintype.card V : ℚ) - m + Fintype.card F = χ)
    (hSides : (Fintype.card S : ℚ) = 2 * m)
    (localCharge : ∀ y, δ ≤ fiber f (fun _ => 1) y + h * (fiber f (curvature p) y - 6)
            + fiber f (fun i => pay (mate i) - pay i) y) :
    (δ - 2) * m ≤ δ * Fintype.card V - (δ + 6*h)*χ := by
  have e := Finset.sum_le_sum (s := (Finset.univ : Finset F)) (fun y _ => localCharge y)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, sum_fiber,
    curvature_total p hu, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at e
  rw [mate.sum_comp pay, sub_self, add_zero, hSides] at e
  linear_combination (norm := ring_nf) e - (δ + 6*h) * hEuler ; norm_num

end Accounting

/-- This target preserves the four-vertex triangle with a leaf. -/
def target (a : ℚ) (n : ℕ) : ℚ := max (n : ℚ) (a * ((n : ℚ) - 1))

theorem target_lift (a : ℚ) (ha : 1 ≤ a) (n : ℕ) :
    target a n + 1 ≤ target a (n+1) := by
  unfold target
  push_cast
  rcases le_total (n:ℚ) (a*(n-1)) with h | h
  · rw [max_eq_right h]
    apply le_trans _ (le_max_right _ _)
    linarith
  · rw [max_eq_left h]
    exact le_max_left _ _

theorem target_join (a : ℚ) (ha : 1 ≤ a) (n k : ℕ) :
    target a n + target a k ≤ target a (n+k) := by
  unfold target
  push_cast
  have hn : (0:ℚ) ≤ n := by positivity
  have hk : (0:ℚ) ≤ k := by positivity
  rcases le_total (n:ℚ) (a*(n-1)) with hx | hx <;>
    rcases le_total (k:ℚ) (a*(k-1)) with hy | hy
  · rw [max_eq_right hx, max_eq_right hy]
    apply le_trans _ (le_max_right _ _)
    linarith only [ha]
  · rw [max_eq_right hx, max_eq_left hy]
    apply le_trans _ (le_max_right _ _)
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hk]
  · rw [max_eq_left hx, max_eq_right hy]
    apply le_trans _ (le_max_right _ _)
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha) hn]
  · rw [max_eq_left hx, max_eq_left hy]
    exact le_max_left _ _

section Reduction
variable {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Edges of the induced graph on U; endpoint input also represents parallel
edges faithfully. The reduction does not require simplicity. -/
def onEdges (a b : E → V) (U : Finset V) : Finset E :=
  Finset.univ.filter fun e => a e ∈ U ∧ b e ∈ U

def incident (a b : E → V) (U : Finset V) (x : V) : Finset E :=
  (onEdges a b U).filter fun e => a e = x ∨ b e = x

/-- Connected via the nonexistence of a nonempty two-part separation.
Empty sets cause no ambiguity in the reduction, as they have no edges. -/
def conn (a b : E → V) (U : Finset V) : Prop :=
  ¬ ∃ A B : Finset V, A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧ U = A ∪ B ∧
    onEdges a b U = onEdges a b A ∪ onEdges a b B

def NoSmallBicyclic (a b : E → V) (N : ℕ) : Prop :=
  ∀ U : Finset V, U.card ≤ N → (onEdges a b U).card ≤ U.card

omit [DecidableEq E] in
/-- A rank-two support supplies a lower edge-count bound, even if a walk
revisits vertices or sides. The witnesses here are actual vertex/edge sets. -/
theorem bicycle_capacity (a b : E → V) {N : ℕ} (hn : NoSmallBicyclic a b N)
    (U : Finset V) (W : Finset E) (inc : W ⊆ onEdges a b U)
    (rank : U.card < W.card) : N+2 ≤ W.card := by
  by_contra! bad
  have h : U.card ≤ N := by omega
  have := le_trans (Finset.card_le_card inc) (hn U h)
  omega

omit [DecidableEq E] in
theorem remove_count (a b : E → V) (U : Finset V) (x : V) :
    (onEdges a b (U.erase x)).card + (incident a b U x).card =
      (onEdges a b U).card := by
  have eqn : onEdges a b (U.erase x) =
      (onEdges a b U).filter (fun e => ¬(a e = x ∨ b e = x)) := by
    ext e
    simp [onEdges, Finset.mem_erase]
    tauto
  rw [eqn, add_comm]
  apply Finset.card_filter_add_card_filter_not

theorem forest_reduction (a b : E → V) (α : ℚ) (ha : 1 ≤ α)
    (core : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card →
       ((onEdges a b U).card : ℚ) ≤ α*((U.card:ℚ)-1))
    (U : Finset V) : ((onEdges a b U).card : ℚ) ≤ target α U.card := by
  classical
  induction U using Finset.strongInductionOn
  rename_i U ih
  by_cases hc : U.card < (onEdges a b U).card
  · by_cases hconn : conn a b U
    · by_cases mindeg : ∀ x ∈ U, 2 ≤ (incident a b U x).card
      · exact le_trans (core U hconn mindeg hc) (le_max_right ..)
      · push Not at mindeg
        obtain ⟨x,hx,low⟩ := mindeg
        have small := ih (U.erase x) (Finset.erase_ssubset hx)
        have ct := remove_count a b U x
        have cv := Finset.card_erase_add_one hx
        have ll := target_lift α ha (U.erase x).card
        rw [cv] at ll
        have rr : ((onEdges a b U).card:ℚ) ≤ ((onEdges a b (U.erase x)).card:ℚ)+1 := by
          exact_mod_cast (show (onEdges a b U).card ≤ (onEdges a b (U.erase x)).card + 1 by omega)
        linarith
    · unfold conn at hconn
      push Not at hconn
      obtain ⟨A,B,hA,hB,disj,hu,he⟩ := hconn
      have vct : U.card = A.card+B.card := by rw [hu,Finset.card_union_of_disjoint disj]
      have aa : A ⊂ U := by
        apply Finset.ssubset_iff_subset_ne.mpr
        exact ⟨hu ▸ Finset.subset_union_left, fun e => by
          have := hB.card_pos
          rw [e] at vct
          omega⟩
      have bb : B ⊂ U := by
        apply Finset.ssubset_iff_subset_ne.mpr
        exact ⟨hu ▸ Finset.subset_union_right, fun e => by
          have := hA.card_pos
          rw [e] at vct
          omega⟩
      have ed : ((onEdges a b U).card:ℚ) ≤ (onEdges a b A).card + (onEdges a b B).card := by
        exact_mod_cast (he ▸ Finset.card_union_le (onEdges a b A) (onEdges a b B))
      calc
        _ ≤ target α A.card + target α B.card := by linarith [ih A aa, ih B bb]
        _ ≤ _ := vct ▸ target_join α ha A.card B.card
  · exact le_trans (by exact_mod_cast Nat.le_of_not_gt hc) (le_max_left ..)

end Reduction
end ConwayThrackle

namespace ConwayThrackle
namespace Profile

/-- Run statistics: u,v are numbers of maximal 6/8 runs, x,y the corresponding
edge counts. If both colors occur, there are j transitions in each direction
in the cyclic sequence of run colors. k is a conservative integral lower
bound for corners plus endpoint rebates minus virtual-thread expenses. -/
structure Rule where
  cap₆ : ℤ → ℤ
  cap₈ : ℤ → ℤ
  cap₁₀ : ℤ → ℤ
  g₆₆ : ℤ
  g₆₈ : ℤ
  g₈₈ : ℤ
  e₆₆ : ℤ
  e₆₈ : ℤ
  e₈₈ : ℤ
  virtualize : Bool

def adm (w : Rule) (D u v j x y k : ℤ) : Prop :=
  let g := D-x-y
  let hasGap : ℤ := if 0<g then 1 else 0
  let e := max hasGap ((u-j)*w.e₆₆+2*j*w.e₆₈+(v-j)*w.e₈₈)
  let p := max hasGap ((u-j)*(if 0<w.g₆₆ then 1 else 0)+
       2*j*(if 0<w.g₆₈ then 1 else 0)+(v-j)*(if 0<w.g₈₈ then 1 else 0))
  10 ≤ D ∧ D % 2 = 0 ∧ 0 ≤ u ∧ 0 ≤ v ∧ 0 ≤ j ∧ j ≤ u ∧ j ≤ v ∧
  (u=0 ∨ v=0 ∨ 1 ≤ j) ∧ u ≤ x ∧ v ≤ y ∧ 0 ≤ g ∧
  x ≤ (w.cap₆ D)*u ∧ y ≤ (w.cap₈ D)*v ∧
  (u-j)*w.g₆₆+2*j*w.g₆₈+(v-j)*w.g₈₈ ≤ g ∧
  u+v-g/3 ≤ k ∧
  (if w.virtualize then
      (if D=10 then u+v+e ≤ k ∧ g ≤ 3*(k-u-v)
       else u+v+e-(g-p)/3 ≤ k ∧ (w.cap₁₀ D ≤ 6 → u+v ≤ k))
   else u+v+e ≤ k)

def oneTheta : Rule where
  cap₆ := fun D => if D = 10 then 2 else if D = 12 then 4 else 6
  cap₈ := fun D => if D = 10 then 4 else if D = 12 then 5 else 8
  cap₁₀ := fun D => if D = 10 then 6 else if D = 12 then 8 else 10
  g₆₆ := 2
  g₆₈ := 0
  g₈₈ := 0
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 0
  virtualize := false

/-- Scaled donor budget for δ=396/49, h=6/49. -/
theorem oneTheta_budget (D u v j x y k : ℤ) (hw : adm oneTheta D u v j x y k) :
    396 ≤ 49*D + 6*(k + u + v - 6) - 23*x - 5*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 17 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 := by omega
    rcases casesD with rfl | rfl | rfl | rfl <;> norm_num [oneTheta] at hc₆ hc₈ hm he ⊢ <;> first | omega | (simp only [max_def] at he; split_ifs at he <;> omega)

def tierA : Rule where
  cap₆ := fun D => if D = 10 then 1 else if D = 12 then 3 else if D = 14 then 5 else 6
  cap₈ := fun D => if D = 10 then 3 else if D = 12 then 5 else if D = 14 then 7 else 8
  cap₁₀ := fun D => if D = 10 then 5 else if D = 12 then 7 else if D = 14 then 9 else 10
  g₆₆ := 3
  g₆₈ := 1
  g₈₈ := 0
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 0
  virtualize := false

/-- Scaled donor budget for δ=42/5, h=1/5. -/
theorem tierA_budget (D u v j x y k : ℤ) (hw : adm tierA D u v j x y k) :
    42 ≤ 5*D + 1*(k + u + v - 6) - 3*x - 1*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 24 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierA] at hc₆ hc₈ hm he ⊢ <;> omega

def tierB : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 2 else if D = 14 then 4 else 6
  cap₈ := fun D => if D = 10 then 2 else if D = 12 then 4 else if D = 14 then 6 else 8
  cap₁₀ := fun D => if D = 10 then 4 else if D = 12 then 6 else if D = 14 then 8 else 10
  g₆₆ := 4
  g₆₈ := 2
  g₈₈ := 0
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := false

/-- Scaled donor budget for δ=9, h=1/6. -/
theorem tierB_budget (D u v j x y k : ℤ) (hw : adm tierB D u v j x y k) :
    108 ≤ 12*D + 2*(k + u + v - 6) - 8*x - 3*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 30 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierB] at hc₆ hc₈ hm he ⊢ <;> omega

def tierC1 : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 2 else if D = 14 then 4 else 6
  cap₈ := fun D => if D = 10 then 1 else if D = 12 then 4 else if D = 14 then 5 else 8
  cap₁₀ := fun D => if D = 10 then 4 else if D = 12 then 6 else if D = 14 then 7 else 10
  g₆₆ := 4
  g₆₈ := 2
  g₈₈ := 0
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := false

/-- Scaled donor budget for δ=688/73, h=16/219. -/
theorem tierC1_budget (D u v j x y k : ℤ) (hw : adm tierC1 D u v j x y k) :
    2064 ≤ 219*D + 16*(k + u + v - 6) - 141*x - 51*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 28 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierC1] at hc₆ hc₈ hm he ⊢ <;> omega

def tierC3 : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 1 else if D = 14 then 3 else 6
  cap₈ := fun D => if D = 10 then 1 else if D = 12 then 4 else if D = 14 then 5 else 8
  cap₁₀ := fun D => if D = 10 then 4 else if D = 12 then 6 else if D = 14 then 7 else 10
  g₆₆ := 4
  g₆₈ := 2
  g₈₈ := 1
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := false

/-- Scaled donor budget for δ=19/2, h=1/12. -/
theorem tierC3_budget (D u v j x y k : ℤ) (hw : adm tierC3 D u v j x y k) :
    114 ≤ 12*D + 1*(k + u + v - 6) - 8*x - 3*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 30 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierC3] at hc₆ hc₈ hm he ⊢ <;> omega

def tierC4 : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 1 else if D = 14 then 3 else 6
  cap₈ := fun D => if D = 10 then 1 else if D = 12 then 4 else if D = 14 then 5 else 8
  cap₁₀ := fun D => if D = 10 then 3 else if D = 12 then 5 else if D = 14 then 7 else 10
  g₆₆ := 4
  g₆₈ := 2
  g₈₈ := 1
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := true

/-- Scaled donor budget for δ=124/13, h=2/13. -/
theorem tierC4_budget (D u v j x y k : ℤ) (hw : adm tierC4 D u v j x y k) (ends : D=14 → u=2 → v=0 → x=6 → 4≤k) :
    372 ≤ 39*D + 6*(k + u + v - 6) - 29*x - 12*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 41 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 ∨ D = 30 ∨ D = 32 ∨ D = 34 ∨ D = 36 ∨ D = 38 ∨ D = 40 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierC4] at hc₆ hc₈ hm he ⊢ <;> first | omega | (simp only [max_def] at he; split_ifs at he <;> omega)

def tierC5 : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 1 else if D = 14 then 3 else 6
  cap₈ := fun D => if D = 10 then 1 else if D = 12 then 4 else if D = 14 then 5 else 8
  cap₁₀ := fun D => if D = 10 then 3 else if D = 12 then 5 else if D = 14 then 7 else 10
  g₆₆ := 5
  g₆₈ := 2
  g₈₈ := 1
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := true

/-- Scaled donor budget for δ=124/13, h=2/13. -/
theorem tierC5_budget (D u v j x y k : ℤ) (hw : adm tierC5 D u v j x y k) :
    372 ≤ 39*D + 6*(k + u + v - 6) - 29*x - 12*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 41 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 ∨ D = 30 ∨ D = 32 ∨ D = 34 ∨ D = 36 ∨ D = 38 ∨ D = 40 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierC5] at hc₆ hc₈ hm he ⊢ <;> first | omega | (simp only [max_def] at he; split_ifs at he <;> omega)

def tierD : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 1 else if D = 14 then 3 else if D = 16 then 5 else 6
  cap₈ := fun D => if D = 10 then 1 else if D = 12 then 3 else if D = 14 then 5 else if D = 16 then 7 else 8
  cap₁₀ := fun D => if D = 10 then 3 else if D = 12 then 5 else if D = 14 then 7 else if D = 16 then 9 else 10
  g₆₆ := 5
  g₆₈ := 3
  g₈₈ := 1
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := true

/-- Scaled donor budget for δ=124/13, h=2/13. -/
theorem tierD_budget (D u v j x y k : ℤ) (hw : adm tierD D u v j x y k) :
    372 ≤ 39*D + 6*(k + u + v - 6) - 29*x - 12*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 41 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 ∨ D = 30 ∨ D = 32 ∨ D = 34 ∨ D = 36 ∨ D = 38 ∨ D = 40 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierD] at hc₆ hc₈ hm he ⊢ <;> omega

def tierE1 : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 1 else if D = 14 then 3 else if D = 16 then 5 else 6
  cap₈ := fun D => if D = 10 then 0 else if D = 12 then 3 else if D = 14 then 5 else if D = 16 then 6 else 8
  cap₁₀ := fun D => if D = 10 then 3 else if D = 12 then 5 else if D = 14 then 7 else if D = 16 then 8 else 10
  g₆₆ := 5
  g₆₈ := 3
  g₈₈ := 1
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := false

/-- Scaled donor budget for δ=168/17, h=0. -/
theorem tierE1_budget (D u v j x y k : ℤ) (hw : adm tierE1 D u v j x y k) :
    168 ≤ 17*D + 0*(k + u + v - 6) - 11*x - 4*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 28 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierE1] at hc₆ hc₈ hm he ⊢ <;> omega

def tierE2 : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 1 else if D = 14 then 3 else if D = 16 then 5 else 6
  cap₈ := fun D => if D = 10 then 0 else if D = 12 then 2 else if D = 14 then 4 else if D = 16 then 6 else 8
  cap₁₀ := fun D => if D = 10 then 3 else if D = 12 then 5 else if D = 14 then 7 else if D = 16 then 8 else 10
  g₆₆ := 5
  g₆₈ := 3
  g₈₈ := 1
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := false

/-- Scaled donor budget for δ=10, h=0. -/
theorem tierE2_budget (D u v j x y k : ℤ) (hw : adm tierE2 D u v j x y k) :
    120 ≤ 12*D + 0*(k + u + v - 6) - 8*x - 3*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 30 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierE2] at hc₆ hc₈ hm he ⊢ <;> omega

def tierE2b : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 1 else if D = 14 then 3 else if D = 16 then 5 else 6
  cap₈ := fun D => if D = 10 then 0 else if D = 12 then 3 else if D = 14 then 5 else if D = 16 then 6 else 8
  cap₁₀ := fun D => if D = 10 then 3 else if D = 12 then 5 else if D = 14 then 7 else if D = 16 then 8 else 10
  g₆₆ := 5
  g₆₈ := 3
  g₈₈ := 2
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := false

/-- Scaled donor budget for δ=10, h=0. -/
theorem tierE2b_budget (D u v j x y k : ℤ) (hw : adm tierE2b D u v j x y k) :
    120 ≤ 12*D + 0*(k + u + v - 6) - 8*x - 3*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 30 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierE2b] at hc₆ hc₈ hm he ⊢ <;> omega

def tierF : Rule where
  cap₆ := fun D => if D = 10 then 0 else if D = 12 then 0 else if D = 14 then 2 else if D = 16 then 4 else 6
  cap₈ := fun D => if D = 10 then 0 else if D = 12 then 2 else if D = 14 then 4 else if D = 16 then 6 else 8
  cap₁₀ := fun D => if D = 10 then 2 else if D = 12 then 4 else if D = 14 then 6 else if D = 16 then 8 else 10
  g₆₆ := 6
  g₆₈ := 4
  g₈₈ := 2
  e₆₆ := 1
  e₆₈ := 1
  e₈₈ := 1
  virtualize := false

/-- Scaled donor budget for δ=10, h=0. -/
theorem tierF_budget (D u v j x y k : ℤ) (hw : adm tierF D u v j x y k) :
    120 ≤ 12*D + 0*(k + u + v - 6) - 8*x - 3*y := by
  rcases hw with ⟨hd, hp, hu, hv, hj, hj₁, hj₂, hj₃, hx, hy, hg, hc₆, hc₈, hm, hk, he⟩
  by_cases tail : 30 ≤ D
  · omega
  · have casesD : D = 10 ∨ D = 12 ∨ D = 14 ∨ D = 16 ∨ D = 18 ∨ D = 20 ∨ D = 22 ∨ D = 24 ∨ D = 26 ∨ D = 28 := by omega
    rcases casesD with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [tierF] at hc₆ hc₈ hm he ⊢ <;> omega

end Profile
end ConwayThrackle
namespace ConwayThrackle
namespace ThreadA
open Finset
open scoped BigOperators

/-- A local topological rank test is witnessed by actual vertices and edges
of the input graph; it is independent of the numerical exclusion cutoff. -/
structure RankTest {V E : Type*} [DecidableEq V] [Fintype E] (a b : E → V) (budget : ℤ) where
  vertices : Finset V
  edges : Finset E
  support : edges ⊆ onEdges a b vertices
  excess : vertices.card < edges.card
  cost : (edges.card : ℤ) ≤ budget

theorem rank_lb {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    {a b : E → V} (ns : NoSmallBicyclic a b 13) {z : ℤ} (test : RankTest a b z) :
    15 ≤ z := by
  have := test.cost
  have := bicycle_capacity a b ns test.vertices test.edges test.support test.excess
  omega

def short (s : ℤ) : Prop := s=6 ∨ s=8
instance (s : ℤ) : Decidable (short s) := inferInstanceAs (Decidable (s=6 ∨ s=8))
def tag (s c r : ℤ) : ℤ := if s=c then r else 0

def cash (s r : ℤ) := 3*tag s 6 r + tag s 8 r - tag s 6 1 - tag s 8 1

variable {I : Type*} [Fintype I] [DecidableEq I]
def bucket (owner : I → Option I) (w : I → ℤ) (j : I) : ℤ :=
  ∑ i, if owner i = some j then w i else 0

theorem bucket_nonneg (owner : I → Option I) (w : I → ℤ) (h : ∀ i, 0 ≤ w i) (j : I) :
    0 ≤ bucket owner w j := by
  unfold bucket
  apply Finset.sum_nonneg
  intro i _
  split <;> simp [h]

theorem bucket_room (owner : I → Option I) (w s : I → ℤ) (h : ∀ i, 0 ≤ w i)
    (only : ∀ i j, owner i = some j → ¬short (s i)) :
    (∑ j, bucket owner w j) ≤ ∑ i, (w i - tag (s i) 6 (w i) - tag (s i) 8 (w i)) := by
  unfold bucket
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  cases hh : owner i with
  | none => simp; grind [tag]
  | some j =>
    have := only i j hh
    simp
    grind [short,tag]

theorem bucket_count_pos (owner : I → Option I) (w : I → ℤ) (j : I)
    (h : 0 < bucket owner w j) : 1 ≤ bucket owner (fun _ => 1) j := by
  by_cases he : ∃ i, owner i = some j
  · obtain ⟨i, hi⟩ := he
    unfold bucket
    exact le_trans (show 1 ≤ (if owner i = some j then (1:ℤ) else 0) by simp [hi])
      (Finset.single_le_sum (f := fun t => if owner t = some j then (1:ℤ) else 0)
        (by intro t _; split <;> decide) (Finset.mem_univ i))
  · push Not at he
    simp [bucket,he] at h

/-- Two estimates for an oriented gap, including a return to a previously
encountered recipient. They sum independently of the order of run colors. -/
theorem gap_credit (s t g : ℤ) (hg : 0 ≤ g) (hm : short s ↔ short t)
    (hb : short s → 15 ≤ s+t+g) :
    tag s 6 1 + tag t 6 1 ≤ g ∧
    (3*tag s 6 1-tag s 8 1)+(3*tag t 6 1-tag t 8 1) ≤ 2*g := by
  grind [short,tag]

/-- Small-face and large-face arithmetic with independently folded gap bounds. -/
theorem budget (D u v x y k : ℤ) (hd : 6 ≤ D) (par : D%2=0)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hx : u ≤ x) (hy : v ≤ y)
    (cover : x+y ≤ D) (small : u+v ≤ k)
    (cx : x ≤ min 6 (D-9)*u) (cy : y ≤ min 8 (D-7)*v)
    (abs₆ : D-9<1 → u=0) (abs₈ : D-7<1 → v=0)
    (gp : 10 ≤ D → 2*u ≤ D-x-y ∧ 3*u-v ≤ D-x-y ∧ 2*u+v ≤ k)
    (extra : x+y < D → u+v+1 ≤ k) :
    42 ≤ 5*D + k-6 + (if D=6 then 3*D-k else if D=8 then D-k else 0)
      - (3*x+y-u-v) := by
  by_cases tail : 24 ≤ D
  · simp [show D≠6 by omega,show D≠8 by omega]
    omega
  · have splitD : D=6 ∨ D=8 ∨ D=10 ∨ D=12 ∨ D=14 ∨ D=16 ∨ D=18 ∨ D=20 ∨ D=22 := by omega
    rcases splitD with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num at cx cy gp abs₆ abs₈ ⊢ <;> omega

/-- A normalized facial incidence record. Each element of I is one boundary
thread between branch corners. The cyclic successor of marked threads preserves
the marked set and is extended by the identity on unmarked threads. Unmarked
threads in each gap have a unique owner. Rank tests are independent geometric
subgraph certificates: contact = union of face supports, gap = recipients joined
by the gap. They are not numerical discharging conditions. -/
structure Local {V E : Type*} [DecidableEq V] [Fintype E] (a b : E → V)
    (D : ℤ) (s r : I → ℤ) where
  degree : 6 ≤ D
  parity : D%2 = 0
  boundary : ∑ i, r i = D
  positive : ∀ i, 1 ≤ r i
  fits : ∀ i, r i ≤ s i
  rankContact : ∀ i, short (s i) → RankTest a b (D+s i-r i)
  nxt : I ≃ I
  marked : ∀ i, short (s i) ↔ short (s (nxt i))
  owner : I → Option I
  uncovered : ∀ i j, owner i = some j → ¬short (s i)
  rankGap : ∀ i, 10 ≤ D → short (s i) → RankTest a b (s i+s (nxt i)+bucket owner r i)

set_option maxHeartbeats 1800000 in
theorem face_budget {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    {a b : E → V} (ns : NoSmallBicyclic a b 13) {D : ℤ} {s r : I → ℤ}
    (w : Local a b D s r) :
    42 ≤ 5*D+Fintype.card I-6 + (∑ i, cash D (r i)) - ∑ i, cash (s i) (r i) := by
  classical
  let u := ∑ i, tag (s i) 6 1
  let v := ∑ i, tag (s i) 8 1
  let x := ∑ i, tag (s i) 6 (r i)
  let y := ∑ i, tag (s i) 8 (r i)
  have nn (c : ℤ) : 0 ≤ ∑ i, tag (s i) c 1 := Finset.sum_nonneg (by
    intro i _; unfold tag; split <;> decide)
  have covers (c : ℤ) : (∑ i, tag (s i) c 1) ≤ ∑ i, tag (s i) c (r i) :=
    Finset.sum_le_sum (by intro i _; have := w.positive i; grind [tag])
  have counts (f : I → ℤ) (hh : ∀ i, 0 ≤ f i) :
      (∑ i, tag (s i) 6 (f i)) + ∑ i, tag (s i) 8 (f i) ≤ ∑ i, f i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (by intro i _; have := hh i; grind [tag])
  have pos i : 0 ≤ r i := le_trans (by decide) (w.positive i)
  have cg := counts r pos
  rw [w.boundary] at cg
  have cs := counts (fun _ => 1) (by intro; decide)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at cs
  have ex (c : ℤ) (hc : short c) (i : I) (hi : s i=c) :
      r i ≤ min c (D+c-15) := by
    have h := rank_lb ns (w.rankContact i (hi ▸ hc))
    have f := w.fits i
    omega
  have caps (c : ℤ) (hc : short c) :
      (∑ i, tag (s i) c (r i)) ≤ min c (D+c-15) * ∑ i, tag (s i) c 1 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : s i=c
    · simpa [tag,h] using ex c hc i h
    · simp [tag,h]
  have none (c : ℤ) (hc : short c) (tiny : D+c-15<1) :
      (∑ i, tag (s i) c 1)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    by_cases h : s i=c
    · have := ex c hc i h; have := w.positive i; omega
    · simp [tag,h]
  have gapstats (large : 10 ≤ D) : 2*u ≤ D-x-y ∧ 3*u-v ≤ D-x-y ∧
      2*u+v ≤ Fintype.card I := by
    let g := bucket w.owner r
    let n := w.nxt
    have cr (i : I) := gap_credit (s i) (s (n i)) (g i)
      (bucket_nonneg w.owner r pos i) (w.marked i) (fun hh => rank_lb ns (w.rankGap i large hh))
    have e₁ := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => (cr i).1)
    have e₂ := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => (cr i).2)
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum] at e₁ e₂
    have tr (c : ℤ) : (∑ i, tag (s (n i)) c 1) = ∑ i, tag (s i) c 1 :=
      n.sum_comp (fun i => tag (s i) c 1)
    rw [tr] at e₁
    rw [tr,tr] at e₂
    have br := bucket_room w.owner r s pos w.uncovered
    simp only [Finset.sum_sub_distrib,w.boundary] at br
    have br' := bucket_room w.owner (fun _ => 1) s (by intro; decide) w.uncovered
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at br'
    have en := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (f:=fun i=>tag (s i) 6 1)
      (g:=fun i=>bucket w.owner (fun _=>1) i) (fun i _ => by
        by_cases hi : s i=6
        · have gc := (cr i).1
          have tt : 0 ≤ tag (s (n i)) 6 1 := by unfold tag; split <;> decide
          have aa : tag (s i) 6 1 = 1 := by simp [tag,hi]
          rw [aa] at gc
          have pg : 0 < g i := lt_of_lt_of_le (show 0 < 1+tag (s (n i)) 6 1 by omega) gc
          simpa [tag,hi] using bucket_count_pos w.owner r i pg
        · simpa [tag,hi] using bucket_nonneg w.owner (fun _ => 1) (by intro; decide) i)
    dsimp [u,v,x,y,g] at *
    omega
  have left (lt : x+y<D) : u+v+1 ≤ Fintype.card I := by
    by_contra! bad
    have ez : (∑ i, (1-tag (s i) 6 1-tag (s i) 8 1)) = 0 := by
      simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      dsimp [u,v] at bad; omega
    have ez' := (Finset.sum_eq_zero_iff_of_nonneg (f:=fun i=>1-tag (s i) 6 1-tag (s i) 8 1)
      (by intro i _; grind [tag])).mp ez
    have all := Finset.sum_eq_zero (s:=(Finset.univ : Finset I))
      (f:=fun i=>r i-tag (s i) 6 (r i)-tag (s i) 8 (r i)) (by
        intro i hi; have := ez' i hi; grind [tag])
    simp only [Finset.sum_sub_distrib,w.boundary] at all
    dsimp [x,y] at lt; omega
  have cx := caps 6 (by decide)
  have cy := caps 8 (by decide)
  have abs₆ := none 6 (by decide)
  have abs₈ := none 8 (by decide)
  have bgt := budget D u v x y (Fintype.card I) w.degree w.parity (nn 6) (nn 8)
    (covers 6) (covers 8) cg cs (by simpa [u,x,show D+6-15=D-9 by omega] using cx)
      (by simpa [v,y,show D+8-15=D-7 by omega] using cy) (fun _ => abs₆ (by omega))
      (fun _ => abs₈ (by omega)) gapstats left
  have inc : (∑ i,cash D (r i)) =
      if D=6 then 3*D-Fintype.card I else if D=8 then D-Fintype.card I else 0 := by
    by_cases h : D=6 <;> by_cases h' : D=8 <;>
      simp [cash,tag,h,h',Finset.sum_sub_distrib,← Finset.mul_sum, w.boundary]
  rw [inc]
  simpa only [cash,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,u,v,x,y] using bgt

end ThreadA
end ConwayThrackle
namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

/-- Sharp N=13 core bound for a rank-certified cellular thread presentation.
The four counting equations are ordinary weighted sides, unweighted sides,
suppression of bivalent vertices, and Euler. The degree inequality is the
branch handshake. No local budget or density is an input. -/
theorem sharp_core {V E F : Type*} [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype F]
    {a b : E → V} (ns : NoSmallBicyclic a b 13)
    (I : F → Type*) [∀ y, Fintype (I y)] [∀ y, DecidableEq (I y)]
    (D : F → ℤ) (r : Sigma I → ℤ) (opp : Sigma I ≃ Sigma I)
    (paired : ∀ t, r (opp t) = r t)
    (localData : ∀ y, Local a b (D y) (fun i : I y => D (opp ⟨y,i⟩).1) (fun i => r ⟨y,i⟩))
    (n m e v χ : ℤ) (sides : ∑ y, D y = 2*m)
    (threads : ∑ y, (Fintype.card (I y) : ℤ) = 2*e)
    (handshake : 3*v ≤ 2*e)
    (subdiv : n = v+(m-e)) (euler : n-m+Fintype.card F=χ) :
    16*m ≤ 21*n-24*χ := by
  classical
  let weight (t : Sigma I) := cash (D t.1) (r t)
  have bal := opp.sum_comp weight
  rw [Fintype.sum_sigma, Fintype.sum_sigma] at bal
  simp only [weight,paired] at bal
  have eqn := Finset.sum_le_sum (s := (Finset.univ : Finset F)) (fun y _ =>
    face_budget ns (localData y))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,sides,threads] at eqn
  omega

end ConwayThrackle.ThreadA
namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

/-- Cellular data on an induced connected noncycle core U. The parameters
m,n in the incidence identities are the graph's actual edge and vertex counts.
RankTest values contain actual subgraphs, not assertions of a degree cap. -/
structure Presentation {V E : Type*} [DecidableEq V] [Fintype E]
    (a b : E → V) (U : Finset V) where
  Face : Type
  [faceFinite : Fintype Face]
  Sectors : Face → Type
  [cornerFinite : ∀ y, Fintype (Sectors y)]
  [cornerDec : ∀ y, DecidableEq (Sectors y)]
  d : Face → ℤ
  span : Sigma Sectors → ℤ
  mate : Sigma Sectors ≃ Sigma Sectors
  paired : ∀ t, span (mate t) = span t
  incidences : ∀ y, Local a b (d y) (fun i : Sectors y => d (mate ⟨y,i⟩).1) (fun i => span ⟨y,i⟩)
  e : ℕ
  v : ℕ
  χ : ℤ
  chi_pos : 1 ≤ χ
  sides : ∑ y, d y = 2 * ((onEdges a b U).card : ℤ)
  threads : ∑ y, (Fintype.card (Sectors y) : ℤ) = 2*(e:ℤ)
  handshake : 3*(v:ℤ) ≤ 2*(e:ℤ)
  subdiv : (U.card:ℤ) = v+(((onEdges a b U).card:ℤ)-e)
  euler : (U.card:ℤ)-(onEdges a b U).card+Fintype.card Face=χ

/-- All-graph sharp N=13 bound conditional on the finite exclusion and the
local rank-certified embeddings of the connected min-degree-two cores. -/
theorem bound_of_NSB13 {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (a b : E → V) (ns : NoSmallBicyclic a b 13)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card → Nonempty (Presentation a b U))
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (21/16) U.card := by
  apply forest_reduction a b (21/16) (by norm_num) _ U
  intro W hc hm hr
  obtain ⟨p⟩ := emb W hc hm hr
  let : Fintype p.Face := p.faceFinite
  let : ∀ y, Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y, DecidableEq (p.Sectors y) := p.cornerDec
  have bd := sharp_core ns p.Sectors p.d p.span p.mate p.paired p.incidences
    W.card (onEdges a b W).card p.e p.v p.χ p.sides p.threads p.handshake p.subdiv p.euler
  have hc' := p.chi_pos
  have z : 16*((onEdges a b W).card:ℤ) ≤ 21*(W.card:ℤ)-21 := by omega
  have q : 16*((onEdges a b W).card:ℚ) ≤ 21*(W.card:ℚ)-21 := by exact_mod_cast z
  linarith

end ConwayThrackle.ThreadA
namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

def rate16 (s r : ℤ) : ℤ := 8*tag s 6 r + 3*tag s 8 r

theorem budget16 (D u v x y : ℤ) (mind : 6 ≤ D) (even : D%2=0)
    (u₀ : 0 ≤ u) (v₀ : 0 ≤ v) (x₀ : u ≤ x) (y₀ : v ≤ y) (covered : x+y ≤ D)
    (cap₆ : x ≤ min 6 (D-12)*u) (cap₈ : y ≤ min 8 (D-10)*v)
    (gap : 10 ≤ D → 6*u+2*v ≤ D-x-y) :
    120 ≤ 12*D + (if D=6 then 8*D else if D=8 then 3*D else 0) - (8*x+3*y) := by
  by_cases tail : 30 ≤ D
  · simp [show D≠6 by omega,show D≠8 by omega]; omega
  · have d : D=6 ∨ D=8 ∨ D=10 ∨ D=12 ∨ D=14 ∨ D=16 ∨ D=18 ∨ D=20 ∨ D=22 ∨
        D=24 ∨ D=26 ∨ D=28 := by omega
    rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num at cap₆ cap₈ gap ⊢ <;> omega

set_option maxHeartbeats 900000 in
theorem face_budget16 {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    [Fintype E] [DecidableEq E] {a b : E → V} (ns : NoSmallBicyclic a b 16)
    {D : ℤ} {s r : I → ℤ} (w : Local a b D s r) :
    120 ≤ 12*D + (∑ i,rate16 D (r i)) - ∑ i,rate16 (s i) (r i) := by
  have rk {z : ℤ} (rr : RankTest a b z) : 18 ≤ z := by
    have := bicycle_capacity a b ns rr.vertices rr.edges rr.support rr.excess
    have := rr.cost
    omega
  let cnt (c:ℤ) := ∑ i, tag (s i) c 1
  let wt (c:ℤ) := ∑ i, tag (s i) c (r i)
  have pos i : 0≤r i := le_trans (by decide) (w.positive i)
  have nn (c:ℤ) : 0≤cnt c := Finset.sum_nonneg (by intro i _; unfold tag; split <;> decide)
  have lo (c:ℤ) : cnt c ≤ wt c := Finset.sum_le_sum (by
    intro i _; have := w.positive i; grind only [tag])
  have cov : wt 6 + wt 8 ≤ D := by
    rw [← w.boundary]; dsimp [wt]; rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (by intro i _; have := pos i; grind only [tag])
  have cap (c:ℤ) (hc : short c) : wt c ≤ min c (D+c-18)*cnt c := by
    dsimp [wt,cnt]; rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : s i=c
    · have z := rk (w.rankContact i (h ▸ hc))
      have := w.fits i
      simp [tag,h]; omega
    · simp [tag,h]
  have gp (large : 10≤D) : 6*cnt 6+2*cnt 8 ≤ D-wt 6-wt 8 := by
    let t i := 3*tag (s i) 6 1+tag (s i) 8 1
    let g := bucket w.owner r
    have eqn := Finset.sum_le_sum (s := (Finset.univ : Finset I))
      (f:=fun i=> t i+t (w.nxt i)) (g:=g) (fun i _ => by
        have h0 := bucket_nonneg w.owner r pos i
        have hm := w.marked i
        have hb (h : short (s i)) := rk (w.rankGap i large h)
        dsimp [t,g]
        grind only [short,tag])
    rw [Finset.sum_add_distrib,w.nxt.sum_comp t] at eqn
    have e := bucket_room w.owner r s pos w.uncovered
    simp only [Finset.sum_sub_distrib,w.boundary] at e
    simp only [t,Finset.sum_add_distrib,← Finset.mul_sum,g] at eqn
    dsimp [cnt,wt]; omega
  have hb := budget16 D (cnt 6) (cnt 8) (wt 6) (wt 8) w.degree w.parity
    (nn 6) (nn 8) (lo 6) (lo 8) cov
    (by simpa [show D+6-18=D-12 by omega] using cap 6 (by decide))
    (by simpa [show D+8-18=D-10 by omega] using cap 8 (by decide)) gp
  have inc : (∑ i,rate16 D (r i)) = if D=6 then 8*D else if D=8 then 3*D else 0 := by
    by_cases h : D=6 <;> by_cases h' : D=8 <;>
      simp [rate16,tag,h,h',← Finset.mul_sum,w.boundary]
  rw [inc]
  simpa only [rate16,Finset.sum_add_distrib,← Finset.mul_sum,wt] using hb

theorem core16 {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E] {a b : E → V}
    (ns : NoSmallBicyclic a b 16) (U : Finset V) (p : Presentation a b U) :
    4*((onEdges a b U).card:ℤ) ≤ 5*(U.card:ℤ)-5*p.χ := by
  classical
  let : Fintype p.Face := p.faceFinite
  let : ∀ y, Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y, DecidableEq (p.Sectors y) := p.cornerDec
  let z (t : Sigma p.Sectors) := rate16 (p.d t.1) (p.span t)
  have bal := p.mate.sum_comp z
  rw [Fintype.sum_sigma,Fintype.sum_sigma] at bal
  simp only [z,p.paired] at bal
  have eqn := Finset.sum_le_sum (s := (Finset.univ : Finset p.Face))
    (fun y _ => face_budget16 ns (p.incidences y))
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,p.sides] at eqn
  have := p.euler
  omega

theorem bound_of_NSB16 {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (a b : E → V) (ns : NoSmallBicyclic a b 16)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card → Nonempty (Presentation a b U))
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (5/4) U.card := by
  apply forest_reduction a b (5/4) (by norm_num) _ U
  intro W hc hm hr
  obtain ⟨p⟩ := emb W hc hm hr
  have := core16 ns W p
  have := p.chi_pos
  have z : 4*((onEdges a b W).card:ℤ) ≤ 5*(W.card:ℤ)-5 := by omega
  have q : 4*((onEdges a b W).card:ℚ) ≤ 5*(W.card:ℚ)-5 := by exact_mod_cast z
  linarith

end ConwayThrackle.ThreadA
namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

/-- Unoriented incidence of an edge with a specified pair of endpoints. -/
def joins {V E : Type*} (a b : E → V) (e : E) (x y : V) : Prop :=
  (a e=x ∧ b e=y) ∨ (a e=y ∧ b e=x)

structure Strand {V E : Type*} (a b : E → V) (n : ℕ) (x y : V) where
  pt : Fin (n+1) ↪ V
  ed : Fin n ↪ E
  first : pt 0=x
  last : pt (Fin.last n)=y
  side : ∀ i, joins a b (ed i) (pt i.castSucc) (pt i.succ)

/-- Three internally vertex-disjoint, edge-disjoint paths with the same
distinct ends. Multiplicities in the unordered length triple are preserved. -/
def hasTheta {V E : Type*} (a b : E → V) (lengths : Multiset ℕ) : Prop :=
  ∃ (x y : V) (L : Fin 3 → ℕ) (P : ∀ i, Strand a b (L i) x y),
  x≠y ∧ (↑([L 0,L 1,L 2] : List ℕ) : Multiset ℕ)=lengths ∧
  ∀ i j, i≠j → (∀ u v, (P i).ed u ≠ (P j).ed v) ∧
    (∀ u v, (P i).pt u = (P j).pt v → (P i).pt u=x ∨ (P i).pt u=y)

def legs (x y z : ℤ) : Multiset ℕ := ([x.toNat,y.toNat,z.toNat] : List ℕ)

structure OctCircuit {V E : Type*} (a b : E → V) where
  pt : Fin 8 ↪ V
  ed : Fin 8 ↪ E
  side : ∀ i, joins a b (ed i) (pt i) (pt (i+1))

def hasOctWedge {V E : Type*} (a b : E → V) : Prop :=
  ∃ (p q : OctCircuit a b) (i j : Fin 8), p.pt i=q.pt j ∧
  (∀ k l, p.pt k=q.pt l → k=i ∧ l=j) ∧ (∀ k l, p.ed k≠q.ed l)

structure EExclusions {V E : Type*} (a b : E → V) : Prop where
  th179 : ¬hasTheta a b (legs 1 7 9)
  th359 : ¬hasTheta a b (legs 3 5 9)
structure CExclusions {V E : Type*} (a b : E → V) : Prop where
  db880 : ¬hasOctWedge a b
  th2410 : ¬hasTheta a b (legs 2 4 10)
  th268 : ¬hasTheta a b (legs 2 6 8)
  th466 : ¬hasTheta a b (legs 4 6 6)

section
variable {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype E]
variable {a b : E → V} {D : ℤ} {s r : I → ℤ}

/-- A threshold contact on simple small facial cycles either costs at least
one fewer edge than the naive bicyclic support, or supplies the exact theta
as an actual subgraph. No forbidden-pattern or discharging bound is assumed. -/
structure Detail (w : Local a b D s r) where
  ten : ∀ i, s i=10 → RankTest a b (D+s i-r i)
  path : ∀ i, D ≤ 14 → s i ≤ 10 → r i < D → r i < s i →
    Nonempty (RankTest a b (D+s i-r i-1)) ∨ hasTheta a b (legs (r i) (s i-r i) (D-r i))
  wedge : ∀ i, s i=8 → s (w.nxt i)=8 → bucket w.owner r i=0 →
    Nonempty (RankTest a b 15) ∨ hasOctWedge a b

def hasDetails {U : Finset V} (p : Presentation a b U) : Prop :=
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y,DecidableEq (p.Sectors y) := p.cornerDec
  ∀ y, Nonempty (Detail (p.incidences y))

theorem rank_limit {N : ℕ} (ns : NoSmallBicyclic a b N) {z : ℤ} (t : RankTest a b z) :
    (N:ℤ)+2 ≤ z := by
  classical
  have := bicycle_capacity a b ns t.vertices t.edges t.support t.excess
  have := t.cost
  omega

def countOf (s : I → ℤ) (k : ℤ) : ℤ := ∑ i, tag (s i) k 1
def weightOf (s r : I → ℤ) (k : ℤ) : ℤ := ∑ i, tag (s i) k (r i)
def markedUnit (s : ℤ) : ℤ := if short s then 1 else 0

omit [DecidableEq I] in
theorem sum_marked : (∑ i, markedUnit (s i))=countOf s 6+countOf s 8 := by
  unfold countOf; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; grind only [markedUnit, short,tag]

omit [DecidableEq I] in
theorem count_nonneg (k:ℤ) : 0≤countOf s k := Finset.sum_nonneg (by
  intro i _; unfold tag; split <;> decide)
theorem cover_low (w : Local a b D s r) (k:ℤ) : countOf s k≤weightOf s r k :=
  Finset.sum_le_sum (by intro i _; have := w.positive i; grind only [tag])
theorem cover_total (w : Local a b D s r) : weightOf s r 6+weightOf s r 8 ≤ D := by
  rw [← w.boundary]; unfold weightOf; rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (by intro i _; have := w.positive i; grind only [tag])
theorem count_total (_w : Local a b D s r) : countOf s 6+countOf s 8 ≤ Fintype.card I := by
  unfold countOf; rw [← Finset.sum_add_distrib]
  exact le_trans (Finset.sum_le_sum (g:=fun _=>(1:ℤ)) (by
    intro i _; grind only [tag])) (by simp)

theorem extra_corner (w : Local a b D s r) (hg : weightOf s r 6+weightOf s r 8<D) :
    countOf s 6+countOf s 8+1 ≤ Fintype.card I := by
  by_contra! bad
  have := count_total w
  have z : (∑ i, (1-tag (s i) 6 1-tag (s i) 8 1))=0 := by
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
    unfold countOf at *; omega
  have each := (Finset.sum_eq_zero_iff_of_nonneg (f:=fun i=>1-tag (s i) 6 1-tag (s i) 8 1)
    (by intro i _; grind only [tag])).mp z
  have z' := Finset.sum_eq_zero (s:=(Finset.univ : Finset I))
    (f:=fun i=>r i-tag (s i) 6 (r i)-tag (s i) 8 (r i)) (by
      intro i hi; have := each i hi; grind only [tag])
  simp only [Finset.sum_sub_distrib,w.boundary] at z'
  unfold weightOf at hg; omega

omit [DecidableEq I] in
theorem sum_cap (k cap : ℤ) (h : ∀ i, s i=k → r i≤cap) :
    weightOf s r k ≤ cap*countOf s k := by
  unfold weightOf countOf; rw [Finset.mul_sum]; apply Finset.sum_le_sum
  intro i _; by_cases e : s i=k
  · simpa [tag,e] using h i e
  · simp [tag,e]

theorem plain_cap {N : ℕ} (w : Local a b D s r) (ns : NoSmallBicyclic a b N)
    (k : ℤ) (hk : short k) (i : I) (h : s i=k) :
    r i ≤ min k (D+k-N-2) := by
  have := rank_limit ns (w.rankContact i (h ▸ hk))
  have := w.fits i; omega

theorem gap_moment (w : Local a b D s r) (c₆ c₈ z : ℤ) (hz : 0≤z)
    (pt : ∀ i, (c₆*tag (s i) 6 1+c₈*tag (s i) 8 1)+
       (c₆*tag (s (w.nxt i)) 6 1+c₈*tag (s (w.nxt i)) 8 1) ≤ z*bucket w.owner r i) :
    2*(c₆*countOf s 6+c₈*countOf s 8) ≤ z*(D-weightOf s r 6-weightOf s r 8) := by
  let f i := c₆*tag (s i) 6 1+c₈*tag (s i) 8 1
  have e := Finset.sum_le_sum (s := (Finset.univ : Finset I))
    (f:=fun i=> f i+f (w.nxt i)) (g:= fun i=>z*bucket w.owner r i) (fun i _ => pt i)
  rw [Finset.sum_add_distrib,w.nxt.sum_comp f,←Finset.mul_sum] at e
  simp only [f,Finset.sum_add_distrib,←Finset.mul_sum] at e
  have br := bucket_room w.owner r s (fun i=>le_trans (by decide) (w.positive i)) w.uncovered
  simp only [Finset.sum_sub_distrib,w.boundary] at br
  unfold countOf weightOf
  linarith only [e,mul_le_mul_of_nonneg_left br hz]

/-- Scaled global accounting for sector-based transfers, including any proved
vertex budget. The graph counts in the conclusion are those of the induced core. -/
theorem settle {U : Finset V} (p : Presentation a b U) (K S H : ℤ)
    (payment : ℤ → ℤ → ℤ) (ex : p.Face → ℤ)
    (extra : letI := p.faceFinite; (∑ y, ex y) ≤ H*(4*(p.e:ℤ)-6*(p.v:ℤ)))
    (faces : letI := p.cornerFinite; ∀ y, K≤ S*p.d y+H*((Fintype.card (p.Sectors y):ℤ)-6)+ex y+
      (∑ i:p.Sectors y,payment (p.d y) (p.span ⟨y,i⟩))-
       ∑ i:p.Sectors y,payment (p.d (p.mate ⟨y,i⟩).1) (p.span ⟨y,i⟩)) :
    (K-2*S)*((onEdges a b U).card:ℤ) ≤ K*(U.card:ℤ)-(K+6*H)*p.χ := by
  classical
  let : Fintype p.Face := p.faceFinite
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let cash' (t : Sigma p.Sectors) := payment (p.d t.1) (p.span t)
  have bal := p.mate.sum_comp cash'
  rw [Fintype.sum_sigma,Fintype.sum_sigma] at bal
  simp only [cash',p.paired] at bal
  have eqn := Finset.sum_le_sum (s := (Finset.univ : Finset p.Face)) (fun y _ => faces y)
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,p.sides,p.threads] at eqn
  have eu := p.euler
  have sd := p.subdiv
  linear_combination (norm := ring_nf) eqn + extra - (K+6*H)*eu + 6*H*sd - bal; norm_num
end
end ConwayThrackle.ThreadA

namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

theorem budgetE (D u v x y : ℤ) (mind : 6 ≤ D) (even : D%2=0)
    (u₀ : 0 ≤ u) (v₀ : 0 ≤ v) (x₀ : u ≤ x) (y₀ : v ≤ y) (covered : x+y ≤ D)
    (cap₆ : x ≤ min 6 (D-11)*u)
    (cap₈ : y ≤ (if D=10 then 0 else if D=12 then 2 else min 8 (D-9))*v)
    (gap : 10 ≤ D → 5*u+v ≤ D-x-y) :
    120 ≤ 12*D + (if D=6 then 8*D else if D=8 then 3*D else 0) - (8*x+3*y) := by
  by_cases tail : 30 ≤ D
  · simp [show D≠6 by omega,show D≠8 by omega]; omega
  · have d : D=6 ∨ D=8 ∨ D=10 ∨ D=12 ∨ D=14 ∨ D=16 ∨ D=18 ∨ D=20 ∨ D=22 ∨
        D=24 ∨ D=26 ∨ D=28 := by omega
    rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num at cap₆ cap₈ gap ⊢ <;> omega

theorem faceE {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V]
    [Fintype E] {a b : E → V} (ns : NoSmallBicyclic a b 15) (ban : EExclusions a b)
    {D : ℤ} {s r : I → ℤ} (w : Local a b D s r) (d : Detail w) :
    120 ≤ 12*D + (∑ i,rate16 D (r i)) - ∑ i,rate16 (s i) (r i) := by
  have cv₆ := sum_cap 6 (min 6 (D-11)) (s:=s) (r:=r) (fun i hi => by
    have := plain_cap w ns 6 (by decide) i hi; omega)
  have cv₈ := sum_cap 8 (if D=10 then 0 else if D=12 then 2 else min 8 (D-9))
    (s:=s) (r:=r) (fun i hi => by
      have le := plain_cap w ns 8 (by decide) i hi
      have pos := w.positive i
      split
      · rename_i e; have rr : r i=1 := by omega
        rcases d.path i (by omega) (by omega) (by omega) (by omega) with small|th
        · have  := rank_limit ns small.some; omega
        · rw [hi,e,rr] at th
          exact False.elim (ban.th179 (by convert th using 1; decide))
      · split
        · rename_i e
          by_contra! ng
          have rr : r i=3 := by omega
          rcases d.path i (by omega) (by omega) (by omega) (by omega) with small|th
          · have  := rank_limit ns small.some; omega
          · rw [hi,e,rr] at th
            exact ban.th359 (by convert th using 1; decide)
        · omega)
  have spacer (hd : 10≤D) : 5*countOf s 6 + countOf s 8 ≤ D-weightOf s r 6-weightOf s r 8 := by
    have e := gap_moment w 5 1 2 (by decide) (fun i => by
      have := bucket_nonneg w.owner r (fun j=>le_trans (by decide) (w.positive j)) i
      have hm := w.marked i
      have hb (h : short (s i)) := rank_limit ns (w.rankGap i hd h)
      norm_num at hb
      grind only [short,tag])
    omega
  have bgt := budgetE D (countOf s 6) (countOf s 8) (weightOf s r 6) (weightOf s r 8)
    w.degree w.parity (count_nonneg 6) (count_nonneg 8) (cover_low w 6) (cover_low w 8)
    (cover_total w) cv₆ cv₈ spacer
  have inc : (∑ i,rate16 D (r i)) = if D=6 then 8*D else if D=8 then 3*D else 0 := by
    by_cases h : D=6 <;> by_cases h' : D=8 <;>
      simp [rate16,tag,h,h',← Finset.mul_sum,w.boundary]
  rw [inc]
  simpa only [rate16,Finset.sum_add_distrib,← Finset.mul_sum,weightOf] using bgt

theorem bound_of_E2 {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (a b : E → V) (ns : NoSmallBicyclic a b 15) (ban : EExclusions a b)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card →
       ∃ p : Presentation a b U, hasDetails p)
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (5/4) U.card := by
  apply forest_reduction a b (5/4) (by norm_num) _ U
  intro W hc hm hr
  obtain ⟨p,hp⟩ := emb W hc hm hr
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y,DecidableEq (p.Sectors y) := p.cornerDec
  have z := settle p 120 12 0 rate16 (fun _=>0) (by simp) (fun y => by
    obtain ⟨d⟩ := hp y
    simpa using faceE ns ban (p.incidences y) d)
  have := p.chi_pos
  have q : 4*((onEdges a b W).card:ℚ) ≤ 5*(W.card:ℚ)-5 := by
    exact_mod_cast (show 4*((onEdges a b W).card:ℤ) ≤ 5*(W.card:ℤ)-5 by omega)
  linarith
end ConwayThrackle.ThreadA

namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

def flag (p : Prop) [Decidable p] : ℤ := if p then 1 else 0

/-- Branch degree is counted from actual sector occurrences, including repeated
visits on a non-simple facial boundary. -/
def valence {X Y : Type*} [Fintype X] [DecidableEq Y] (v : X→Y) (b:Y) : ℕ :=
  (univ.filter (fun i=>v i=b)).card

theorem group_by_branch {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (v : X→Y) (f : Y→ℤ) : (∑ i, f (v i))=∑ y, f y*(valence v y:ℤ) := by
  classical
  have c (y:Y) : (valence v y:ℤ) = ∑ i, if v i=y then 1 else 0 := by simp [valence]
  simp_rw [c,Finset.mul_sum]; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _; simp [mul_ite]

theorem high_capacity {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (v : X→Y) (min3 : ∀ y, 3≤valence v y) :
    (∑ i,flag (4≤valence v (v i))) ≤ 4*((Fintype.card X:ℤ)-3*Fintype.card Y) := by
  have e := group_by_branch v (fun y=>flag (4≤valence v y))
  have all := group_by_branch v (fun _=>(1:ℤ))
  simp at all
  rw [e]
  calc
    _ ≤ ∑ y, 4*((valence v y:ℤ)-3) := by
      apply Finset.sum_le_sum; intro y _
      have := min3 y; unfold flag; split <;> simp <;> omega
    _ = _ := by
      rw [←Finset.mul_sum,Finset.sum_sub_distrib,←all]; simp; ring

section
variable {V E : Type*} [DecidableEq V] [Fintype E] {a b : E→V} {U : Finset V}

abbrev oppDeg (p : Presentation a b U) {y:p.Face} (i:p.Sectors y) :=
  p.d (p.mate ⟨y,i⟩).1
abbrev gapOwner (p : Presentation a b U) {y:p.Face} : p.Sectors y→Option (p.Sectors y) :=
  let : Fintype (p.Sectors y) := p.cornerFinite y
  let : DecidableEq (p.Sectors y) := p.cornerDec y
  (p.incidences y).owner
abbrev nxtMark (p : Presentation a b U) (y:p.Face) : p.Sectors y ≃ p.Sectors y :=
  let : Fintype (p.Sectors y) := p.cornerFinite y
  let : DecidableEq (p.Sectors y) := p.cornerDec y
  (p.incidences y).nxt
abbrev gapLen (p : Presentation a b U) {y:p.Face} (i:p.Sectors y) :=
  @bucket (p.Sectors y) (p.cornerFinite y) (p.cornerDec y)
    (gapOwner p) (fun j=>p.span ⟨y,j⟩) i
abbrev gapCount (p : Presentation a b U) {y:p.Face} (i:p.Sectors y) :=
  @bucket (p.Sectors y) (p.cornerFinite y) (p.cornerDec y)
    (gapOwner p) (fun _=>1) i

/-- Raw sector permutations and branch incidence for sharp vertex accounting.
The consecutive opposite faces meet across a third edge at a trivalent junction,
giving a budget of s+t-1 edges for a bicycle if they are small. -/
structure Rotation (p : Presentation a b U) where
  vertex : Sigma p.Sectors → Fin p.v
  val3 : letI := p.faceFinite; letI := p.cornerFinite; ∀ b, 3≤valence vertex b
  clockwise : Sigma p.Sectors ≃ Sigma p.Sectors
  stays : ∀ t, vertex (clockwise t)=vertex t
  forward : ∀ y, p.Sectors y ≃ p.Sectors y
  neighbor : ∀ y i, p.d (clockwise ⟨y,forward y i⟩).1 = oppDeg p i ∨
    p.d (clockwise ⟨y,forward y i⟩).1 = oppDeg p (forward y i)
  adjacent : ∀ y i, short (oppDeg p i) → gapLen p i=0 → forward y i=(nxtMark p y) i
  single : ∀ y (i j : p.Sectors y), short (oppDeg p i) →
    (gapOwner p) j=some i → gapCount p i=1 →
    forward y i=j ∧ forward y j=(nxtMark p y) i
  third : letI := p.faceFinite; letI := p.cornerFinite; ∀ y i,
    valence vertex (vertex ⟨y,forward y i⟩)≤3 → oppDeg p i≤10 → oppDeg p (forward y i)≤10 →
    RankTest a b (oppDeg p i + oppDeg p (forward y i)-1)

def high (p : Presentation a b U) (o : Rotation p) (t : Sigma p.Sectors) : ℤ :=
  let : Fintype p.Face := p.faceFinite
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  flag (4≤valence o.vertex (o.vertex t))

theorem high_sum (p : Presentation a b U) (o : Rotation p) :
    let := p.faceFinite; letI := p.cornerFinite
    (∑ t : Sigma p.Sectors, high p o t) ≤ 4*(2*(p.e:ℤ)-3*(p.v:ℤ)) := by
  dsimp only
  let : Fintype p.Face := p.faceFinite
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  have h := high_capacity o.vertex o.val3
  have eqn := p.threads
  simp only [Fintype.card_sigma,Nat.cast_sum,Fintype.card_fin] at h
  change (∑ i : Sigma p.Sectors, flag (4≤valence o.vertex (o.vertex i))) ≤ _
  omega

/-- Lift a permutation on the sector positions of each face. -/
def permSector {F : Type*} {I : F → Type*} (e : ∀ y,I y≃I y) : Sigma I ≃ Sigma I where
  toFun t := ⟨t.1,e t.1 t.2⟩
  invFun t := ⟨t.1,(e t.1).symm t.2⟩
  left_inv := by rintro ⟨y,i⟩; simp
  right_inv := by rintro ⟨y,i⟩; simp

theorem two_slots {X : Type*} [Fintype X] (request high' color : X→ℤ)
    (first second : X≃X)
    (h₁ : ∀ t, request t≤ if color (first t)=0 then high' (first t) else 0)
    (h₂ : ∀ t, request t≤ if color (second t)=0 then 0 else high' (second t)) :
    2*(∑ t,request t) ≤ ∑ t,high' t := by
  let l t := if color t=0 then high' t else 0
  let r t := if color t=0 then 0 else high' t
  have e₁ := Finset.sum_le_sum (s:=(univ:Finset X)) (f:=request) (g:=fun t=>l (first t)) (fun i _=>h₁ i)
  have e₂ := Finset.sum_le_sum (s:=(univ:Finset X)) (f:=request) (g:=fun t=>r (second t)) (fun i _=>h₂ i)
  rw [first.sum_comp l] at e₁; rw [second.sum_comp r] at e₂
  have eqn : (∑ t,l t)+(∑ t,r t)=∑ t,high' t := by
    rw [←Finset.sum_add_distrib]; apply Finset.sum_congr rfl
    intro i _; dsimp [l,r]; split <;> simp
  omega

def needB (p : Presentation a b U) (t : Sigma p.Sectors) : ℤ :=
  flag (10≤p.d t.1 ∧ short (oppDeg p t.2) ∧ gapLen p t.2=0)

theorem bonusB_total (p : Presentation a b U) (o : Rotation p) (ns : NoSmallBicyclic a b 14) :
    let := p.faceFinite; letI := p.cornerFinite
    2*(∑ t : Sigma p.Sectors, needB p t) ≤ 4*(2*(p.e:ℤ)-3*(p.v:ℤ)) := by
  dsimp only
  let : Fintype p.Face := p.faceFinite
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y,DecidableEq (p.Sectors y) := p.cornerDec
  let A := permSector o.forward
  let B := A.trans o.clockwise
  let col (t : Sigma p.Sectors) := flag (short (p.d t.1))
  have linked (t : Sigma p.Sectors) (z : needB p t≠0) :
      high p o (A t)=1 ∧ high p o (B t)=1 ∧ col (A t)=0 ∧ col (B t)≠0 := by
    rcases t with ⟨y,i⟩
    have hz : 10≤p.d y ∧ short (oppDeg p i) ∧ gapLen p i=0 := by
      simpa [needB,flag] using z
    have nxt := o.adjacent y i hz.2.1 hz.2.2
    have sh := ((p.incidences y).marked i).mp hz.2.1
    have nshort : short (oppDeg p (o.forward y i)) := nxt ▸ sh
    have sm : short (p.d (o.clockwise ⟨y,o.forward y i⟩).1) := by
      rcases o.neighbor y i with e|e
      · exact e ▸ hz.2.1
      · exact e ▸ nshort
    have hv : 4≤valence o.vertex (o.vertex ⟨y,o.forward y i⟩) := by
      by_contra! bad
      have := rank_limit ns (o.third y i (by omega) (by unfold short at hz; omega)
        (by unfold short at nshort; omega))
      unfold short at nshort hz
      norm_num at this; omega
    change high p o ⟨y,o.forward y i⟩=1 ∧ high p o (o.clockwise ⟨y,o.forward y i⟩)=1 ∧
      flag (short (p.d y))=0 ∧ flag (short (p.d (o.clockwise ⟨y,o.forward y i⟩).1))≠0
    have non : ¬short (p.d y) := by unfold short; omega
    simp [high,flag,hv,o.stays,sm,non]
  have val (t : Sigma p.Sectors) : needB p t=0 ∨ needB p t=1 := by unfold needB flag; split <;> simp
  have nn t : 0≤high p o t := by change 0≤flag (4≤valence o.vertex (o.vertex t)); unfold flag; split <;> decide
  have h := two_slots (needB p) (high p o) col A B (fun t => by
    rcases val t with h|h
    · rw [h]; split <;> simp [nn]
    · have z:=linked t (by omega); simp [h,z.2.2.1,z.1])
    (fun t => by
      rcases val t with h|h
      · rw [h]; split <;> simp [nn]
      · have z:=linked t (by omega); simp [h,z.2.2.2,z.2.1])
  exact le_trans h (high_sum p o)
end
end ConwayThrackle.ThreadA

namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

def cashB (s r : ℤ) := 8*tag s 6 r + 3*tag s 8 r - 2*tag s 6 1 - 2*tag s 8 1

theorem budgetB (D k z u v x y : ℤ) (mind : 6≤D) (ev : D%2=0)
    (u₀ : 0≤u) (v₀ : 0≤v) (x₀ : u≤x) (y₀ : v≤y) (cov : x+y≤D)
    (c₆ : x≤min 6 (D-10)*u) (c₈ : y≤min 8 (D-8)*v)
    (g : 10≤D → 4*u≤D-x-y ∧ 2*(u+v)≤k+z)
    (ex : x+y<D → u+v+1≤k) (kt : u+v≤k) (zn : 0≤z) :
    108 ≤ 12*D + 2*(k-6)+2*z +
      (if D=6 then 8*D-2*k else if D=8 then 3*D-2*k else 0)-(8*x+3*y-2*u-2*v) := by
  by_cases ht : 30≤D
  · simp [show D≠6 by omega,show D≠8 by omega]; omega
  · have casesD : D=6 ∨ D=8 ∨ D=10 ∨ D=12 ∨ D=14 ∨ D=16 ∨ D=18 ∨ D=20 ∨ D=22 ∨
        D=24 ∨ D=26 ∨ D=28 := by omega
    rcases casesD with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num at c₆ c₈ g ⊢ <;> omega

section
variable {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype E]
    {a b : E→V} {D : ℤ} {s r : I→ℤ}
def zeroBonus (w : Local a b D s r) (i : I) :=
  flag (10≤D ∧ short (s i) ∧ bucket w.owner r i=0)

theorem marked_corners (w : Local a b D s r) (lg : 10≤D) :
    2*(countOf s 6+countOf s 8) ≤ Fintype.card I+∑ i,zeroBonus w i := by
  have pt (i:I) : markedUnit (s i) ≤ bucket w.owner (fun _=>1) i + zeroBonus w i := by
    have n := bucket_nonneg w.owner (fun _=>1) (by intro; decide) i
    have n' := bucket_nonneg w.owner r (fun j=>le_trans (by decide) (w.positive j)) i
    by_cases sh : short (s i)
    · by_cases z : bucket w.owner r i=0
      · simp [markedUnit,zeroBonus,flag,lg,sh,z]; omega
      · have p := bucket_count_pos w.owner r i (by omega)
        simp [markedUnit,zeroBonus,flag,lg,sh,z]; omega
    · simp [markedUnit,zeroBonus,flag,sh,n]
  have h := Finset.sum_le_sum (s:=(Finset.univ : Finset I)) (fun i _=>pt i)
  rw [Finset.sum_add_distrib,sum_marked] at h
  have room:=bucket_room w.owner (fun _=>1) s (by intro; decide) w.uncovered
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at room
  unfold countOf at h ⊢; omega

theorem faceB (ns : NoSmallBicyclic a b 14) (w : Local a b D s r) :
    108 ≤ 12*D+2*((Fintype.card I:ℤ)-6)+2*(∑ i,zeroBonus w i) +
      (∑ i,cashB D (r i)) - ∑ i,cashB (s i) (r i) := by
  have c₆ := sum_cap 6 (min 6 (D-10)) (s:=s) (r:=r) (fun i hi=>by
    have := plain_cap w ns 6 (by decide) i hi; omega)
  have c₈ := sum_cap 8 (min 8 (D-8)) (s:=s) (r:=r) (fun i hi=>by
    have := plain_cap w ns 8 (by decide) i hi; omega)
  have gp (lg : 10≤D) : 4*countOf s 6≤D-weightOf s r 6-weightOf s r 8 := by
    have z := gap_moment w 2 0 1 (by decide) (fun i=>by
      have := bucket_nonneg w.owner r (fun j=>le_trans (by decide) (w.positive j)) i
      have hm:=w.marked i
      have hb (h:short (s i)) := rank_limit ns (w.rankGap i lg h)
      norm_num at hb; grind only [short,tag])
    omega
  have h := budgetB D (Fintype.card I) (∑i,zeroBonus w i) (countOf s 6) (countOf s 8)
    (weightOf s r 6) (weightOf s r 8) w.degree w.parity (count_nonneg 6) (count_nonneg 8)
    (cover_low w 6) (cover_low w 8) (cover_total w) c₆ c₈
    (fun lg=>⟨gp lg,marked_corners w lg⟩) (extra_corner w) (count_total w)
    (Finset.sum_nonneg (by intro i _; unfold zeroBonus flag; split <;> decide))
  have inc : (∑ i,cashB D (r i)) =
      if D=6 then 8*D-2*Fintype.card I else if D=8 then 3*D-2*Fintype.card I else 0 := by
    by_cases he : D=6 <;> by_cases he' : D=8 <;>
      simp [cashB,tag,he,he',Finset.sum_sub_distrib,←Finset.mul_sum,w.boundary] <;> ring
  rw [inc]
  simpa only [cashB,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,
    countOf,weightOf] using h

theorem bound_of_NSB14 (a b : E→V) [DecidableEq E] (ns : NoSmallBicyclic a b 14)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card → ∃ p : Presentation a b U, Nonempty (Rotation p))
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (9/7) U.card := by
  apply forest_reduction a b (9/7) (by norm_num) _ U
  intro W hc hm hr
  obtain ⟨p,⟨o⟩⟩ := emb W hc hm hr
  let : Fintype p.Face := p.faceFinite
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y,DecidableEq (p.Sectors y) := p.cornerDec
  let ex (y:p.Face) := 2*(∑ i:p.Sectors y,needB p ⟨y,i⟩)
  have bonus := bonusB_total p o ns
  change 2*(∑ t : Sigma p.Sectors, needB p t) ≤ _ at bonus
  rw [Fintype.sum_sigma] at bonus
  have z := settle p 108 12 2 cashB ex (by
    simp only [ex,←Finset.mul_sum]; omega)
    (fun y=>faceB ns (p.incidences y))
  have := p.chi_pos
  have q : 7*((onEdges a b W).card:ℚ) ≤ 9*(W.card:ℚ)-9 := by
    exact_mod_cast (show 7*((onEdges a b W).card:ℤ) ≤ 9*(W.card:ℤ)-9 by omega)
  linarith
end
end ConwayThrackle.ThreadA

namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

section
variable {V E : Type*} [DecidableEq V] [Fintype E] {a b : E→V} {U : Finset V}
def needC (p : Presentation a b U) (o : Rotation p) (t : Sigma p.Sectors) : ℤ :=
  flag (p.d t.1=14 ∧ oppDeg p t.2=10 ∧ p.span t=4 ∧
        oppDeg p ((o.forward t.1).symm t.2)=6 ∧ oppDeg p (o.forward t.1 t.2)=6)

theorem bonusC_total (p : Presentation a b U) (o : Rotation p) (ns : NoSmallBicyclic a b 14) :
    letI := p.faceFinite; letI := p.cornerFinite
    2*(∑ t : Sigma p.Sectors, needC p o t) ≤ 4*(2*(p.e:ℤ)-3*(p.v:ℤ)) := by
  let : Fintype p.Face := p.faceFinite
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let A := permSector o.forward
  let col (t : Sigma p.Sectors) := flag (oppDeg p t.2=6)
  have linked (t : Sigma p.Sectors) (z : needC p o t≠0) :
      high p o t=1 ∧ high p o (A t)=1 ∧ col t=0 ∧ col (A t)≠0 := by
    rcases t with ⟨y,i⟩
    have hz : p.d y=14 ∧ oppDeg p i=10 ∧ p.span ⟨y,i⟩=4 ∧ oppDeg p ((o.forward y).symm i)=6 ∧ oppDeg p (o.forward y i)=6 := by simpa [needC,flag] using z
    obtain ⟨_,hi,_,hb,ha⟩ := hz
    have hv : 4≤valence o.vertex (o.vertex ⟨y,o.forward y i⟩) := by
      by_contra! bad
      have t:=rank_limit ns (o.third y i (by omega) (by omega) (by omega))
      rw [hi,ha] at t; omega
    have hv' : 4≤valence o.vertex (o.vertex ⟨y,i⟩) := by
      by_contra! bad
      have t:=rank_limit ns (o.third y ((o.forward y).symm i)
        (by simpa using (show valence o.vertex (o.vertex ⟨y,i⟩)≤3 by omega))
        (by omega) (by simpa using (show oppDeg p i≤10 by omega)))
      simp only [Equiv.apply_symm_apply,hb,hi] at t; omega
    change high p o ⟨y,i⟩=1 ∧ high p o ⟨y,o.forward y i⟩=1 ∧
      flag (oppDeg p i=6)=0 ∧ flag (oppDeg p (o.forward y i)=6)≠0
    simp [high,flag,hv,hv',hi,ha]
  have val (t : Sigma p.Sectors) : needC p o t=0 ∨ needC p o t=1 := by unfold needC flag; split <;> simp
  have nn t : 0≤high p o t := by change 0≤flag (4≤valence o.vertex (o.vertex t)); unfold flag; split <;> decide
  have h := two_slots (needC p o) (high p o) col (Equiv.refl _) A (fun t => by
    change needC p o t≤if col t=0 then high p o t else 0
    rcases val t with h|h
    · rw [h]; split <;> simp [nn]
    · have z:=linked t (by omega); simp [h,z.2.2.1,z.1])
    (fun t => by
      rcases val t with h|h
      · rw [h]; split <;> simp [nn]
      · have z:=linked t (by omega); simp [h,z.2.2.2,z.2.1])
  exact le_trans h (high_sum p o)
end

def virtual (r:ℤ) := (r-1)/3
def cashC (s r : ℤ) := 29*tag s 6 r+12*tag s 8 r-6*tag s 6 1-6*tag s 8 1+6*tag s 10 (virtual r)

theorem point_eq {I : Type*} [Fintype I] {f g : I→ℤ} (h : ∀i,f i≤g i)
    (he : (∑i,g i)≤∑i,f i) (i:I) : f i=g i := by
  have sumh:=Finset.sum_le_sum (s:=(univ:Finset I)) (fun j _=>h j)
  have eqn : (∑ j, (g j - f j))=0 := by rw [Finset.sum_sub_distrib]; omega
  have z:=(Finset.sum_eq_zero_iff_of_nonneg (f:=fun j=>g j-f j) (fun j _=>by have:=h j;omega)).mp eqn i (mem_univ i)
  omega

theorem bucket_exact {I : Type*} [Fintype I] [DecidableEq I] (own : I→Option I) (w:I→ℤ) :
    (∑i,bucket own w i) = ∑j,if own j=none then 0 else w j := by
  unfold bucket; rw [Finset.sum_comm]; apply Finset.sum_congr rfl
  intro j _; cases hh:own j <;> simp

theorem budgetC (D k z u v x y pay virt : ℤ) (mind : 6≤D) (ev : D%2=0)
    (u₀ : 0≤u) (v₀ : 0≤v) (x₀ : u≤x) (y₀ : v≤y) (cov : x+y≤D)
    (c₆ : x ≤ (if D=12 then 1 else if D=14 then 3 else min 6 (D-10))*u)
    (c₈ : y ≤ (if D=10 then 1 else min 8 (D-8))*v)
    (kt : u+v≤k) (z₀ : 0≤z) (pay₀ : 0≤pay) (pv : 3*pay ≤ D-x-y-(k-u-v))
    (sp : D≤10 → pay=0) (v₀' : 0≤virt)
    (g : 10≤D → 4*u≤D-x-y ∧ 2*(u+v)≤k)
    (ex : x+y<D → u+v+1≤k)
    (sim : D=10 → D-x-y ≤ 3*(k-u-v+virt))
    (tight₁₂ : D=12 → pay ≤ k-u-v)
    (tight₁₄ : D=14 → u=2 → v=0 → x=6 → k=4 → pay≤z) :
    372 ≤ 39*D+6*(k-6)+6*z+(if D=6 then 29*D-6*k else if D=8 then 12*D-6*k
      else if D=10 then 6*virt else 0) -(29*x+12*y-6*u-6*v+6*pay) := by
  by_cases tail : 42≤D
  · simp [show D≠6 by omega,show D≠8 by omega,show D≠10 by omega]; omega
  · have d : D=6 ∨ D=8 ∨ D=10 ∨ D=12 ∨ D=14 ∨ D=16 ∨ D=18 ∨ D=20 ∨ D=22 ∨
        D=24 ∨ D=26 ∨ D=28 ∨ D=30 ∨ D=32 ∨ D=34 ∨ D=36 ∨ D=38 ∨ D=40 := by omega
    rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num at c₆ c₈ g sp sim tight₁₂ tight₁₄ ⊢
    all_goals first
      | omega
      | (have hu : u = 0 ∨ u = 1 ∨ u = 2 ∨ u = 3 := by omega
         have hv : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ 4 ≤ v := by omega
         have hp : pay = 0 ∨ pay = 1 ∨ 2 ≤ pay := by omega
         rcases hu with rfl|rfl|rfl|rfl <;>
           rcases hv with rfl|rfl|rfl|rfl|hv <;>
           rcases hp with rfl|rfl|hp <;> omega)

end ConwayThrackle.ThreadA

namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators
section
variable {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype E]
    {a b : E→V} {D : ℤ} {s r : I→ℤ}

theorem ruled_path (w : Local a b D s r) (d : Detail w) (ns : NoSmallBicyclic a b 14)
    (i:I) (hd : D≤14) (hs : s i≤10) (hr : r i<D) (hr' : r i<s i)
    (cost : D+s i-r i=16) {M : Multiset ℕ} (ban : ¬hasTheta a b M)
    (ident : legs (r i) (s i-r i) (D-r i)=M) : False := by
  rcases d.path i hd hs hr hr' with h|h
  · have := rank_limit ns h.some; omega
  · exact ban (ident ▸ h)

theorem capC6 (w : Local a b D s r) (d : Detail w) (ns : NoSmallBicyclic a b 14)
    (drop : NoSmallBicyclic a b 15 ∨ CExclusions a b) (i:I) (hi : s i=6) :
    r i ≤ if D=12 then 1 else if D=14 then 3 else min 6 (D-10) := by
  rcases drop with strong | ban
  · have := plain_cap w strong 6 (by decide) i hi
    split_ifs <;> omega
  have h := plain_cap w ns 6 (by decide) i hi
  split
  · rename_i hd; by_contra! ng
    have hr : r i=2 := by omega
    exact ruled_path w d ns i (by omega) (by omega) (by omega) (by omega)
      (by omega) ban.th2410 (by rw [hi,hd,hr]; decide)
  · split
    · rename_i hd; by_contra! ng
      have hr : r i=4 := by omega
      exact ruled_path w d ns i (by omega) (by omega) (by omega) (by omega)
        (by omega) ban.th2410 (by rw [hi,hd,hr]; decide)
    · omega

theorem capC8 (w : Local a b D s r) (d : Detail w) (ns : NoSmallBicyclic a b 14)
    (drop : NoSmallBicyclic a b 15 ∨ CExclusions a b) (i:I) (hi : s i=8) :
    r i ≤ if D=10 then 1 else min 8 (D-8) := by
  rcases drop with strong | ban
  · have := plain_cap w strong 8 (by decide) i hi
    split_ifs <;> omega
  have h := plain_cap w ns 8 (by decide) i hi
  split
  · rename_i hd; by_contra! ng
    have hr : r i=2 := by omega
    exact ruled_path w d ns i (by omega) (by omega) (by omega) (by omega)
      (by omega) ban.th268 (by rw [hi,hd,hr]; decide)
  · omega

theorem small_ten (w : Local a b D s r) (d : Detail w) (ns : NoSmallBicyclic a b 14)
    (drop : NoSmallBicyclic a b 15 ∨ CExclusions a b) (md : D≤10) (i:I) (hi : s i=10) : virtual (r i)=0 := by
  rcases drop with strong | ban
  · have := rank_limit strong (d.ten i hi)
    have := w.positive i
    unfold virtual; omega
  have h := rank_limit ns (d.ten i hi)
  have pos := w.positive i
  unfold virtual; by_contra ng
  have hd : D=10 := by omega
  have hr : r i=4 := by omega
  exact ruled_path w d ns i (by omega) (by omega) (by omega) (by omega)
    (by omega) ban.th466 (by rw [hi,hd,hr]; decide)

theorem gaps_pos (w : Local a b D s r) (d : Detail w) (ns : NoSmallBicyclic a b 14)
    (drop : NoSmallBicyclic a b 15 ∨ CExclusions a b) (hd : 10≤D) (i:I) (sh : short (s i)) :
    0<bucket w.owner r i := by
  rcases drop with strong | ban
  · have hb := rank_limit strong (w.rankGap i hd sh)
    have ht := (w.marked i).mp sh
    unfold short at ht sh; omega
  have hb := rank_limit ns (w.rankGap i hd sh)
  have ht := (w.marked i).mp sh
  have nn := bucket_nonneg w.owner r (fun j=>le_trans (by decide) (w.positive j)) i
  by_contra! ng
  have g0 : bucket w.owner r i=0 := by omega
  unfold short at sh ht
  have s1 : s i=8 := by omega
  have s2 : s (w.nxt i)=8 := by omega
  rcases d.wedge i s1 s2 g0 with h|h
  · have := rank_limit ns h.some; omega
  · exact ban.db880 h

theorem nbC (w : Local a b D s r) (d : Detail w) (ns : NoSmallBicyclic a b 14)
    (drop : NoSmallBicyclic a b 15 ∨ CExclusions a b) (hd : 10≤D) :
    2*(countOf s 6+countOf s 8)≤ Fintype.card I := by
  have m := marked_corners w hd
  have z : (∑i,zeroBonus w i)=0 := Finset.sum_eq_zero (by
    intro i _; by_cases h:short (s i)
    · have := gaps_pos w d ns drop hd i h
      simp [zeroBonus,flag,ne_of_gt this]
    · simp [zeroBonus,flag,h])
  omega

theorem poolC (w : Local a b D s r) :
    3*(∑i,tag (s i) 10 (virtual (r i))) ≤
      D-weightOf s r 6-weightOf s r 8-((Fintype.card I:ℤ)-countOf s 6-countOf s 8) := by
  have h (i:I) : 3*tag (s i) 10 (virtual (r i)) ≤ r i-tag (s i) 6 (r i)-
      tag (s i) 8 (r i)-(1-tag (s i) 6 1-tag (s i) 8 1) := by
    have pos := w.positive i; simp only [tag,virtual]; split_ifs <;> omega
  have e := Finset.sum_le_sum (s:=(univ:Finset I)) (fun i _=>h i)
  simpa only [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,mul_one,countOf,weightOf,w.boundary] using e

theorem sim10 (w : Local a b D s r) :
    D-weightOf s r 6-weightOf s r 8 ≤ 3*((Fintype.card I:ℤ)-countOf s 6-countOf s 8+
      ∑i,virtual (r i)) := by
  have h (i:I) : r i-tag (s i) 6 (r i)-tag (s i) 8 (r i) ≤
      3*(1-tag (s i) 6 1-tag (s i) 8 1 +virtual (r i)) := by
    have pos := w.positive i; simp only [tag,virtual]; split_ifs <;> omega
  have e := Finset.sum_le_sum (s:=(univ:Finset I)) (fun i _=>h i)
  simpa only [Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,
    Finset.card_univ,nsmul_eq_mul,mul_one,countOf,weightOf,w.boundary] using e

theorem smallpay12 (w : Local a b D s r) (d : Detail w) (ns : NoSmallBicyclic a b 14)
    (hd : D=12) :
    (∑i,tag (s i) 10 (virtual (r i)))≤(Fintype.card I:ℤ)-countOf s 6-countOf s 8 := by
  have h (i:I) : tag (s i) 10 (virtual (r i)) ≤ 1-tag (s i) 6 1-tag (s i) 8 1 := by
    by_cases hh:s i=10
    · have z:=rank_limit ns (d.ten i hh); simp [tag,hh,virtual]; omega
    · simp only [tag]; split_ifs <;> omega
  have e := Finset.sum_le_sum (s:=(univ:Finset I)) (fun i _=>h i)
  simpa only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,countOf] using e

/-- Equality case of gap ownership. Every marked run is followed by exactly
one thread of length four; no unmarked thread lies outside these gaps. -/
theorem four_gap (w : Local a b D s r) (ns : NoSmallBicyclic a b 14) (hd : D=14)
    (cu : countOf s 6=2) (cv : countOf s 8=0) (cx : weightOf s r 6=6)
    (ck : (Fintype.card I:ℤ)=4) :
    (∀ i, s i≠8) ∧ (∀ i, bucket w.owner r i=4*markedUnit (s i)) ∧
    (∀ i, bucket w.owner (fun _=>1) i=markedUnit (s i)) ∧
    (∀ j, ¬short (s j) → ∃ i,w.owner j=some i) := by
  have no8 (i:I) : s i≠8 := by
    intro e
    have h:=Finset.single_le_sum (s:=(univ:Finset I)) (f:=fun t=>tag (s t) 8 1)
      (fun t _=>by unfold tag; split <;> decide) (mem_univ i)
    have on : tag (s i) 8 1=1 := by simp [tag,e]
    rw [on] at h; unfold countOf at cv; omega
  have cy : weightOf s r 8=0 := Finset.sum_eq_zero (by intro i _;simp [tag,no8])
  have total : (∑i,markedUnit (s i))=2 := by rw [sum_marked,cu,cv]; decide
  have bounds (i:I) : 4*markedUnit (s i)≤bucket w.owner r i ∧
      markedUnit (s i)≤bucket w.owner (fun _=>1) i := by
    by_cases h:short (s i)
    · have ht := (w.marked i).mp h
      have si : s i=6 := h.resolve_right (no8 i)
      have st : s (w.nxt i)=6 := ht.resolve_right (no8 _)
      have z:=rank_limit ns (w.rankGap i (by omega) h)
      have wide : 4≤bucket w.owner r i := by omega
      simpa [markedUnit,h] using And.intro wide (bucket_count_pos w.owner r i (by omega))
    · simp [markedUnit,h,bucket_nonneg w.owner r (fun j=>le_trans (by decide) (w.positive j)),
        bucket_nonneg w.owner (fun _=>1) (by intro;decide)]
  have wg := bucket_room w.owner r s (fun j=>le_trans (by decide) (w.positive j)) w.uncovered
  have wc := bucket_room w.owner (fun _=>1) s (by intro;decide) w.uncovered
  simp only [Finset.sum_sub_distrib,w.boundary,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at wg wc
  have gn : (∑i,bucket w.owner r i)≤8 := by unfold weightOf at cx cy;omega
  have cn : (∑i,bucket w.owner (fun _=>1) i)≤2 := by unfold countOf at cu cv;omega
  have geq i := (point_eq (fun j=>(bounds j).1)
    (by rw [←Finset.mul_sum,total];exact gn) i).symm
  have ceq i := (point_eq (fun j=>(bounds j).2) (by rw [total];exact cn) i).symm
  refine ⟨no8,geq,ceq,?_⟩
  have owners := bucket_exact w.owner (fun _=>(1:ℤ))
  simp only [ceq,total] at owners
  have dom (j:I) : (if w.owner j=none then (0:ℤ) else 1) ≤ 1-markedUnit (s j) := by
    cases hh:w.owner j with
    | none => simp only [ite_true]; unfold markedUnit; split <;> decide
    | some i => simp [markedUnit,w.uncovered j i hh]
  have cover : ∀j, (if w.owner j=none then (0:ℤ) else 1) = 1-markedUnit (s j) :=
    point_eq dom (by rw [Finset.sum_sub_distrib,total]; simp; omega)
  intro j hj; have e:=cover j
  cases hh:w.owner j with
  | none => simp [hh,markedUnit,hj] at e
  | some i => exact ⟨i,rfl⟩
end
end ConwayThrackle.ThreadA

namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

section
variable {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype E]
    {a b : E→V} {D : ℤ} {s r : I→ℤ}

theorem lone_pay (w : Local a b D s r) (ns : NoSmallBicyclic a b 14) (turn : I≃I)
    (singleGap : ∀ i j, short (s i) → w.owner j=some i → bucket w.owner (fun _=>1) i=1 →
       turn i=j ∧ turn j=w.nxt i)
    (hd : D=14) (cu : countOf s 6=2) (cv : countOf s 8=0) (cx : weightOf s r 6=6)
    (ck : (Fintype.card I:ℤ)=4) :
    (∑ j,tag (s j) 10 (virtual (r j))) ≤
      ∑ j,flag (D=14 ∧ s j=10 ∧ r j=4 ∧ s (turn.symm j)=6 ∧ s (turn j)=6) := by
  obtain ⟨no8,ge,ce,assign⟩ := four_gap w ns hd cu cv cx ck
  apply Finset.sum_le_sum; intro j _
  by_cases h : s j=10
  · obtain ⟨i,hi⟩ := assign j (by unfold short;omega)
    have ub : r j≤bucket w.owner r i := by
      unfold bucket
      exact le_trans (show r j≤(if w.owner j=some i then r j else 0) by simp [hi])
        (Finset.single_le_sum (f:=fun z => if w.owner z=some i then r z else 0)
        (by intro z _; by_cases q : w.owner z=some i
            · have := w.positive z; simp [q]; omega
            · simp [q]) (mem_univ j))
    have rg:=w.positive j
    have sh : short (s i) := by
      by_contra ng; rw [ge] at ub; simp [markedUnit,ng] at ub; omega
    have rc := ce i
    simp only [markedUnit,sh,ite_true] at rc
    obtain ⟨bef,aft⟩ := singleGap i j sh hi rc
    have so : s (turn.symm j)=6 := by
      rw [←bef,Equiv.symm_apply_apply]
      exact sh.resolve_right (no8 i)
    have sn : s (turn j)=6 := by rw [aft]; exact ((w.marked i).mp sh).resolve_right (no8 _)
    rw [ge] at ub; simp only [markedUnit,sh,ite_true,mul_one] at ub
    by_cases rr:r j=4
    · simp [tag,h,virtual,flag,hd,so,sn,rr]
    · simp [tag,h,virtual,flag,rr];omega
  · simp [tag,h,flag]

set_option maxHeartbeats 1000000 in
theorem faceC (ns : NoSmallBicyclic a b 14) (drop : NoSmallBicyclic a b 15 ∨ CExclusions a b)
    (w : Local a b D s r) (d : Detail w) (turn : I≃I)
    (singleGap : ∀ i j, short (s i) → w.owner j=some i → bucket w.owner (fun _=>1) i=1 →
       turn i=j ∧ turn j=w.nxt i) :
    372≤39*D+6*((Fintype.card I:ℤ)-6)+
      6*(∑ j,flag (D=14 ∧ s j=10 ∧ r j=4 ∧ s (turn.symm j)=6 ∧ s (turn j)=6))+
      (∑ i,cashC D (r i))-∑ i,cashC (s i) (r i) := by
  let z (j:I) := flag (D=14 ∧ s j=10 ∧ r j=4 ∧ s (turn.symm j)=6 ∧ s (turn j)=6)
  have c₆ := sum_cap 6 _ (capC6 w d ns drop)
  have c₈ := sum_cap 8 _ (capC8 w d ns drop)
  have gp (lg:10≤D) : 4*countOf s 6≤D-weightOf s r 6-weightOf s r 8 := by
    have g:=gap_moment w 2 0 1 (by decide) (fun i=>by
      have := bucket_nonneg w.owner r (fun j=>le_trans (by decide) (w.positive j)) i
      have hm:=w.marked i
      have hb (h:short (s i)) := rank_limit ns (w.rankGap i lg h)
      norm_num at hb;grind only [short,tag])
    omega
  have sp (md:D≤10) : (∑i,tag (s i) 10 (virtual (r i)))=0 := by
    apply Finset.sum_eq_zero;intro i _
    by_cases hi:s i=10
    · simp [tag,hi,small_ten w d ns drop md i hi]
    · simp [tag,hi]
  have bh := budgetC D (Fintype.card I) (∑i,z i) (countOf s 6) (countOf s 8) (weightOf s r 6)
      (weightOf s r 8) (∑i,tag (s i) 10 (virtual (r i))) (∑i,virtual (r i))
      w.degree w.parity (count_nonneg 6) (count_nonneg 8) (cover_low w 6) (cover_low w 8)
      (cover_total w) c₆ c₈ (count_total w) (Finset.sum_nonneg (by intro j _; unfold z flag; split <;> decide))
      (Finset.sum_nonneg (by intro i _; have := w.positive i; unfold tag virtual; split <;> omega))
      (poolC w) sp (Finset.sum_nonneg (by intro i _; have := w.positive i;unfold virtual;omega))
      (fun hd=>⟨gp hd,nbC w d ns drop hd⟩) (extra_corner w) (fun _ => sim10 w) (smallpay12 w d ns)
      (lone_pay w ns turn singleGap)
  have inc : (∑i,cashC D (r i))=(if D=6 then 29*D-6*(Fintype.card I:ℤ)
      else if D=8 then 12*D-6*(Fintype.card I:ℤ) else if D=10 then 6*(∑i,virtual (r i)) else 0) := by
    by_cases h:D=6 <;> by_cases h':D=8 <;> by_cases h'':D=10 <;>
      simp [cashC,tag,h,h',h'',Finset.sum_sub_distrib,←Finset.mul_sum,w.boundary] <;> ring
  rw [inc]
  simpa only [cashC,Finset.sum_sub_distrib,Finset.sum_add_distrib,←Finset.mul_sum,
    weightOf,countOf,z] using bh

theorem boundC (a b : E→V) [DecidableEq E] (ns : NoSmallBicyclic a b 14)
    (drop : NoSmallBicyclic a b 15 ∨ CExclusions a b)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card → ∃ p : Presentation a b U, hasDetails p ∧ Nonempty (Rotation p))
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (62/49) U.card := by
  apply forest_reduction a b (62/49) (by norm_num) _ U
  intro W hc hm hr
  obtain ⟨p,detail,⟨o⟩⟩ := emb W hc hm hr
  let : Fintype p.Face := p.faceFinite
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y,DecidableEq (p.Sectors y) := p.cornerDec
  let ex (y:p.Face) := 6*(∑ i:p.Sectors y,needC p o ⟨y,i⟩)
  have bonus := bonusC_total p o ns
  change 2*(∑ t : Sigma p.Sectors,needC p o t)≤_ at bonus
  rw [Fintype.sum_sigma] at bonus
  have z:=settle p 372 39 6 cashC ex (by simp only [ex,←Finset.mul_sum]; omega)
    (fun y=>faceC ns drop (p.incidences y) (detail y).some (o.forward y) (o.single y))
  have := p.chi_pos
  have q : 49*((onEdges a b W).card:ℚ) ≤ 62*(W.card:ℚ)-62 := by
    exact_mod_cast (show 49*((onEdges a b W).card:ℤ) ≤ 62*(W.card:ℤ)-62 by omega)
  linarith

theorem bound_of_C4 (a b : E→V) [DecidableEq E] (ns : NoSmallBicyclic a b 14)
    (ban : CExclusions a b)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card → ∃ p : Presentation a b U, hasDetails p ∧ Nonempty (Rotation p))
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (62/49) U.card :=
  boundC a b ns (.inr ban) emb U

theorem bound_of_NSB15 (a b : E→V) [DecidableEq E] (ns : NoSmallBicyclic a b 15)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card → ∃ p : Presentation a b U, hasDetails p ∧ Nonempty (Rotation p))
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (62/49) U.card :=
  boundC a b (fun W hw => ns W (by omega)) (.inl ns) emb U

end
end ConwayThrackle.ThreadA

namespace ConwayThrackle.ThreadA
open Finset
open scoped BigOperators

/-- Two vertex-disjoint octagons and a single edge joining them. -/
def hasOctBridge {V E : Type*} (a b : E→V) : Prop :=
  ∃ p q : OctCircuit a b, (∀ i j,p.pt i≠q.pt j) ∧
    ∃ (i j : Fin 8) (e:E), joins a b e (p.pt i) (q.pt j)

def bridgeTest {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype E]
    {a b : E→V} {D : ℤ} {s r : I→ℤ} (w : Local a b D s r) : Prop :=
  ∀ i, s i=8 → s (w.nxt i)=8 → bucket w.owner r i=1 →
    Nonempty (RankTest a b 16) ∨ hasOctBridge a b

def hasBridgeTests {V E : Type*} [DecidableEq V] [Fintype E] {a b : E→V}
    {U : Finset V} (p : Presentation a b U) : Prop :=
  let : ∀ y, Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y, DecidableEq (p.Sectors y) := p.cornerDec
  ∀ y, bridgeTest (p.incidences y)

theorem budgetEb (D u v x y : ℤ) (mind : 6 ≤ D) (even : D%2=0)
    (u₀ : 0 ≤ u) (v₀ : 0 ≤ v) (x₀ : u ≤ x) (y₀ : v ≤ y) (covered : x+y ≤ D)
    (cap₆ : x ≤ min 6 (D-11)*u) (cap₈ : y ≤ (if D=10 then 0 else min 8 (D-9))*v)
    (gap : 10 ≤ D → 5*u+v ≤ D-x-y ∧ 4*u+2*v ≤ D-x-y) :
    120 ≤ 12*D + (if D=6 then 8*D else if D=8 then 3*D else 0) - (8*x+3*y) := by
  by_cases tail : 30 ≤ D
  · simp [show D≠6 by omega,show D≠8 by omega]; omega
  · have d : D=6 ∨ D=8 ∨ D=10 ∨ D=12 ∨ D=14 ∨ D=16 ∨ D=18 ∨ D=20 ∨ D=22 ∨
        D=24 ∨ D=26 ∨ D=28 := by omega
    rcases d with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
      norm_num at cap₆ cap₈ gap ⊢ <;> omega

theorem faceEb {I V E : Type*} [Fintype I] [DecidableEq I] [DecidableEq V] [Fintype E]
    {a b : E→V} (ns : NoSmallBicyclic a b 15) (noTh : ¬hasTheta a b (legs 1 7 9))
    (noBridge : ¬hasOctBridge a b) {D : ℤ} {s r : I→ℤ} (w : Local a b D s r)
    (d : Detail w) (bt : bridgeTest w) :
    120 ≤ 12*D + (∑ i,rate16 D (r i)) - ∑ i,rate16 (s i) (r i) := by
  have c₆ := sum_cap 6 (min 6 (D-11)) (s:=s) (r:=r) (fun i hi=>by
    have := plain_cap w ns 6 (by decide) i hi;omega)
  have c₈ := sum_cap 8 (if D=10 then 0 else min 8 (D-9)) (s:=s) (r:=r) (fun i hi=>by
    have ub := plain_cap w ns 8 (by decide) i hi
    have pos := w.positive i
    split
    · rename_i hd
      have hr : r i=1 := by omega
      rcases d.path i (by omega) (by omega) (by omega) (by omega) with small|th
      · have := rank_limit ns small.some;omega
      · rw [hi,hd,hr] at th
        exact False.elim (noTh (by convert th using 1;decide))
    · omega)
  have spacing (lg : 10≤D) : 5*countOf s 6+countOf s 8 ≤ D-weightOf s r 6-weightOf s r 8 ∧
      4*countOf s 6+2*countOf s 8 ≤ D-weightOf s r 6-weightOf s r 8 := by
    have facts (i:I) : 0≤bucket w.owner r i ∧ (short (s i) ↔ short (s (w.nxt i))) ∧
        (short (s i) → 17≤s i+s (w.nxt i)+bucket w.owner r i) ∧
        (s i=8 → s (w.nxt i)=8 → 2≤bucket w.owner r i) := by
      have hb (h:short (s i)) := rank_limit ns (w.rankGap i lg h)
      norm_num at hb
      refine ⟨bucket_nonneg w.owner r (fun j=>le_trans (by decide) (w.positive j)) i,w.marked i,hb,?_⟩
      intro hi hj
      have h₁:=hb (Or.inr hi)
      by_contra! small
      rcases bt i hi hj (by omega) with h|h
      · have := rank_limit ns h.some; omega
      · exact noBridge h
    have h₁ := gap_moment w 5 1 2 (by decide) (fun i=>by
      obtain ⟨a,b,c,d⟩ := facts i; grind only [short,tag])
    have h₂ := gap_moment w 4 2 2 (by decide) (fun i=>by
      obtain ⟨a,b,c,d⟩ := facts i; grind only [short,tag])
    omega
  have hb := budgetEb D (countOf s 6) (countOf s 8) (weightOf s r 6) (weightOf s r 8)
    w.degree w.parity (count_nonneg 6) (count_nonneg 8) (cover_low w 6) (cover_low w 8)
    (cover_total w) c₆ c₈ spacing
  have inc : (∑i,rate16 D (r i))=if D=6 then 8*D else if D=8 then 3*D else 0 := by
    by_cases h:D=6 <;> by_cases h':D=8 <;> simp [rate16,tag,h,h',←Finset.mul_sum,w.boundary]
  rw [inc]; simpa only [rate16,Finset.sum_add_distrib,←Finset.mul_sum,weightOf] using hb

theorem bound_of_E2b {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (a b : E→V) (ns : NoSmallBicyclic a b 15) (noTh : ¬hasTheta a b (legs 1 7 9))
    (noBridge : ¬hasOctBridge a b)
    (emb : ∀ U : Finset V, conn a b U → (∀ x ∈ U, 2 ≤ (incident a b U x).card) →
       U.card < (onEdges a b U).card →
       ∃ p : Presentation a b U, hasDetails p ∧ hasBridgeTests p)
    (U : Finset V) : ((onEdges a b U).card:ℚ) ≤ target (5/4) U.card := by
  apply forest_reduction a b (5/4) (by norm_num) _ U
  intro W hc hm hr
  obtain ⟨p,dp,bp⟩ := emb W hc hm hr
  let : ∀ y,Fintype (p.Sectors y) := p.cornerFinite
  let : ∀ y,DecidableEq (p.Sectors y) := p.cornerDec
  have z := settle p 120 12 0 rate16 (fun _=>0) (by simp) (fun y=>by
    simpa using faceEb ns noTh noBridge (p.incidences y) (dp y).some (bp y))
  have := p.chi_pos
  have q : 4*((onEdges a b W).card:ℚ) ≤ 5*(W.card:ℚ)-5 := by
    exact_mod_cast (show 4*((onEdges a b W).card:ℤ) ≤ 5*(W.card:ℤ)-5 by omega)
  linarith
end ConwayThrackle.ThreadA

