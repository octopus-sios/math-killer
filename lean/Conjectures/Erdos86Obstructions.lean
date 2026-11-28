import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Square defects and structural obstructions in the hypercube

Vertices are Boolean coordinate vectors. A graph records, at each vertex, the
directions present; the reversal law identifies the two ends of each edge.
-/

namespace Erdos86Obstructions

open Finset
open scoped BigOperators

abbrev Vertex (ι : Type*) := ι → Bool

def flip {ι : Type*} [DecidableEq ι] (x : Vertex ι) (i : ι) : Vertex ι :=
  fun k => if k = i then !(x k) else x k

@[simp] theorem flip_self {ι : Type*} [DecidableEq ι] (x : Vertex ι) (i : ι) :
    flip x i i = !(x i) := by simp [flip]

@[simp] theorem flip_other {ι : Type*} [DecidableEq ι] {x : Vertex ι} {i j : ι} (h : j ≠ i) :
    flip x i j = x j := by simp [flip, h]

@[simp] theorem flip_twice {ι : Type*} [DecidableEq ι] (x : Vertex ι) (i : ι) :
    flip (flip x i) i = x := by
  funext k
  by_cases h : k = i <;> simp [flip, h]

theorem flip_comm {ι : Type*} [DecidableEq ι] (x : Vertex ι) (i j : ι) :
    flip (flip x i) j = flip (flip x j) i := by
  funext k
  by_cases hij : i = j
  · subst j; rfl
  · by_cases hi : k = i
    · subst k; simp [flip, hij]
    · by_cases hj : k = j
      · subst k; simp [flip, hi]
      · simp [flip, hi, hj]

private theorem sum_flip {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*}
    [AddCommMonoid R] (f : Vertex ι → R) (i : ι) :
    (∑ x, f (flip x i)) = ∑ x, f x := by
  let e : Vertex ι ≃ Vertex ι :=
    ⟨fun x => flip x i, fun x => flip x i, fun x => flip_twice x i, fun x => flip_twice x i⟩
  exact e.sum_comp f

structure Graph (ι : Type*) [DecidableEq ι] where
  edge : Vertex ι → ι → Bool
  reverse : ∀ x i, edge (flip x i) i = edge x i

variable {ι : Type*} [DecidableEq ι]

def C4Free (G : Graph ι) : Prop :=
  ∀ x i j, i ≠ j → ¬(G.edge x i = true ∧ G.edge x j = true ∧
    G.edge (flip x i) j = true ∧ G.edge (flip x j) i = true)

def OddSquare (G : Graph ι) : Prop :=
  ∀ x i j, i ≠ j → (G.edge x i ^^ G.edge x j ^^
    G.edge (flip x i) j ^^ G.edge (flip x j) i) = true

def dirs [Fintype ι] (G : Graph ι) (x : Vertex ι) : Finset ι :=
  univ.filter fun i => G.edge x i = true

def degree [Fintype ι] (G : Graph ι) (x : Vertex ι) : ℕ := (dirs G x).card

private def sign (b : Bool) : ℤ := if b then 1 else -1

private theorem sign_sq (b : Bool) : (sign b)^2 = 1 := by cases b <;> decide

private theorem degree_signs [Fintype ι] (G : Graph ι) (x : Vertex ι) :
    2 * (degree G x : ℤ) - Fintype.card ι = ∑ i, sign (G.edge x i) := by
  classical
  have h : (degree G x : ℤ) = ∑ i, if G.edge x i = true then (1 : ℤ) else 0 := by
    simp [degree, dirs, Finset.sum_boole]
  rw [h, Finset.mul_sum]
  calc
    _ = ∑ i : ι, (2 * (if G.edge x i = true then (1 : ℤ) else 0) - 1) := by
      simp [Finset.sum_sub_distrib]
    _ = _ := by apply Finset.sum_congr rfl; intro i _; cases G.edge x i <;> decide

private theorem square_sum [Fintype ι] [LinearOrder ι] (f : ι → ℤ) :
    (∑ i, f i)^2 = (∑ i, (f i)^2) +
      2 * ∑ i, ∑ j, if i < j then f i * f j else 0 := by
  classical
  have h (i j : ι) : f i * f j =
      (if i = j then (f i)^2 else 0) + ((if i < j then f i * f j else 0) +
        (if j < i then f j * f i else 0)) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, h.ne, not_lt_of_ge h.le]
    · simp [sq]
    · simp [h, h.ne', not_lt_of_ge h.le, mul_comm]
  rw [sq, Finset.sum_mul]
  conv_lhs => simp only [Finset.mul_sum]
  trans ∑ i, ∑ j, ((if i = j then (f i)^2 else 0) + ((if i < j then f i * f j else 0) +
        (if j < i then f j * f i else 0)))
  · apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _; exact h i j
  simp_rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hswap : (∑ i : ι, ∑ j : ι, if j < i then f j * f i else 0) =
      ∑ i : ι, ∑ j : ι, if i < j then f i * f j else 0 := Finset.sum_comm
  rw [hswap]; ring

private theorem sum_halves [Fintype ι] (f : Vertex ι → ℤ) (i : ι) :
    ∑ x, f x = ∑ x, if x i then 0 else f x + f (flip x i) := by
  let p (x : Vertex ι) : ℤ := if x i then f x else 0
  calc
    _ = (∑ x : Vertex ι, if x i then 0 else f x) + ∑ x, p x := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _; cases h : x i <;> simp [p, h]
    _ = _ := by
      rw [← sum_flip p i, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _; cases h : x i <;> simp [p, h]

private theorem sum_squares [Fintype ι] (f : Vertex ι → ℤ) {i j : ι} (h : i ≠ j) :
    ∑ x, f x = ∑ x, if x i = false ∧ x j = false then
      f x + f (flip x i) + f (flip x j) + f (flip (flip x j) i) else 0 := by
  calc
    _ = _ := sum_halves f i
    _ = _ := sum_halves _ j
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      cases hi : x i <;> cases hj : x j <;> simp [hi, flip_other h, add_assoc]

private def isEmptySq (a b c d : Bool) : Bool := !(a || b || c || d)
private def isOppSq (a b c d : Bool) : Bool :=
  (a && d && !b && !c) || (b && c && !a && !d)

private def squareCount {n : ℕ} (G : Graph (Fin n)) (P : Bool → Bool → Bool → Bool → Bool) : ℤ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then ∑ x : Vertex (Fin n),
    if x i = false ∧ x j = false then
      (if P (G.edge x i) (G.edge x j) (G.edge (flip x i) j) (G.edge (flip x j) i)
       then 1 else 0) else 0 else 0

/-- Count squares once, at their corner with both varying coordinates false. -/
def emptySquares {n : ℕ} (G : Graph (Fin n)) : ℤ := squareCount G isEmptySq

/-- Count squares with exactly two opposite retained edges. -/
def oppositeSquares {n : ℕ} (G : Graph (Fin n)) : ℤ := squareCount G isOppSq

private theorem corner_total (a b c d : Bool) (h : ¬(a = true ∧ b = true ∧ c = true ∧ d = true)) :
    sign a * sign b + sign a * sign c + sign d * sign b + sign d * sign c =
    4 * ((if isEmptySq a b c d then 1 else 0) - (if isOppSq a b c d then 1 else 0)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [sign, isEmptySq, isOppSq]

private theorem transpose_sum {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β → γ → ℤ) : (∑ x, ∑ i, ∑ j, f x i j) = ∑ i, ∑ j, ∑ x, f x i j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _; exact Finset.sum_comm

/-- Wang's exact square-defect identity, for unrestricted square-free cube subgraphs. -/
theorem squareDefectIdentity {n : ℕ} (G : Graph (Fin n)) (hG : C4Free G) :
    (∑ x, (2 * (degree G x : ℤ) - n)^2) =
      (n : ℤ) * 2^n + 8 * (emptySquares G - oppositeSquares G) := by
  classical
  have deg (x : Vertex (Fin n)) : 2 * (degree G x : ℤ) - n = ∑ i, sign (G.edge x i) := by
    simpa using degree_signs G x
  simp_rw [deg, square_sum, sign_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Int.mul_one, ← Finset.mul_sum]
  rw [transpose_sum]
  have cv : (Fintype.card (Vertex (Fin n)) : ℤ) = 2 ^ n := by simp [Vertex]
  rw [cv, mul_comm (2^n : ℤ) n]
  congr 1
  unfold emptySquares oppositeSquares squareCount
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hij : i < j
  · simp only [hij, ite_true]
    rw [sum_squares (fun x => sign (G.edge x i) * sign (G.edge x j)) hij.ne,
      ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro x _
    by_cases hx : x i = false ∧ x j = false
    · simp only [hx, true_and, ite_true, G.reverse]
      rw [flip_comm x j i, G.reverse]
      rw [corner_total _ _ _ _ (hG x i j hij.ne)]
      ring
    · simp [hx]
  · simp [hij]


/-!
## Capacity across adjacent three-dimensional fibres

If both parallel fibres retain two of the three directions at every vertex,
their common retained graph has degrees in [1,2]. The positions of retained
connecting edges are independent in this common graph. Counting oriented
common edges out of these positions therefore gives at most five connectors.
-/

private theorem fibre_capacity (G : Graph ι) (hG : C4Free G)
    (b : Fin 3 → ι) (j : ι) (hj : ∀ i, b i ≠ j)
    (v : Vertex (Fin 3) → Vertex ι)
    (hv : ∀ t i, v (flip t i) = flip (v t) (b i))
    (deg : ∀ x, (∑ i : Fin 3, (G.edge x (b i)).toNat) = 2) :
    (∑ t, (G.edge (v t) j).toNat) ≤ 5 := by
  let s (t : Vertex (Fin 3)) := G.edge (v t) j
  let p (t : Vertex (Fin 3)) (i : Fin 3) := G.edge (v t) (b i)
  let q (t : Vertex (Fin 3)) (i : Fin 3) := G.edge (flip (v t) j) (b i)
  let c (t : Vertex (Fin 3)) (i : Fin 3) := p t i && q t i
  have band (t) : 1 ≤ ∑ i, (c t i).toNat ∧ (∑ i, (c t i).toNat) ≤ 2 := by
    have h₁ (i) : (p t i).toNat + (q t i).toNat ≤ 1 + (c t i).toNat := by
      unfold c; cases p t i <;> cases q t i <;> decide
    have h₂ (i) : (c t i).toNat ≤ (p t i).toNat := by
      unfold c; cases p t i <;> cases q t i <;> decide
    have l := Finset.sum_le_sum (s := univ) (fun i _ => h₁ i)
    have u := Finset.sum_le_sum (s := univ) (fun i _ => h₂ i)
    have hp : (∑ i, (p t i).toNat) = 2 := deg _
    have hq : (∑ i, (q t i).toNat) = 2 := deg _
    simp only [Finset.sum_add_distrib, hp, hq, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at l
    omega
  have rev (t i) : c (flip t i) i = c t i := by
    dsimp [c, p, q]; rw [hv, flip_comm (v t) (b i) j]; simp [G.reverse]
  have indep (t i) (hs : s t = true) (hc : c t i = true) : s (flip t i) = false := by
    by_contra! hn
    have pq : p t i = true ∧ q t i = true := Bool.and_eq_true_iff.mp hc
    exact hG (v t) (b i) j (hj i) ⟨pq.1, hs, by simpa [s, hv] using hn, pq.2⟩
  let a (t : Vertex (Fin 3)) (i : Fin 3) := (s t && c t i).toNat
  have lo (t) : (s t).toNat ≤ ∑ i, a t i := by
    cases h : s t <;> simp [a, h, (band t).1]
  have up (t) : (∑ i, a (flip t i) i) + 2 * (s t).toNat ≤ 2 := by
    cases h : s t with
    | false =>
      simp only [Bool.toNat_false, Nat.mul_zero, Nat.add_zero]
      apply le_trans _ (band t).2
      apply Finset.sum_le_sum; intro i _
      dsimp [a]; rw [rev]; cases s (flip t i) <;> cases c t i <;> decide
    | true =>
      have hz (i) : a (flip t i) i = 0 := by
        dsimp [a]; rw [rev]
        cases hc : c t i <;> simp [*, indep t i]
      simp [hz]
  have recount : (∑ t, ∑ i, a (flip t i) i) = ∑ t, ∑ i, a t i := by
    calc
      _ = ∑ i : Fin 3, ∑ t, a (flip t i) i := Finset.sum_comm
      _ = ∑ i : Fin 3, ∑ t, a t i := by
        apply Finset.sum_congr rfl; intro i _; exact sum_flip (fun t => a t i) i
      _ = _ := Finset.sum_comm
  have l := Finset.sum_le_sum (s := univ) (fun t _ => lo t)
  have u := Finset.sum_le_sum (s := univ) (fun t _ => up t)
  have card : Fintype.card (Vertex (Fin 3)) = 8 := by simp [Vertex]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, recount, Finset.sum_const,
    Finset.card_univ, card, nsmul_eq_mul] at u
  change (∑ t, (s t).toNat) ≤ 5
  omega

private def layer (e : Fin 3 × Fin 3 ≃ ι) (t : Vertex (Fin 3)) : Vertex ι :=
  fun k => if (e.symm k).1 = 0 then t (e.symm k).2 else false

private theorem layer_flip (e : Fin 3 × Fin 3 ≃ ι) (t : Vertex (Fin 3)) (i : Fin 3) :
    layer e (flip t i) = flip (layer e t) (e (0,i)) := by
  funext k
  obtain ⟨⟨u,w⟩,rfl⟩ := e.surjective k
  by_cases hu : u = 0 <;> by_cases hw : w = i <;> simp [layer, flip, Prod.ext_iff, hu, hw]

/-- For an arbitrary labelling of the nine directions by block and position,
no square-free graph has degree exactly two in every block at every vertex. -/
theorem hamiltonFibreObstruction (e : Fin 3 × Fin 3 ≃ Fin 9) (G : Graph (Fin 9))
    (hG : C4Free G) :
    ¬ ∀ x (d : Fin 3), (∑ i : Fin 3, (G.edge x (e (d,i))).toNat) = 2 := by
  intro deg
  have cap (j : Fin 3) : (∑ t, (G.edge (layer e t) (e (1,j))).toNat) ≤ 5 :=
    fibre_capacity G hG (fun i => e (0,i)) _ (by intro i; simp) (layer e) (layer_flip e)
      (fun x => deg x 0)
  have total := Finset.sum_le_sum (s := univ) (fun j _ => cap j)
  rw [Finset.sum_comm] at total
  simp [deg, Vertex] at total


/-!
## Odd-square switches

Edges are counted at their unique even endpoint. Switching a subset of a single
parity class toggles disjoint stars, so the gains add.
-/

def parity [Fintype ι] (x : Vertex ι) : Bool :=
  decide ((∑ k, (x k).toNat) % 2 = 1)

@[simp] theorem parity_flip [Fintype ι] (x : Vertex ι) (i : ι) :
    parity (flip x i) = !(parity x) := by
  classical
  let a := ∑ k ∈ (univ : Finset ι).erase i, (x k).toNat
  have h₁ : (∑ k, (x k).toNat) = a + (x i).toNat :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  have h₂ : (∑ k, (flip x i k).toNat) = a + (!x i).toNat := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), flip_self]
    congr 1
    apply Finset.sum_congr rfl; intro k hk
    rw [flip_other (Finset.ne_of_mem_erase hk)]
  simp only [parity, h₁, h₂]
  cases h : x i <;> simp only [Bool.not_false, Bool.not_true, Bool.toNat_true, Bool.toNat_false]
    <;> rcases Nat.mod_two_eq_zero_or_one a with hh | hh <;> simp [Nat.add_mod, hh]

def edges [Fintype ι] (G : Graph ι) (side : Bool := false) : Finset (Vertex ι × ι) :=
  univ.filter fun e => parity e.1 = side ∧ G.edge e.1 e.2 = true

def edgeCount [Fintype ι] (G : Graph ι) : ℕ := (edges G false).card

/-- Maximum cardinality among odd-square subgraphs of the n-cube. -/
noncomputable def g (n : ℕ) : ℕ :=
  sSup {k | ∃ G : Graph (Fin n), OddSquare G ∧ edgeCount G = k}

theorem le_g {n : ℕ} {G : Graph (Fin n)} (hG : OddSquare G) : edgeCount G ≤ g n := by
  unfold g
  refine le_csSup ?_ (Set.mem_ofPred.mpr ⟨G, hG, rfl⟩)
  refine ⟨Fintype.card (Vertex (Fin n) × Fin n), ?_⟩
  rintro k ⟨K,_,rfl⟩
  exact Finset.card_le_univ _

private def otherEnd (e : Vertex ι × ι) : Vertex ι × ι := (flip e.1 e.2, e.2)

private theorem other_twice (e : Vertex ι × ι) : otherEnd (otherEnd e) = e := by
  rcases e with ⟨x,i⟩; simp [otherEnd]

private theorem count_side [Fintype ι] (G : Graph ι) (p : Bool) :
    edgeCount G = (edges G p).card := by
  cases p with
  | false => rfl
  | true =>
    unfold edgeCount
    apply Finset.card_bij (fun e _ => otherEnd e)
    · rintro ⟨x,i⟩ he
      simpa [edges, otherEnd, G.reverse] using he
    · intro x _ y _ he
      simpa only [other_twice] using congrArg otherEnd he
    · rintro ⟨x,i⟩ he
      refine ⟨otherEnd (x,i), ?_, other_twice _⟩
      simpa [edges, otherEnd, G.reverse] using he

private theorem count_degree [Fintype ι] (G : Graph ι) (p : Bool) :
    (edgeCount G : ℤ) = ∑ x, if parity x = p then (degree G x : ℤ) else 0 := by
  classical
  rw [count_side G p]
  calc
    _ = ∑ e : Vertex ι × ι, if parity e.1 = p ∧ G.edge e.1 e.2 = true then (1 : ℤ) else 0 := by
      simp [edges, Finset.sum_boole]
    _ = ∑ x : Vertex ι, ∑ i : ι, if parity x = p ∧ G.edge x i = true then (1 : ℤ) else 0 :=
      Fintype.sum_prod_type _
    _ = _ := by
      apply Finset.sum_congr rfl; intro x _
      by_cases hx : parity x = p <;> simp [hx, degree, dirs, Finset.sum_boole]

private def switch [Fintype ι] (G : Graph ι) (U : Finset (Vertex ι)) : Graph ι where
  edge x i := G.edge x i ^^ decide (x ∈ U) ^^ decide (flip x i ∈ U)
  reverse x i := by
    rw [flip_twice, G.reverse]
    cases decide (x ∈ U) <;> cases decide (flip x i ∈ U) <;> cases G.edge x i <;> rfl

private theorem cancel_marks (a b c d u v w z : Bool) :
    ((a ^^ u ^^ v) ^^ (b ^^ u ^^ w) ^^ (c ^^ v ^^ z) ^^ (d ^^ w ^^ z)) =
      (a ^^ b ^^ c ^^ d) := by decide +revert

private theorem odd_switch [Fintype ι] (G : Graph ι) (oG : OddSquare G) (U : Finset (Vertex ι)) :
    OddSquare (switch G U) := by
  intro x i j hij
  dsimp [switch]
  rw [flip_comm x j i, cancel_marks, oG x i j hij]

private def gain {n : ℕ} (G : Graph (Fin n)) (x : Vertex (Fin n)) : ℤ :=
  n - 2 * (degree G x : ℤ)

private theorem switch_gain {n : ℕ} (G : Graph (Fin n)) (U : Finset (Vertex (Fin n)))
    (p : Bool) (hU : ∀ x ∈ U, parity x = p) :
    (edgeCount (switch G U) : ℤ) = edgeCount G + ∑ x ∈ U, gain G x := by
  classical
  rw [count_degree (switch G U) p, count_degree G p]
  have hu_sum : (∑ x ∈ U, gain G x) = ∑ x, if x ∈ U then gain G x else 0 := by
    rw [← Finset.sum_filter]; simp
  rw [hu_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  by_cases hx : parity x = p
  · have away (i : Fin n) : flip x i ∉ U := by
      intro hi
      have ha := hU _ hi
      rw [parity_flip, hx] at ha
      cases p <;> contradiction
    by_cases hu : x ∈ U
    · have hc : dirs (switch G U) x = (dirs G x)ᶜ := by
        ext i; cases he : G.edge x i <;> simp [dirs, switch, hu, away, he]
      simp only [hx, ite_true, hu, degree, gain, hc, Finset.card_compl, Fintype.card_fin]
      have hle : (dirs G x).card ≤ n := by simpa using (dirs G x).card_le_univ
      omega
    · have hc : dirs (switch G U) x = dirs G x := by ext i; simp [dirs, switch, hu, away]
      simp [hx, hu, degree, hc]
  · have hu : x ∉ U := fun h => hx (hU _ h)
    simp [hu, hx]

private def added {n : ℕ} (H G : Graph (Fin n)) := edges H false \ edges G false
private def removed {n : ℕ} (H G : Graph (Fin n)) := edges G false \ edges H false

/-- Symmetric-difference cardinality of the undirected edge sets. -/
def editDistance {n : ℕ} (H G : Graph (Fin n)) : ℕ :=
  (added H G).card + (removed H G).card

private theorem balance {n : ℕ} (H G : Graph (Fin n)) :
    edgeCount H + (removed H G).card = edgeCount G + (added H G).card := by
  have h := Finset.card_sdiff_add_card_inter (edges H false) (edges G false)
  have g := Finset.card_sdiff_add_card_inter (edges G false) (edges H false)
  rw [Finset.inter_comm] at g
  unfold edgeCount added removed; omega

private def enc {n : ℕ} (x : Vertex (Fin n)) (i : Fin n) : Vertex (Fin n) × Fin n :=
  (if parity x then flip x i else x, i)

@[simp] private theorem mem_enc {n : ℕ} (G : Graph (Fin n)) (x : Vertex (Fin n)) (i : Fin n) :
    enc x i ∈ edges G false ↔ G.edge x i = true := by
  cases hp : parity x <;> simp [enc, edges, hp, G.reverse]

private theorem add_bits {n : ℕ} {H G : Graph (Fin n)} {x i} (ha : (x,i) ∈ added H G) :
    parity x = false ∧ H.edge x i = true ∧ G.edge x i = false := by
  simp [added, edges, and_assoc] at ha
  exact ⟨ha.1, ha.2.1, ha.2.2 ha.1⟩

private def common {n : ℕ} (G : Graph (Fin n)) (x : Vertex (Fin n)) (i : Fin n) :=
  dirs G x ∩ dirs G (flip x i)

private theorem union_sub {n : ℕ} (G : Graph (Fin n)) (x : Vertex (Fin n)) (i : Fin n)
    (hg : G.edge x i = false) :
    dirs G x ∪ dirs G (flip x i) ⊆ univ.erase i := by
  intro j hj
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  rintro rfl
  simp [dirs, G.reverse, hg] at hj

private theorem degree_pair {n : ℕ} (G : Graph (Fin n)) (x : Vertex (Fin n)) (i : Fin n) :
    degree G x + degree G (flip x i) =
      (dirs G x ∪ dirs G (flip x i)).card + (common G x i).card :=
  (Finset.card_union_add_card_inter _ _).symm

private def Witness {n : ℕ} (x : Vertex (Fin n)) (i j : Fin n) (e : Vertex (Fin n) × Fin n) :
    Prop := e = enc x j ∨ e = enc (flip x i) j ∨ e = enc (flip x j) i

private theorem forced_deletion {n : ℕ} (H G : Graph (Fin n)) (cf : C4Free H) (og : OddSquare G)
    {x i} (ha : (x,i) ∈ added H G) {j} (hj : j ∈ common G x i) :
    ∃ e ∈ removed H G, Witness x i j e := by
  obtain ⟨_,hh,hg⟩ := add_bits ha
  obtain ⟨l,r⟩ : G.edge x j = true ∧ G.edge (flip x i) j = true := by
    simpa [common, dirs] using hj
  have hij : i ≠ j := by rintro rfl; simp_all
  have opp := og x i j hij
  simp [hg,l,r] at opp
  by_cases h : H.edge x j = true
  · by_cases k : H.edge (flip x i) j = true
    · have d : H.edge (flip x j) i ≠ true := fun hd => cf x i j hij ⟨hh,h,k,hd⟩
      exact ⟨enc (flip x j) i, by simp [removed,opp,d], Or.inr (Or.inr rfl)⟩
    · exact ⟨enc (flip x i) j, by simp [removed,r,k], Or.inr (Or.inl rfl)⟩
  · exact ⟨enc x j, by simp [removed,l,h], Or.inl rfl⟩

private theorem flip_dir_inj {n : ℕ} (x : Vertex (Fin n)) : Function.Injective (flip x) := by
  intro i j h
  by_contra hn
  have hh := congrFun h i
  cases hi : x i <;> simp [flip, hn, hi] at hh

private theorem witness_unique {n : ℕ} {x : Vertex (Fin n)} {i j k : Fin n}
    {e : Vertex (Fin n) × Fin n} (hx : parity x = false) (hj : j ≠ i) (hk : k ≠ i)
    (a : Witness x i j e) (b : Witness x i k e) : j = k := by
  rcases a with rfl | rfl | rfl <;> rcases b with h | h | h
  all_goals first
    | exact congrArg Prod.snd h
    | exact (hj (congrArg Prod.snd h)).elim
    | exact (hk (congrArg Prod.snd h).symm).elim
    | have hh := congrArg Prod.fst h
      simp [enc, hx] at hh
      have h' := congrArg (fun v : Vertex (Fin n) => flip v i) hh
      exact flip_dir_inj x (by simpa only [flip_twice] using h')

/-- Each common retained direction at the ends of a new edge requires a distinct deletion. -/
private theorem common_le_removed {n : ℕ} (H G : Graph (Fin n)) (cf : C4Free H) (og : OddSquare G)
    {x i} (ha : (x,i) ∈ added H G) : (common G x i).card ≤ (removed H G).card := by
  classical
  let W := common G x i
  let D := removed H G
  have ex (j : W) : ∃ e ∈ D, Witness x i j e := forced_deletion H G cf og ha j.property
  let f (j : W) : D := ⟨(ex j).choose, (ex j).choose_spec.1⟩
  obtain ⟨hp,_,hg⟩ := add_bits ha
  have hj (j : W) : (j : Fin n) ≠ i := by
    intro he
    have hj' := j.property
    change j.val ∈ common G x i at hj'
    simp [he, common, dirs, hg] at hj'
  have hf : Function.Injective f := by
    intro j k he
    apply Subtype.ext
    apply witness_unique hp (hj j) (hj k) (ex j).choose_spec.2
    have hv : (ex j).choose = (ex k).choose := congrArg Subtype.val he
    rw [hv]; exact (ex k).choose_spec.2
  simpa [W, D] using Fintype.card_le_of_injective f hf

/-- In odd dimension, a square-free graph at edge distance at most three from
an odd-square graph has no more edges than the odd-square optimum. -/
theorem threeEdgeDefect {n : ℕ} (hn : Odd n) (H G : Graph (Fin n)) (cf : C4Free H)
    (og : OddSquare G) (hd : editDistance H G ≤ 3) : edgeCount H ≤ g n := by
  classical
  by_contra! bad
  have dist : (added H G).card + (removed H G).card ≤ 3 := hd
  have bal := balance H G
  have opt := le_g og
  have bound (U : Finset (Vertex (Fin n))) (p : Bool) (hu : ∀ x ∈ U, parity x = p) :
      (∑ x ∈ U, gain G x) ≤ (g n : ℤ) - edgeCount G := by
    have hs := switch_gain G U p hu
    have hm := le_g (odd_switch G og U)
    omega
  have single (x : Vertex (Fin n)) : gain G x ≤ (g n : ℤ) - edgeCount G := by
    simpa using bound {x} (parity x) (by simp)
  obtain ⟨m,hm⟩ := hn
  have small (x : Vertex (Fin n)) : gain G x ≤ 1 := by
    have h := single x; unfold gain at *; omega
  have ne : (added H G).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨⟨x₀,i₀⟩,h₀⟩ := ne
  have cap (x : Vertex (Fin n)) (i : Fin n) (ha : (x,i) ∈ added H G) :
      degree G x + degree G (flip x i) ≤ (n-1) + (removed H G).card := by
    have ub := Finset.card_le_card (union_sub G x i (add_bits ha).2.2)
    have ub' : (dirs G x ∪ dirs G (flip x i)).card ≤ n-1 := by simpa using ub
    have commonBound := common_le_removed H G cf og ha
    have pair := degree_pair G x i
    omega
  have noDel : (removed H G).card = 0 := by
    by_contra hpos
    have gains (x : Vertex (Fin n)) : gain G x ≤ -1 := by
      have hs := single x; unfold gain at *; omega
    have l := gains x₀
    have r := gains (flip x₀ i₀)
    have c := cap _ _ h₀
    unfold gain at l r
    omega
  have info (x : Vertex (Fin n)) (i : Fin n) (ha : (x,i) ∈ added H G) :
      gain G x = 1 ∧ dirs G x ∪ dirs G (flip x i) = univ.erase i := by
    have pair := degree_pair G x i
    have cm := common_le_removed H G cf og ha
    have c := cap x i ha
    have l := small x
    have r := small (flip x i)
    unfold gain at *
    constructor
    · omega
    · apply Finset.eq_of_subset_of_card_le (union_sub G x i (add_bits ha).2.2)
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
  have inj : Set.InjOn Prod.fst (added H G : Set (Vertex (Fin n) × Fin n)) := by
    rintro ⟨x,i⟩ hi ⟨y,j⟩ hj hxy
    change x = y at hxy; subst y
    by_contra neq
    have hij : i ≠ j := fun h => neq (h ▸ rfl)
    have bi := add_bits hi
    have bj := add_bits hj
    have propagate (k l : Fin n) (hk : (x,k) ∈ added H G) (hl : (x,l) ∈ added H G)
        (hne : l ≠ k) : G.edge (flip x k) l = true := by
      have hm' : l ∈ dirs G x ∪ dirs G (flip x k) := by
        rw [(info x k hk).2]; simp [hne]
      simpa [dirs, (add_bits hl).2.2] using hm'
    have g₁ := propagate i j hi hj hij.symm
    have g₂ := propagate j i hj hi hij
    have o := og x i j hij
    simp [bi.2.2, bj.2.2, g₁, g₂] at o
  let U := (added H G).image Prod.fst
  have cardU : U.card = (added H G).card := Finset.card_image_of_injOn inj
  have sideU : ∀ x ∈ U, parity x = false := by
    intro x hx
    obtain ⟨⟨y,i⟩,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (add_bits hi).1
  have gainU : ∀ x ∈ U, gain G x = 1 := by
    intro x hx
    obtain ⟨⟨y,i⟩,hi,rfl⟩ := Finset.mem_image.mp hx
    exact (info _ _ hi).1
  have bs := bound U false sideU
  have score : (∑ x ∈ U, gain G x) = (U.card : ℤ) := by
    calc
      _ = ∑ _x ∈ U, (1 : ℤ) := Finset.sum_congr rfl gainU
      _ = _ := by simp
  rw [score,cardU] at bs
  omega


end Erdos86Obstructions
