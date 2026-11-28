import Mathlib.Data.Fintype.Pi
import Mathlib.SetTheory.Cardinal.Finite

/-! # Balance of order ideals

A directed relation may give just the covers: downward closure along every
edge is equivalent to closure along every directed path. The counts are
cardinalities of actual subtypes, not numbers taken from a census. -/

namespace YiboGaoWeylConvexBalance.Ideals

abbrev Edges (X : Type) := X → X → Bool

def Ideal {X : Type} (E : Edges X) := {I : X → Bool // ∀ x y, E x y = true → I y = true → I x = true}

abbrev Side {X : Type} (E : Edges X) (x : X) (b : Bool) := {I : Ideal E // I.val x = b}

instance {X : Type} [Fintype X] [DecidableEq X] (E : Edges X) : Fintype (Ideal E) := by
  unfold Ideal; infer_instance

noncomputable def total {X : Type} (E : Edges X) := Nat.card (Ideal E)
noncomputable def side {X : Type} (E : Edges X) (x : X) (b : Bool) := Nat.card (Side E x b)
noncomputable def score {X : Type} (E : Edges X) (x : X) := 3 * min (side E x true) (side E x false)

/-- Balance equals one third, without division. -/
def OneThird {X : Type} (E : Edges X) : Prop :=
  0 < total E ∧ (∀ x, score E x ≤ total E) ∧ ∃ x, score E x = total E

def p₂ : Edges (Fin 2) := fun x y => x == 0 && y == 1
def p₄ : Edges (Fin 4) := fun x y =>
  ((x == 0 || x == 1) && y == 2) || (x == 2 && y == 3)
def p₇ : Edges (Fin 7) := fun x y =>
  ((x == 0 || x == 1) && y == 3) || ((x == 1 || x == 2) && y == 4) ||
  ((x == 3 || x == 4) && y == 5) || (x == 5 && y == 6)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem templateBalance : OneThird p₂ ∧ OneThird p₄ ∧ OneThird p₇ := by
  simp only [OneThird, score, side, total, Nat.card_eq_fintype_card]
  decide +kernel

/-- The ideal family detects every comparison, including transitive ones. -/
theorem reachable_iff_forall_ideals {X : Type} (E : Edges X) (x y : X) :
    Relation.ReflTransGen (fun a b => E a b = true) x y ↔
      ∀ I : Ideal E, I.val y = true → I.val x = true := by
  constructor
  · intro path I
    induction path with
    | refl => exact id
    | tail _ edge ih => exact fun h => ih (I.property _ _ edge h)
  · classical
    intro h
    let D : Ideal E := ⟨fun z => decide (Relation.ReflTransGen (fun a b => E a b = true) z y), by
      intro i j e r
      simp only [decide_eq_true_eq] at *
      exact r.head e⟩
    have top : D.val y = true := decide_eq_true Relation.ReflTransGen.refl
    exact of_decide_eq_true (h D top)

def dual {X : Type} (E : Edges X) : Edges X := fun x y => E y x

private def complement {X : Type} {E : Edges X} (I : Ideal E) : Ideal (dual E) :=
  ⟨fun x => !(I.val x), by
    intro x y hyx hy
    have h := I.property y x hyx
    cases hx : I.val x <;> cases hy' : I.val y <;> simp_all⟩

private def complementEquiv {X : Type} (E : Edges X) : Ideal E ≃ Ideal (dual E) where
  toFun := complement
  invFun := complement
  left_inv I := by apply Subtype.ext; funext x; simp [complement]
  right_inv I := by apply Subtype.ext; funext x; simp [complement]

private def complementSide {X : Type} (E : Edges X) (x : X) (b : Bool) :
    Side E x (!b) ≃ Side (dual E) x b where
  toFun I := ⟨complement I.val, by simp [complement, I.property]⟩
  invFun I := ⟨complement I.val, by simp [complement, I.property]⟩
  left_inv I := by apply Subtype.ext; exact (complementEquiv E).left_inv _
  right_inv I := by apply Subtype.ext; exact (complementEquiv E).right_inv _

theorem dual_iff {X : Type} (E : Edges X) : OneThird (dual E) ↔ OneThird E := by
  have n : total (dual E) = total E := (Nat.card_congr (complementEquiv E)).symm
  have h (x : X) (b : Bool) : side (dual E) x b = side E x (!b) :=
    (Nat.card_congr (complementSide E x b)).symm
  simp only [OneThird, score, n, h, Bool.not_true, Bool.not_false, Nat.min_comm (side E _ false)]

def union {X Y : Type} (E : Edges X) (G : Edges Y) : Edges (X ⊕ Y)
  | .inl x, .inl y => E x y
  | .inr x, .inr y => G x y
  | _, _ => false

private def splitIdeal {X Y : Type} (E : Edges X) (G : Edges Y) :
    Ideal (union E G) ≃ (Ideal E × Ideal G) where
  toFun I := (⟨fun x => I.val (.inl x),fun x y => I.property (.inl x) (.inl y)⟩,
              ⟨fun x => I.val (.inr x),fun x y => I.property (.inr x) (.inr y)⟩)
  invFun IJ := ⟨Sum.elim IJ.1.val IJ.2.val, by
    intro x y h
    cases x <;> cases y <;> first | contradiction | apply IJ.1.property _ _ h | apply IJ.2.property _ _ h⟩
  left_inv I := by apply Subtype.ext; funext x; cases x <;> rfl
  right_inv IJ := rfl

private def restrictFst {A B C : Type} (e : C ≃ A × B) (p : A → Prop) :
    {x : C // p (e x).1} ≃ ({a : A // p a} × B) where
  toFun x := (⟨(e x).1, x.property⟩, (e x).2)
  invFun x := ⟨e.symm (x.1.val,x.2), by simpa using x.1.property⟩
  left_inv x := by apply Subtype.ext; simp
  right_inv x := by ext1 <;> simp

private theorem min_scale (a b k : ℕ) : min (a*k) (b*k) = (min a b)*k := by
  rcases le_total a b with h|h
  · rw [min_eq_left h, min_eq_left (Nat.mul_le_mul_right _ h)]
  · rw [min_eq_right h, min_eq_right (Nat.mul_le_mul_right _ h)]

private theorem score_union_left {X Y : Type} (E : Edges X) (G : Edges Y) (x : X) :
    score (union E G) (.inl x) = score E x * total G := by
  have h (b : Bool) : side (union E G) (.inl x) b = side E x b * total G :=
    (Nat.card_congr (restrictFst (splitIdeal E G) (fun I => I.val x = b))).trans (Nat.card_prod _ _)
  simp only [score,h,min_scale, Nat.mul_assoc]

private theorem score_union_right {X Y : Type} (E : Edges X) (G : Edges Y) (y : Y) :
    score (union E G) (.inr y) = score G y * total E := by
  have h (b : Bool) : side (union E G) (.inr y) b = side G y b * total E :=
    (Nat.card_congr (restrictFst ((splitIdeal E G).trans (Equiv.prodComm ..))
      (fun I => I.val y = b))).trans (Nat.card_prod _ _)
  simp only [score,h,min_scale, Nat.mul_assoc]

/-- Arbitrary disjoint unions of equality components preserve equality. -/
theorem union_oneThird {X Y : Type} {E : Edges X} {G : Edges Y}
    (he : OneThird E) (hg : OneThird G) : OneThird (union E G) := by
  have tot : total (union E G) = total E * total G :=
    (Nat.card_congr (splitIdeal E G)).trans (Nat.card_prod _ _)
  refine ⟨tot ▸ Nat.mul_pos he.1 hg.1, ?_, ?_⟩
  · intro z; cases z with
    | inl x => rw [tot, score_union_left]; exact Nat.mul_le_mul_right _ (he.2.1 x)
    | inr y => rw [tot, score_union_right, Nat.mul_comm (total E)]; exact Nat.mul_le_mul_right _ (hg.2.1 y)
  · obtain ⟨x,h⟩ := he.2.2
    exact ⟨.inl x,by rw [score_union_left,tot,h]⟩

end YiboGaoWeylConvexBalance.Ideals
namespace YiboGaoWeylConvexBalance.Ideals

private def restrictIso {A B : Type} (e : A ≃ B) {p : A → Prop} {q : B → Prop}
    (h : ∀ a, p a ↔ q (e a)) : Subtype p ≃ Subtype q where
  toFun a := ⟨e a.val, (h a.val).mp a.property⟩
  invFun b := ⟨e.symm b.val, (h _).mpr (by simp [b.property])⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv b := by apply Subtype.ext; simp

/-! ## Chains of arbitrary length (the dihedral heap case) -/

def chain (n : ℕ) : Edges (Fin n) := fun x y => decide (x.val ≤ y.val)

private def initial {n : ℕ} (k : Fin (n+1)) : Ideal (chain n) :=
  ⟨fun x => decide (x.val < k.val), by
    intro x y h u; simp only [chain,decide_eq_true_eq] at *; omega⟩

private noncomputable def initialEquiv (n : ℕ) : Fin (n+1) ≃ Ideal (chain n) := by
  classical
  apply Equiv.ofBijective initial
  constructor
  · intro k l h
    have noLt {s t : Fin (n+1)} (lt : s.val < t.val) (eq : initial s = initial t) : False := by
      let i : Fin n := ⟨s.val,by have := t.isLt; omega⟩
      have a := congrArg (fun (I : Ideal (chain n)) => I.val i) eq
      simp [initial,i,lt] at a
    apply Fin.ext
    rcases lt_trichotomy k.val l.val with lt|m|gt
    · exact False.elim (noLt lt h)
    · exact m
    · exact False.elim (noLt gt h.symm)
  · intro I
    let bad (k : ℕ) := k=n ∨ ∃ i : Fin n, i.val=k ∧ I.val i=false
    have ex : ∃k, bad k := ⟨n,Or.inl rfl⟩
    let m := Nat.find ex
    have b : bad m := Nat.find_spec ex
    have mn : m ≤ n := Nat.find_min' ex (Or.inl rfl)
    refine ⟨⟨m,by omega⟩, ?_⟩
    apply Subtype.ext; funext x
    by_cases lt : x.val < m
    · have no := Nat.find_min ex lt
      have yes : I.val x=true := by
        cases h : I.val x with
        | true => rfl
        | false => exact False.elim (no (Or.inr ⟨x,rfl,h⟩))
      simp [initial,lt,yes]
    · have := x.isLt
      rcases b with hm|⟨i,hi,off⟩
      · omega
      · have down := I.property i x (by simp [chain,hi]; omega)
        cases hv : I.val x <;> simp_all [initial]

private def cutSide {n : ℕ} (x : Fin n) (b : Bool) :=
  {k : Fin (n+1) // decide (x.val < k.val) = b}

private def upperCuts {n : ℕ} (x : Fin n) : Fin (n-x.val) ≃ cutSide x true where
  toFun i := ⟨⟨x.val+1+i.val,by have := x.isLt; have := i.isLt; omega⟩, by simp; omega⟩
  invFun k := ⟨k.val.val-x.val-1,by
    have h := k.property; simp only [decide_eq_true_eq] at h
    have := k.val.isLt; have := x.isLt; omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv k := by
    apply Subtype.ext; apply Fin.ext; dsimp
    have h := k.property; simp only [decide_eq_true_eq] at h; omega

private def lowerCuts {n : ℕ} (x : Fin n) : Fin (x.val+1) ≃ cutSide x false where
  toFun i := ⟨⟨i.val,by have := i.isLt; have := x.isLt; omega⟩, by simp; have := i.isLt; omega⟩
  invFun k := ⟨k.val.val,by have h := k.property; simp at h; omega⟩
  left_inv i := rfl
  right_inv k := rfl

private theorem chain_counts (n : ℕ) (x : Fin n) :
    total (chain n) = n+1 ∧ side (chain n) x true = n-x.val ∧ side (chain n) x false = x.val+1 := by
  let e (b : Bool) : cutSide x b ≃ Side (chain n) x b :=
    restrictIso (initialEquiv n) fun _ => Iff.rfl
  exact ⟨(Nat.card_congr (initialEquiv n)).symm.trans (by simp),
    (Nat.card_congr ((upperCuts x).trans (e true))).symm.trans (by simp),
    (Nat.card_congr ((lowerCuts x).trans (e false))).symm.trans (by simp)⟩

/-- A chain, with no restriction on the number of points, has ideal
balance exactly one third if and only if it has two points. -/
theorem chain_iff (n : ℕ) : OneThird (chain n) ↔ n = 2 := by
  constructor
  · intro h
    obtain ⟨x,_⟩ := h.2.2
    have hn : 0<n := Nat.zero_lt_of_lt x.isLt
    let m : Fin n := ⟨n/2,by omega⟩
    obtain ⟨N,a,b⟩ := chain_counts n m
    have bound := h.2.1 m
    simp only [score,N,a,b] at bound; dsimp [m] at bound
    simp only [min_def] at bound; split at bound <;> omega
  · rintro rfl
    simp only [OneThird, score, side, total, Nat.card_eq_fintype_card]
    decide +kernel

end YiboGaoWeylConvexBalance.Ideals
