import Conjectures.YiboGaoWeylConvexBalance
import Conjectures.YiboGaoWeylConvexBalance.IdealBalance

/-! # The strip classification up to unlabelled order isomorphism

The regular vertices are nonconstant threshold events. A binary step
`i ≤ j ≤ i+1` gives the two interleaving implications between adjacent
columns. At a free terminal state all threshold points up to the gap are
below the block, and all higher ones are above it. This presentation may
include transitive edges; we compare *all order ideals* after one common
renaming of the points, not the literal edge lists or numerical invariants.
-/

namespace YiboGaoWeylConvexBalance

open Walls Ideals

inductive Point where
  | column (t k : ℕ)
  | block (z : ℕ)
deriving DecidableEq

def columns : List Layer → List Point
  | [] => []
  | (l,h)::s => columns s ++ (List.range (h-l)).map (fun k => .column (s.length+1) (l+k+1))

def Cap.size : Cap → ℕ
  | .plain => 0
  | .chain a _ => 2*a+3
  | .fork a _ => 2*a+2

def points (s : List Layer) (b : Cap) := columns s ++ (List.range b.size).map Point.block

def Cap.level : Cap → ℕ → ℕ
  | .fork a _, z => if z ≤ a then z else z-1
  | _, z => z

def generates (q : ℕ) (b : Cap) : Point → Point → Bool
  | .column t k, .column u h => decide
      ((t=u ∧ k<h) ∨ (u=t+1 ∧ h=k+1) ∨ (t=u+1 ∧ k=h))
  | .column t k, .block _ => decide (t=q ∧ k ≤ b.free)
  | .block _, .column t k => decide (t=q ∧ b.free < k)
  | .block x, .block y => decide (b.level x < b.level y)

def diagram (s : List Layer) (b : Cap) : Edges (Fin (points s b).length) := fun i j =>
  generates s.length b ((points s b).get i) ((points s b).get j)

def Closed {X : Type} (E : Edges X) (I : X → Bool) : Prop :=
  ∀ x y, E x y = true → I y = true → I x = true

/-- Equality of the unlabelled orders: under one vertex bijection the
families of lower sets coincide. These determine the whole generated order
(`x ≤ y` iff every ideal containing `y` contains `x`). -/
def SameHeap {X Y : Type} (E : Edges X) (G : Edges Y) : Prop :=
  ∃ e : X ≃ Y, ∀ I : Y → Bool, Closed G I ↔ Closed E (I ∘ e)

private instance {n : ℕ} (E : Edges (Fin n)) (f : Fin n → Bool) : Decidable (Closed E f) := by
  unfold Closed; infer_instance

private def isoIdeals {X Y : Type} {E : Edges X} {G : Edges Y} (e : X ≃ Y)
    (h : ∀ I : Y → Bool, Closed G I ↔ Closed E (I ∘ e)) : Ideal G ≃ Ideal E where
  toFun I := ⟨I.val ∘ e, (h _).mp I.property⟩
  invFun I := ⟨I.val ∘ e.symm, (h _).mpr (by simpa [Function.comp_def,Closed] using I.property)⟩
  left_inv I := by apply Subtype.ext; funext x; simp [Function.comp_def]
  right_inv I := by apply Subtype.ext; funext x; simp [Function.comp_def]

theorem SameHeap.oneThird_iff {X Y : Type} {E : Edges X} {G : Edges Y} (iso : SameHeap E G) :
    OneThird E ↔ OneThird G := by
  obtain ⟨e,h⟩ := iso
  let p := isoIdeals e h
  have n : total G = total E := Nat.card_congr p
  have sideEq (x : X) (b : Bool) : side G (e x) b = side E x b := by
    let f : Side G (e x) b ≃ Side E x b :=
      { toFun := fun I => ⟨p I.val,I.property⟩
        invFun := fun I => ⟨p.symm I.val, by change I.val.val (e.symm (e x)) = b; simpa using I.property⟩
        left_inv := fun I => Subtype.ext (p.left_inv _)
        right_inv := fun I => Subtype.ext (p.right_inv _) }
    exact Nat.card_congr f
  have sc (x : X) : score G (e x) = score E x := by simp only [score,sideEq]
  unfold OneThird; rw [n]; constructor
  · rintro ⟨pos,gap,x,hx⟩
    refine ⟨pos, fun y => ?_,e x, (sc x).trans hx⟩
    obtain ⟨z,rfl⟩ := e.surjective y; rw [sc]; exact gap z
  · rintro ⟨pos,gap,y,hy⟩
    obtain ⟨x,rfl⟩ := e.surjective y
    exact ⟨pos,fun z => (sc z) ▸ gap (e z),x,(sc x).symm.trans hy⟩

/-- Nonempty finite disjoint unions of the three templates, allowing each
component its own order dual and arbitrary renaming of vertices. -/
inductive TemplateUnion : {X : Type} → Edges X → Prop where
  | two : TemplateUnion p₂
  | four : TemplateUnion p₄
  | seven : TemplateUnion p₇
  | reverse {X : Type} {E : Edges X} : TemplateUnion E → TemplateUnion (dual E)
  | disjoint {X Y : Type} {E : Edges X} {G : Edges Y} :
      TemplateUnion E → TemplateUnion G → TemplateUnion (Ideals.union E G)
  | rename {X Y : Type} {E : Edges X} {G : Edges Y} : SameHeap E G → TemplateUnion E → TemplateUnion G

theorem templateUnion_oneThird {X : Type} {E : Edges X} (h : TemplateUnion E) : OneThird E := by
  induction h with
  | two => exact templateBalance.1
  | four => exact templateBalance.2.1
  | seven => exact templateBalance.2.2
  | reverse _ ih => exact (dual_iff _).2 ih
  | disjoint _ _ ih jh => exact union_oneThird ih jh
  | rename iso _ ih => exact iso.oneThird_iff.mp ih

def ClassicalShapes (s : List Layer) (b : Cap) : Prop :=
  SameHeap (diagram s b) p₂ ∨ SameHeap (diagram s b) p₄ ∨ SameHeap (diagram s b) (dual p₄)

private theorem listed_shapes {s : List Layer} {b : Cap} (h : listed s b) : ClassicalShapes s b := by
  have p : (s,b) ∈ examples := List.contains_iff_mem.mp h
  simp only [examples,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at p
  rcases p with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · left; refine ⟨Equiv.swap (0 : Fin 2) (1 : Fin 2), ?_⟩; decide +kernel
  · left; refine ⟨Equiv.refl (Fin 2), ?_⟩; decide +kernel
  · right; right; refine ⟨(Equiv.swap (1 : Fin 4) (2 : Fin 4)).trans (Equiv.swap 1 3), ?_⟩; decide +kernel
  · right; left; refine ⟨Equiv.swap (1 : Fin 4) (2 : Fin 4), ?_⟩; decide +kernel
  · right; left; refine ⟨((Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap 0 1)).trans
        (Equiv.swap 0 2), ?_⟩; decide +kernel
  · right; right; refine ⟨((Equiv.swap (0 : Fin 4) 3).trans (Equiv.swap 0 1)).trans
        (Equiv.swap 0 2), ?_⟩; decide +kernel

private theorem small_of_shapes {s : List Layer} {b : Cap} (h : ClassicalShapes s b) :
    (points s b).length ≤ 4 ∧ OneThird (diagram s b) := by
  obtain ⟨a,c,_⟩ := templateBalance
  have d := (dual_iff p₄).2 c
  rcases h with h|h|h
  all_goals
    refine ⟨?_,h.oneThird_iff.mpr (by assumption)⟩
    obtain ⟨e,_⟩ := h
    have := Fintype.card_congr e
    simp only [Fintype.card_fin] at this
    omega

private theorem column_length {S : Walls} {q : ℕ} (v : S.Valid q) {t : ℕ} (ht : t ≤ q) :
    t ≤ (columns (S.trace t)).length := by
  induction t with
  | zero => omega
  | succ t ih =>
    have := ih (by omega)
    have := v.wide (t+1) (by omega) ht
    simp [Walls.trace, columns]; omega

private def check {n : ℕ} (E : Edges (Fin n)) : Bool :=
  let N := Fintype.card (Ideal E)
  let z := fun x => 3 * min (Fintype.card (Side E x true)) (Fintype.card (Side E x false))
  decide (0<N ∧ (∀ x, z x ≤ N) ∧ ∃ x, z x=N)

private theorem check_correct {n : ℕ} (E : Edges (Fin n)) : check E ↔ OneThird E := by
  simp only [check,OneThird,score,side,total,Nat.card_eq_fintype_card,decide_eq_true_eq]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem shape_census : (List.range 5).all (fun q => (traces q).all fun s =>
    caps.all fun b => decide (4 < (points s b).length) ||
      !(decide (b.Fits (wallsOf s) q)) || !(check (diagram s b)) || listed s b) = true := by
  decide +kernel

/-- Balance in the strip model equals one third iff the unlabelled heap
is a chain on two points, the four-point template, or its dual. -/
theorem classicalHeapClassification {S : Walls} {q : ℕ} {b : Cap}
    (v : S.Valid q) (hf : b.Fits S q) :
    exactThird S q b = true ↔ ClassicalShapes (S.trace q) b := by
  rw [classicalStripClassification v hf]
  refine ⟨listed_shapes,fun shp => ?_⟩
  obtain ⟨short,balance⟩ := small_of_shapes shp
  have hq' := column_length v (le_refl q)
  simp only [points,List.length_append,List.length_map,List.length_range] at short
  have hq : q ≤ 4 := by omega
  have hm : b.ideals ≤ 16 := by cases b <;> simp_all [Cap.size,Cap.ideals] <;> omega
  have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp shape_census q
      (List.mem_range.mpr (by omega))) _ (trace_mem v (le_refl _))) _ (cap_mem v hf hq hm)
  have r := read_trace v (le_refl q)
  have fits : b.Fits (wallsOf (S.trace q)) q := by simpa only [Cap.Fits,r.1,r.2] using hf
  have good : check (diagram (S.trace q) b) = true := (check_correct _).mpr balance
  have hs : ¬4 < (points (S.trace q) b).length := by simpa [points] using (not_lt.mpr short)
  simpa [hs,fits,good] using h

end YiboGaoWeylConvexBalance
