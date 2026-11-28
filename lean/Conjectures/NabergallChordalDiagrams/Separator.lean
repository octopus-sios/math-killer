module

public import Conjectures.NabergallChordalDiagrams.Clique
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

/-!
# The clique separator

Take the component of `a` after deleting `b` and its neighbors. Every
vertex on its external boundary neighbors both the component and `b`,
so this boundary is an inclusion-minimal separator of `a` from `b`.
Two nonadjacent boundary vertices would give a hole: close a shortest
path through the component by the two edges through `b`.
-/

namespace NabergallChordalDiagrams
namespace Separation

open SimpleGraph

private theorem dist_index {V : Type*} {G : SimpleGraph V} {x y : V} (p : G.Walk x y)
    (hp : p.length = G.dist x y) {i : ℕ} (hi : i ≤ p.length) :
    G.dist x (p.getVert i) = i := by
  have h₁ := dist_le (p.take i)
  have h₂ := dist_le (p.drop i)
  have ht := (p.take i).reachable.dist_triangle_left y
  simp only [Walk.take_length, inf_eq_left.mpr hi, Walk.drop_length] at h₁ h₂
  omega

/-- A path in an induced subgraph whose only vertices adjacent to `b`
are its two ends forces those ends to be adjacent. -/
theorem shortcut {V : Type*} {G : SimpleGraph V} (ch : Chordal G)
    {T : Set V} {x y : T} {b : V} (bout : b ∉ T) (hne : x ≠ y)
    (reach : (G.induce T).Reachable x y)
    (nb : ∀ z : T, G.Adj b z.val ↔ z = x ∨ z = y) : G.Adj x.val y.val := by
  classical
  by_contra non
  let H := G.induce T
  obtain ⟨p,hp⟩ := reach.exists_walk_length_eq_dist
  have len : 2 ≤ p.length := hp ▸ reach.one_lt_dist_of_ne_of_not_adj hne non
  have idx := fun (i : ℕ) (hi : i ≤ p.length) => dist_index p hp hi
  have eqv (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) :
      p.getVert i = p.getVert j ↔ i = j := by
    refine ⟨fun e => ?_, fun e => e ▸ rfl⟩
    rw [← idx i hi, ← idx j hj, e]
  have edges (i j : ℕ) (hi : i ≤ p.length) (hj : j ≤ p.length) :
      H.Adj (p.getVert i) (p.getVert j) ↔ i+1=j ∨ j+1=i := by
    constructor
    · intro e
      have dd := e.diff_dist_adj (u := x)
      change (G.induce T).dist x _ = _ ∨ _ at dd
      rw [idx _ hi, idx _ hj] at dd
      have ne : i ≠ j := fun q => e.ne (q ▸ rfl)
      omega
    · rintro (rfl | q)
      · exact p.adj_getVert_succ (by omega)
      · rw [← q]; exact (p.adj_getVert_succ (by omega)).symm
  have atEnds (i) (hi : i ≤ p.length) :
      G.Adj b (p.getVert i).val ↔ i=0 ∨ i=p.length := by
    rw [nb]
    have e₁ := eqv i 0 hi (Nat.zero_le _)
    have e₂ := eqv i p.length hi le_rfl
    simpa only [Walk.getVert_zero, Walk.getVert_length] using or_congr e₁ e₂
  let f (i : Fin (p.length+2)) := if i.val=0 then b else (p.getVert (i.val-1)).val
  apply ch _ (by omega) f
  · intro i j h
    apply Fin.ext
    have hi := i.isLt; have hj := j.isLt
    by_cases a : i.val=0 <;> by_cases d : j.val=0
    · omega
    · simp only [f,a,d,ite_true,ite_false] at h
      exact (bout (h.symm ▸ (p.getVert _).property)).elim
    · simp only [f,a,d,ite_true,ite_false] at h
      exact (bout (h ▸ (p.getVert _).property)).elim
    · simp only [f,a,d,ite_false] at h
      have := (eqv (i.val-1) (j.val-1) (by omega) (by omega)).mp (Subtype.ext h)
      omega
  · intro i j
    have hi := i.isLt; have hj := j.isLt
    rw [cyclicNeighbor_iff]
    by_cases a : i.val=0 <;> by_cases d : j.val=0
    · simp only [f,a,d,ite_true,G.loopless.irrefl,and_true,false_iff]; omega
    · simp only [f,a,d,ite_true,ite_false]
      rw [atEnds _ (by omega)]; simp only [and_true, and_false, false_or]; omega
    · simp only [f,a,d,ite_true,ite_false]
      rw [G.adj_comm, atEnds _ (by omega)]; simp only [and_true, and_false, or_false]; omega
    · simp only [f,a,d,ite_false]
      rw [← SimpleGraph.induce_adj (s := T) (u := p.getVert _) (v := p.getVert _),
        edges _ _ (by omega) (by omega)]
      simp only [and_false, or_false]; omega

def Fringe {V : Type*} (G : SimpleGraph V) (U : Set V) (x : V) :=
  x ∉ U ∧ ∃ w ∈ U, G.Adj w x

theorem clique_separator {V : Type*} {G : SimpleGraph V} (ch : Chordal G)
    {a b : V} (ne : a ≠ b) (non : ¬G.Adj a b) :
    ∃ U : Set V, a ∈ U ∧ (G.induce U).Connected ∧ b ∉ U ∧
      (∀ u ∈ U, ¬G.Adj u b) ∧ (∀ x, Fringe G U x → G.Adj x b) ∧
      ∀ x y, Fringe G U x → Fringe G U y → x ≠ y → G.Adj x y := by
  classical
  let M : Set V := {x | x ≠ b ∧ ¬ G.Adj x b}
  let a' : M := ⟨a,ne,non⟩
  let C := (G.induce M).connectedComponentMk a'
  let U : Set V := Subtype.val '' C.supp
  have am : a ∈ U := ⟨a',rfl,rfl⟩
  have sub : U ⊆ M := fun _ ⟨x,_,e⟩ => e ▸ x.property
  let inc : (G.induce M).induce C.supp →g G.induce U :=
    ⟨fun x => ⟨x.val.val,⟨x.val,x.property,rfl⟩⟩, fun e => e⟩
  have surj : Function.Surjective inc := by
    rintro ⟨x,z,hz,rfl⟩
    exact ⟨⟨z,hz⟩,rfl⟩
  have conn : (G.induce U).Connected := C.connected_toSimpleGraph.map inc surj
  have bd (x : V) (h : Fringe G U x) : G.Adj x b := by
    obtain ⟨hx,y,hy,e⟩ := h
    by_contra hn
    have xb : x ≠ b := by rintro rfl; exact (sub hy).2 e
    let x' : M := ⟨x,xb,hn⟩
    obtain ⟨z,hz,rfl⟩ := hy
    exact hx ⟨x',C.mem_supp_of_adj_mem_supp hz (show (G.induce M).Adj z x' from e),rfl⟩
  refine ⟨U,am,conn,fun h => (sub h).1 rfl,fun _ h => (sub h).2,bd,?_⟩
  intro x y hx hy hxy
  let T : Set V := {z | z=x ∨ z=y ∨ z ∈ U}
  let x' : T := ⟨x,.inl rfl⟩
  let y' : T := ⟨y,.inr (.inl rfl)⟩
  have bx := bd _ hx; have by' := bd _ hy
  have bout : b ∉ T := by
    rintro (e|e|h)
    · exact bx.ne e.symm
    · exact by'.ne e.symm
    · exact (sub h).1 rfl
  obtain ⟨u,hu,eu⟩ := hx.2
  obtain ⟨v,hv,ev⟩ := hy.2
  let inj : G.induce U →g G.induce T := ⟨fun z => ⟨z.val,.inr (.inr z.property)⟩,fun e => e⟩
  have hmid := (conn ⟨u,hu⟩ ⟨v,hv⟩).map inj
  have reach : (G.induce T).Reachable x' y' :=
    (show (G.induce T).Adj x' (inj ⟨u,hu⟩) from eu.symm).reachable.trans
    (hmid.trans (show (G.induce T).Adj (inj ⟨v,hv⟩) y' from ev).reachable)
  apply shortcut ch bout (fun e : x'=y' => hxy (congrArg Subtype.val e)) reach
  intro z
  constructor
  · intro e
    rcases z.property with h|h|h
    · exact .inl (Subtype.ext h)
    · exact .inr (Subtype.ext h)
    · exact ((sub h).2 e.symm).elim
  · rintro (rfl|rfl)
    · exact bx.symm
    · exact by'.symm

end Separation
end NabergallChordalDiagrams
