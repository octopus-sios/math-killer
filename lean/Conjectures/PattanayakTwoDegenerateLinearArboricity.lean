import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin

/-! The sharpness example for the *strong* dense-case bound (not a
counterexample to two linear forests). Edge indices 0,1,2 give the central
triangle, followed by the three triples of petal edges. Degrees and degeneracy
are computed on the finite simple undirected graph itself. -/

namespace PattanayakTwoDegenerateLinearArboricity

abbrev V := Fin 9
abbrev E := Fin 12

def ends (i : E) : V × V :=
  match i.val with
  | 0 => (0,1) | 1 => (1,2) | 2 => (2,0)
  | 3 => (0,3) | 4 => (0,4) | 5 => (3,4)
  | 6 => (1,5) | 7 => (1,6) | 8 => (5,6)
  | 9 => (2,7) | 10 => (2,8) | _ => (7,8)

/-- The adjacency-with-edge-index lists, audited against `ends` below. -/
def nbr (v : V) : List (V × E) :=
  match v.val with
  | 0 => [(1,0),(2,2),(3,3),(4,4)]
  | 1 => [(0,0),(2,1),(5,6),(6,7)]
  | 2 => [(1,1),(0,2),(7,9),(8,10)]
  | 3 => [(0,3),(4,5)] | 4 => [(0,4),(3,5)]
  | 5 => [(1,6),(6,8)] | 6 => [(1,7),(5,8)]
  | 7 => [(2,9),(8,11)] | _ => [(2,10),(7,11)]

theorem adjacency_checked : (∀ v : V, ((nbr v).map Prod.fst).Nodup) ∧
    (∀ v : V, ∀ w : V, ∀ e : E, (w,e) ∈ nbr v ↔ ends e = (v,w) ∨ ends e = (w,v)) ∧
    (∀ e : E, (ends e).1 ≠ (ends e).2) := by decide

def degIn (use : E → Bool) (S : Finset V) (v : V) : Nat :=
  (((nbr v).toFinset).filter fun p => use p.2 = true ∧ p.1 ∈ S).card

/-- Every nonempty induced subgraph has a vertex of degree at most k. -/
def Degenerate (use : E → Bool) (k : Nat) : Prop :=
  ∀ S : Finset V, S.Nonempty → ∃ v ∈ S, degIn use S v ≤ k

private theorem deg_le {f g : E → Bool} {S T : Finset V} (v : V)
    (hf : ∀ e, f e = true → g e = true) (hs : S ⊆ T) :
    degIn f S v ≤ degIn g T v := by
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hm, he, hn⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hm, hf _ he, hs hn⟩

private theorem of_rank (f : E → Bool) (r : V → Nat) (k : Nat)
    (h : ∀ v, degIn f (Finset.univ.filter fun w => r v ≤ r w) v ≤ k) :
    Degenerate f k := by
  intro S hS
  obtain ⟨v, hv, hmin⟩ := S.exists_min_image r hS
  refine ⟨v, hv, (deg_le v (fun _ h' => h') ?_).trans (h v)⟩
  intro w hw
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmin w hw⟩

def colorsAt (c : E → Bool) (v : V) : List Bool := (nbr v).map fun p => c p.2

/-- A finite forest is exactly a 1-degenerate graph. In addition each
color has degree at most two; hence its components are paths. -/
def Linear (c : E → Bool) : Prop :=
  (∀ v b, (colorsAt c v).count b ≤ 2) ∧
    ∀ b, Degenerate (fun e => c e == b) 1

def mono (a b : Bool) : Nat := if a = b then 1 else 0

def defect (c : E → Bool) (v : V) : Nat :=
  match colorsAt c v with
  | [a,b] => mono a b
  | _ => 0

def defects (c : E → Bool) : Nat :=
  ([0,1,2,3,4,5,6,7,8] : List V).map (defect c) |>.sum

def triV (t : Fin 4) : Finset V :=
  match t.val with
  | 0 => {0,1,2} | 1 => {0,3,4} | 2 => {1,5,6} | _ => {2,7,8}

def triE (t : Fin 4) : List E :=
  match t.val with
  | 0 => [0,1,2] | 1 => [3,4,5] | 2 => [6,7,8] | _ => [9,10,11]

private theorem tri_not_constant (c : E → Bool) (hc : Linear c)
    (t : Fin 4) (b : Bool) : ¬ ∀ e ∈ triE t, c e = b := by
  intro h
  have nonempty : ∀ i, (triV i).Nonempty := by decide
  have degree : ∀ i v, v ∈ triV i →
      2 ≤ degIn (fun e => decide (e ∈ triE i)) (triV i) v := by decide
  obtain ⟨v, hv, hv'⟩ := hc.2 b (triV t) (nonempty t)
  have hle := deg_le (f := fun e => decide (e ∈ triE t))
      (g := fun e => c e == b) (S := triV t) (T := triV t) v
      (fun e he => by simpa using h e (of_decide_eq_true he)) (fun _ h' => h')
  exact (by decide : ¬ 2 ≤ 1) ((degree t v hv).trans (hle.trans hv'))

private def Tri (a b c : Bool) := ¬ (a = b ∧ b = c)

private theorem tri_of_list {a b d : E} (c : E → Bool)
    (h : ¬ ∀ e ∈ [a,b,d], c e = c b) : Tri (c a) (c b) (c d) := by
  intro ⟨hab, hbd⟩
  apply h
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl
  · exact hab
  · rfl
  · exact hbd.symm

private theorem petal_table : ∀ a b x y z : Bool,
    (∀ i : Bool, [a,b,x,y].count i ≤ 2) →
    ¬ (x = y ∧ y = z) →
    mono x z + mono y z = (if a = b then 0 else 1) := by decide

private theorem center_table : ∀ a b c : Bool, ¬ (a = b ∧ b = c) →
    (if a = c then 0 else 1) + (if a = b then 0 else 1) +
    (if b = c then 0 else 1) = (2 : Nat) := by decide

theorem every_linear_coloring_has_two_defects (c : E → Bool) (hc : Linear c) :
    defects c = 2 := by
  have t0 := tri_of_list (a := 0) (b := 1) (d := 2) c (tri_not_constant c hc 0 (c 1))
  have t1 := tri_of_list (a := 3) (b := 4) (d := 5) c (tri_not_constant c hc 1 (c 4))
  have t2 := tri_of_list (a := 6) (b := 7) (d := 8) c (tri_not_constant c hc 2 (c 7))
  have t3 := tri_of_list (a := 9) (b := 10) (d := 11) c (tri_not_constant c hc 3 (c 10))
  have ha := petal_table (c 0) (c 2) (c 3) (c 4) (c 5) (hc.1 0) t1
  have hb := petal_table (c 0) (c 1) (c 6) (c 7) (c 8) (hc.1 1) t2
  have hd := petal_table (c 1) (c 2) (c 9) (c 10) (c 11) (hc.1 2) t3
  calc
    defects c =
        (mono (c 3) (c 5) + mono (c 4) (c 5)) +
        (mono (c 6) (c 8) + mono (c 7) (c 8)) +
        (mono (c 9) (c 11) + mono (c 10) (c 11)) := by
      change 0+(0+(0+(mono _ _+(mono _ _+(mono _ _+(mono _ _+(mono _ _+(mono _ _+0)))))))) = _
      simp [Nat.add_assoc]
    _ = 2 := by rw [ha,hb,hd]; exact center_table _ _ _ t0

def sample (e : E) : Bool := decide (e ∈ ([0,1,3,5,8,9,11] : List E))

private def ranks (xs : List Nat) (v : V) : Nat := xs[v.val]!

theorem flower_two_degenerate : Degenerate (fun _ => true) 2 := by
  apply of_rank _ (ranks [6,7,8,0,1,2,3,4,5])
  decide

theorem flower_size_degree : Fintype.card E = 2 * Fintype.card V - 6 ∧
    (∀ v, (nbr v).length ≤ 4) ∧ (nbr 0).length = 4 := by decide

theorem sample_linear : Linear sample := by
  constructor
  · decide
  · intro b
    cases b
    · apply of_rank _ (ranks [2,5,3,0,1,4,6,7,8])
      decide
    · apply of_rank _ (ranks [2,3,4,1,0,5,6,7,8])
      decide

end PattanayakTwoDegenerateLinearArboricity
