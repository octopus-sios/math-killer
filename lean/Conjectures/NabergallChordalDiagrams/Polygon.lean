module

public import Conjectures.NabergallChordalDiagrams.Separator
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# A good polygon diagonal

Only intersector chords matter at a diagonal. A separator clique isolates
a connected component. Every nonneighbor outside the component has both
ends in the same cyclic gap of its occupied sectors. The gap containing a
second intersector chord determines a diagonal with at least two sectors
on each side. Sector zero is distinguished: the diagonal is always
reported as the nonwrapping block on the side that omits sector zero.
-/

namespace NabergallChordalDiagrams
namespace Polygon

structure Diagonal (d : ℕ) where
  s : ℕ
  e : ℕ
  pos : 0 < s
  span : s+2 ≤ e
  bound : e ≤ d
  other : e+2 ≤ s+d

def Diagonal.In {d} (I : Diagonal d) (p : ℕ) := I.s ≤ p ∧ p < I.e

private def OneSide (S : Finset ℕ) (l r : ℕ) :=
  (∀ p ∈ S, l < p ∧ p < r) ∨ (∀ p ∈ S, p < l ∨ r < p)

/-- A linear description of a gap on the sector circle. If the chosen
gap wraps around zero, its complementary closed hull is used instead. -/
private theorem find_gap {d : ℕ} (S : Finset ℕ) (bound : ∀ p ∈ S, p < d)
    {a₁ a₂ b₁ b₂ : ℕ} (a₁s : a₁ ∈ S) (a₂s : a₂ ∈ S) (ha : a₁<a₂)
    (hb : b₁<b₂) (hb₂ : b₂<d) (side : OneSide S b₁ b₂) :
    ∃ I : Diagonal d,
      (∀ p ∈ S, ∀ q ∈ S, I.In p ↔ I.In q) ∧
      ∀ l r, l<r → r<d → OneSide S l r → (I.In l ↔ I.In r) := by
  have ne : S.Nonempty := ⟨_,a₁s⟩
  let m := S.min' ne
  let M := S.max' ne
  have sm : m ∈ S := S.min'_mem ne
  have sM : M ∈ S := S.max'_mem ne
  have bounds (p) (hp : p ∈ S) : m ≤ p ∧ p ≤ M := ⟨S.min'_le _ hp,S.le_max' _ hp⟩
  have mm : m<M := by have := bounds _ a₁s; have := bounds _ a₂s; omega
  have Md := bound _ sM
  have hull (l r) (h : l<r) (s : OneSide S l r) :
      (m≤l ∧ l≤M) ↔ (m≤r ∧ r≤M) := by
    rcases s with t|t <;> have := t _ sm <;> have := t _ sM <;> omega
  by_cases bh : m≤b₁ ∧ b₁≤M
  · have out : ∀ p ∈ S, p < b₁ ∨ b₂ < p := side.resolve_left (by intro h; have := h _ sm; omega)
    have f₁ := out _ sm
    have f₂ := out _ sM
    have bh₂ := (hull _ _ hb side).mp bh
    let B := S.filter (· < b₁)
    let C := S.filter (b₂ < ·)
    have bn : B.Nonempty := ⟨m,Finset.mem_filter.mpr ⟨sm,by omega⟩⟩
    have cn : C.Nonempty := ⟨M,Finset.mem_filter.mpr ⟨sM,by omega⟩⟩
    let u := B.max' bn
    let v := C.min' cn
    have us : u ∈ S ∧ u < b₁ := Finset.mem_filter.mp (B.max'_mem bn)
    have vs : v ∈ S ∧ b₂ < v := Finset.mem_filter.mp (C.min'_mem cn)
    have vu := bound _ vs.1
    have gap (p) (hp : p ∈ S) : p≤u ∨ v≤p := by
      rcases out p hp with h|h
      · exact .inl (B.le_max' p (Finset.mem_filter.mpr ⟨hp,h⟩))
      · exact .inr (C.min'_le p (Finset.mem_filter.mpr ⟨hp,h⟩))
    let I : Diagonal d := ⟨u+1,v, by omega, by omega, by omega, by omega⟩
    refine ⟨I,?_,?_⟩
    · intro p hp q hq
      have := gap p hp; have := gap q hq
      change (u+1≤p ∧ p<v) ↔ (u+1≤q ∧ q<v); omega
    · intro l r h _ sd
      change (u+1≤l ∧ l<v) ↔ (u+1≤r ∧ r<v)
      rcases sd with t|t <;> have := t _ us.1 <;> have := t _ vs.1 <;> omega
  · have bh₂ := (hull _ _ hb side).not.mp bh
    by_cases hm : m=0
    · let I : Diagonal d := ⟨M+1,d,by omega,by omega,le_rfl,by omega⟩
      refine ⟨I,?_,?_⟩
      · intro p hp q hq
        have := bounds p hp; have := bounds q hq
        change (M+1≤p ∧ p<d) ↔ (M+1≤q ∧ q<d); omega
      · intro l r h rd sd
        have := hull l r h sd
        change (M+1≤l ∧ l<d) ↔ (M+1≤r ∧ r<d); omega
    · let I : Diagonal d := ⟨m,M+1,by omega,by omega,by omega,by omega⟩
      refine ⟨I,?_,?_⟩
      · intro p hp q hq
        have := bounds p hp; have := bounds q hq
        change (m≤p ∧ p<M+1) ↔ (m≤q ∧ q<M+1); omega
      · intro l r h _ sd
        have := hull l r h sd
        change (m≤l ∧ l<M+1) ↔ (m≤r ∧ r<M+1); omega

/-- The order information retained when consecutive endpoints are grouped
into sectors. Strictly alternating sectors force an edge; an actual
crossing can lose strictness but not alternation. -/
structure Sectors {V : Type*} (G : SimpleGraph V) (d : ℕ) where
  lo : V → ℕ
  hi : V → ℕ
  le : ∀ x, lo x ≤ hi x
  bound : ∀ x, hi x < d
  forces : ∀ x y, Cross (lo x) (hi x) (lo y) (hi y) → G.Adj x y
  weak : ∀ x y, G.Adj x y → (lo x ≤ lo y ∧ lo y ≤ hi x ∧ hi x ≤ hi y) ∨
      (lo y ≤ lo x ∧ lo x ≤ hi y ∧ hi y ≤ hi x)
  sector : ∀ s x y, lo x < hi x → lo y < hi y → x ≠ y →
    (lo x=s ∨ hi x=s) → (lo y=s ∨ hi y=s) → G.Adj x y

namespace Sectors
variable {d : ℕ} {V : Type*} {G : SimpleGraph V} (T : Sectors G d)

def Good (I : Diagonal d) := ∀ x y, x≠y →
  ¬(I.In (T.lo x) ↔ I.In (T.hi x)) → ¬(I.In (T.lo y) ↔ I.In (T.hi y)) → G.Adj x y

private abbrev E := {x : V // T.lo x < T.hi x}
private abbrev H := G.induce {x | T.lo x < T.hi x}

private noncomputable def occupied (U : Set T.E) := (Finset.range d).filter fun p =>
  @decide (∃ x ∈ U, T.lo x.val = p ∨ T.hi x.val = p) (Classical.propDecidable _)

private theorem mem_occupied {U : Set T.E} {p} :
    p ∈ T.occupied U ↔ ∃ x ∈ U, T.lo x.val=p ∨ T.hi x.val=p := by
  classical
  simp only [occupied, Finset.mem_filter, Finset.mem_range, decide_eq_true_eq]
  refine and_iff_right_iff_imp.mpr ?_
  rintro ⟨x,_,e|e⟩
  · exact e ▸ lt_of_le_of_lt (T.le _) (T.bound _)
  · exact e ▸ T.bound _

/-- The endpoints of a connected set of strands nonadjacent to `b`
are all strictly on one side of `b`. In particular, this holds for
every other component left after deleting the separator. -/
private theorem component_side {U : Set T.E} {a b : T.E} (ha : a ∈ U)
    (conn : (T.H.induce U).Connected) (bo : b ∉ U)
    (non : ∀ x ∈ U, ¬ T.H.Adj x b) :
    OneSide (T.occupied U) (T.lo b.val) (T.hi b.val) := by
  let inside (p : ℕ) := T.lo b.val < p ∧ p < T.hi b.val
  let outside (p : ℕ) := p < T.lo b.val ∨ T.hi b.val < p
  have whereis (x : T.E) (hx : x ∈ U) :
      (inside (T.lo x.val) ∧ inside (T.hi x.val)) ∨
      (outside (T.lo x.val) ∧ outside (T.hi x.val)) := by
    have diff : x.val ≠ b.val := fun e => bo ((Subtype.ext e : x=b) ▸ hx)
    have nz := non x hx
    have share (p) (h : T.lo x.val=p ∨ T.hi x.val=p) (h' : T.lo b.val=p ∨ T.hi b.val=p) :
        False := nz (T.sector p _ _ x.property b.property diff h h')
    have c₁ : T.lo x.val ≠ T.lo b.val := fun e => share _ (.inl e) (.inl rfl)
    have c₂ : T.lo x.val ≠ T.hi b.val := fun e => share _ (.inl e) (.inr rfl)
    have c₃ : T.hi x.val ≠ T.lo b.val := fun e => share _ (.inr e) (.inl rfl)
    have c₄ : T.hi x.val ≠ T.hi b.val := fun e => share _ (.inr e) (.inr rfl)
    have no : ¬ Cross (T.lo x.val) (T.hi x.val) (T.lo b.val) (T.hi b.val) := fun h => nz (T.forces _ _ h)
    have := x.property; have := b.property
    unfold Cross at no; dsimp [inside,outside]; omega
  have equiv (x y : U) (h : (T.H.induce U).Adj x y) :
      inside (T.lo x.val.val) ↔ inside (T.lo y.val.val) := by
    have hx := whereis x.val x.property
    have hy := whereis y.val y.property
    have hb := b.property
    have w := T.weak x.val.val y.val.val h
    dsimp [inside,outside] at hx hy ⊢; omega
  by_cases test : inside (T.lo a.val)
  · left
    intro p hp
    obtain ⟨x,hx,h|h⟩ := (T.mem_occupied).mp hp <;>
      have hw := along_reachable (P := fun z : U => inside (T.lo z.val.val))
        (fun i j hi e => (equiv i j e).mp hi) (conn ⟨a,ha⟩ ⟨x,hx⟩) test
    · exact h ▸ hw
    · have hh := whereis x hx; dsimp [inside,outside] at hw hh; rw [← h]; omega
  · right
    intro p hp
    obtain ⟨x,hx,h|h⟩ := (T.mem_occupied).mp hp <;>
      have hw := along_reachable (P := fun z : U => ¬inside (T.lo z.val.val))
        (fun i j hi e => (equiv i j e).not.mp hi) (conn ⟨a,ha⟩ ⟨x,hx⟩) test <;>
      have hh := whereis x hx <;> dsimp [inside,outside] at hw hh <;> rw [← h] <;> omega

theorem exists_good_diagonal (hd : 4 ≤ d) (ch : Chordal G) : ∃ I : Diagonal d, T.Good I := by
  classical
  by_cases complete : ∀ x y : T.E, x≠y → T.H.Adj x y
  · let I : Diagonal d := ⟨1,3,by decide,by decide,by omega,by omega⟩
    refine ⟨I,fun x y ne hx hy => ?_⟩
    have inter (z) (h : ¬(I.In (T.lo z) ↔ I.In (T.hi z))) : T.lo z < T.hi z :=
      lt_of_le_of_ne (T.le z) (fun e => h (e ▸ Iff.rfl))
    exact complete ⟨x,inter x hx⟩ ⟨y,inter y hy⟩ (fun h => ne (congrArg Subtype.val h))
  · push Not at complete
    obtain ⟨a,b,ne,non⟩ := complete
    have ch' : Chordal T.H := ch.of_induced Subtype.val Subtype.val_injective (fun _ _ => Iff.rfl)
    obtain ⟨U,ha,conn,bo,nb,_,cl⟩ := Separation.clique_separator ch' ne non
    have occL (x : T.E) (hx : x∈U) : T.lo x.val ∈ T.occupied U :=
      T.mem_occupied.mpr ⟨x,hx,.inl rfl⟩
    have occH (x : T.E) (hx : x∈U) : T.hi x.val ∈ T.occupied U :=
      T.mem_occupied.mpr ⟨x,hx,.inr rfl⟩
    obtain ⟨I,same,stay⟩ := find_gap (T.occupied U) (fun _ h => Finset.mem_range.mp (Finset.mem_filter.mp h).1)
      (occL a ha) (occH a ha) a.property b.property (T.bound b.val) (T.component_side ha conn bo nb)
    have fringe (x : T.E) (hx : ¬(I.In (T.lo x.val) ↔ I.In (T.hi x.val))) : Separation.Fringe T.H U x := by
      have xo : x∉U := fun h => hx (same _ (occL x h) _ (occH x h))
      refine ⟨xo,?_⟩
      by_contra! h
      exact hx (stay _ _ x.property (T.bound _) (T.component_side ha conn xo h))
    refine ⟨I,fun x y e hx hy => ?_⟩
    have inter (z) (h : ¬(I.In (T.lo z) ↔ I.In (T.hi z))) : T.lo z < T.hi z :=
      lt_of_le_of_ne (T.le z) (fun q => h (q ▸ Iff.rfl))
    exact cl ⟨x,inter x hx⟩ ⟨y,inter y hy⟩ (fringe _ hx) (fringe _ hy)
      (fun eq => e (congrArg Subtype.val eq))

end Sectors
end Polygon
end NabergallChordalDiagrams
