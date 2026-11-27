module

public import Conjectures.NabergallChordalDiagrams.Assembly
public import Conjectures.NabergallChordalDiagrams.Triangulation

@[expose] public section

/-!
# Earliest cuts

At a specified cut, every spanning internal pair must contain every
singleton and be contained in no other internal pair. These two local
conditions are exactly the central clique test. This equivalent version
also applies when we move the cut to an earlier gap.
-/

namespace NabergallChordalDiagrams

variable {N L R t : ℕ}

def Outer (F : Fragment N) (b : Fin N) :=
  (∀ s, F.mate s=s → F.mate b < s ∧ s < b) ∧
  (∀ d, ¬(F.mate d < F.mate b ∧ b < d))

theorem admissible_iff_outer (F : Fragment N) (g : ℕ) :
    Admissible F g ↔ ∀ b : Fin N, (F.mate b).val < g → g ≤ b.val → Outer F b := by
  constructor
  · intro h b hb eb
    let c : F.Chord := ⟨b, by change _ ≤ b.val; omega⟩
    refine ⟨link_contains_singleton F h c hb eb,?_⟩
    rintro d ⟨hd,bd⟩
    let e : F.Chord := ⟨d, (hd.trans_le (c.property.trans bd.le)).le⟩
    have ds : (F.mate d).val < g ∧ g ≤ d.val := ⟨lt_trans hd hb,eb.trans bd.le⟩
    exact (not_lt_of_ge bd.le) (links_same_order F h e c ds ⟨hb,eb⟩ hd)
  · intro test c hc e he ne
    have crossFixed (u v : F.Chord) (hu : (F.mate u.val).val < g ∧ g ≤ u.val.val)
        (hv : F.mate v.val = v.val) : F.graph.Adj u v := by
      have hn : F.mate u.val ≠ u.val := by intro eq; rw [eq] at hu; omega
      have h := F.adj_internal_at u hn v.val
      rw [Fragment.chordAt_right,ite_eq_left hv] at h
      exact h.mpr ((test _ hu.1 hu.2).1 _ hv)
    rcases hc with hc|hc <;> rcases he with he|he
    · exact (F.adj_fixed _ _ hc he).mpr ne
    · exact (crossFixed _ _ he hc).symm
    · exact crossFixed _ _ hc he
    · have eqr : c.val.val ≠ e.val.val := fun h => ne (Subtype.ext (Fin.ext h))
      have eql : (F.mate c.val).val ≠ (F.mate e.val).val := by
        intro h
        exact ne (Subtype.ext (F.property.injective (Fin.ext h)))
      have cne : F.mate c.val ≠ c.val := by intro h; rw [h] at hc; omega
      have ene : F.mate e.val ≠ e.val := by intro h; rw [h] at he; omega
      have nc := (test _ hc.1 hc.2).2 e.val
      have nd := (test _ he.1 he.2).2 c.val
      change Cross (F.start c.val) (N+c.val.val) (F.start e.val) (N+e.val.val)
      simp only [Fragment.start,ite_eq_right cne,ite_eq_right ene,Cross,Nat.add_lt_add_iff_left]
      simp only [Fin.lt_def] at nc nd
      omega

/-- Both sides of an unspanned gap contain an original singleton. -/
theorem singletons_at_free_gap (F : Fragment N) (hv : F.Valid) (hk : 0 < F.weight)
    {q} (hp : 0<q) (hq : q<N) (un : ¬F.Spanned q) :
    (∃ s, F.mate s=s ∧ s.val<q) ∧ (∃ s, F.mate s=s ∧ q≤s.val) := by
  have lock (x : Fin N) : (F.mate x).val<q ↔ x.val<q := by
    constructor
    · intro a; by_contra! b; exact un ⟨x,a,b⟩
    · intro a; by_contra! b; exact un ⟨F.mate x, by simpa using a,b⟩
  let W : Window N q := ⟨0,by omega⟩
  let Z : Window N (N-q) := ⟨q,by omega⟩
  obtain ⟨c,hc⟩ := W.boundary_exists F hp hv.1 hk
  obtain ⟨e,he⟩ := Z.boundary_exists F (by omega) hv.1 hk
  have l := lock c.val
  have r := lock e.val
  have c₁ := hc.1; have c₂ := hc.2
  have e₁ := he.1; have e₂ := he.2
  have := c.val.isLt; have := e.val.isLt
  have := (F.mate e.val).isLt
  simp only [Window.Hits, Window.Internal, Window.Contains, W, Z, zero_add, Nat.zero_le, true_and,
    Fin.ext_iff, ne_eq] at c₁ c₂ e₁ e₂
  refine ⟨⟨c.val,Fin.ext (by omega),by omega⟩, ⟨e.val,Fin.ext (by omega),by omega⟩⟩

def Earliest (F : Fragment N) (g : ℕ) := Admissible F g ∧
  ∀ q, 0 < q → q < g → ¬ Admissible F q

def FirstFree (F : Fragment N) (g : ℕ) := ¬F.Spanned g ∧
  ∀ q, 0 < q → q < g → F.Spanned q

theorem admissible_of_free (F : Fragment N) {g} (h : ¬F.Spanned g) : Admissible F g :=
  (admissible_iff_outer F g).mpr fun b hb eb => (h ⟨b,hb,eb⟩).elim

theorem exists_firstFree {F : Fragment N} (nr : ¬F.Irreducible) :
    ∃ g, 0<g ∧ g<N ∧ FirstFree F g := by
  classical
  unfold Fragment.Irreducible at nr
  push Not at nr
  let g := Nat.find nr
  obtain ⟨gp,gl,free⟩ := Nat.find_spec nr
  exact ⟨g,gp,gl,free,fun q hq qg => Classical.byContradiction fun h =>
    Nat.find_min nr qg ⟨hq,by omega,h⟩⟩

theorem exists_earliest {F : Fragment N} (hv : F.Valid) (hn : 2≤N) :
    ∃ g, 0<g ∧ g<N ∧ Earliest F g := by
  classical
  have ex := exists_admissible F hv.2 hn
  obtain ⟨gp,gl,adm⟩ := Nat.find_spec ex
  exact ⟨Nat.find ex,gp,gl,adm,fun q hq qg h => Nat.find_min ex qg ⟨hq,by omega,h⟩⟩

namespace LinkPlan
variable {A : Fragment L} {B : Fragment R} (P : LinkPlan A B t)

theorem split_spanned : P.glue.Spanned L ↔ 0<t := by
  constructor
  · rintro ⟨b,hl,hr⟩
    let c : P.glue.Chord := ⟨b,by change _ ≤ b.val; omega⟩
    obtain ⟨i,_⟩ := (P.spanning_iff c).mp ⟨hl,hr⟩
    exact Nat.zero_lt_of_lt i.isLt
  · intro h; let i : Fin t := ⟨0,h⟩
    have hs := (P.spanning_iff (P.linkVertex i)).mpr ⟨i,rfl⟩
    exact ⟨_,hs⟩

theorem irreducible_iff (hv : P.glue.Valid) (hk : 0<P.glue.weight) (hl : 0<L) (hr : 0<R) :
    P.glue.Irreducible ↔ 0<t := by
  refine ⟨fun h => P.split_spanned.mp (h L hl (by omega)), ?_⟩
  intro pos q qp qlt
  by_contra! h
  obtain ⟨⟨a,ha,aq⟩,⟨b,hb,bq⟩⟩ := singletons_at_free_gap _ hv hk qp qlt h
  obtain ⟨c,hc,ec⟩ := P.split_spanned.mpr pos
  have out := ((admissible_iff_outer _ L).mp P.admissible c hc ec).1
  have x := out _ ha; have y := out _ hb
  exact h ⟨c, lt_trans x.1 aq,le_trans bq y.2.le⟩

theorem internal_mate {x : Fin L} (h : A.mate x ≠ x) :
    P.glue.mate (x.castAdd R) = (A.mate x).castAdd R := by
  rw [glue_left, P.mateL_rest (fun ⟨i,e⟩ => h (e ▸ P.fl i))]

private theorem left_piece {b : Fin (L+R)} (hb : b.val < L) (hm : (P.glue.mate b).val < L) :
    ∃ x : Fin L, b=x.castAdd R ∧ P.glue.mate b = (A.mate x).castAdd R := by
  let x : Fin L := ⟨b.val,hb⟩
  have e : b = x.castAdd R := Fin.ext rfl
  refine ⟨x,e,?_⟩
  rw [e, glue_left] at hm ⊢
  apply P.mateL_rest
  rintro ⟨i,hi⟩
  rw [← hi, mateL_link] at hm
  change L+_ < L at hm; omega

theorem lift_spanned {q} (h : A.Spanned q) : P.glue.Spanned q := by
  obtain ⟨x,a,b⟩ := h
  have ne : A.mate x ≠ x := by intro e; rw [e] at a; omega
  exact ⟨x.castAdd R,by simpa only [P.internal_mate ne, Fin.val_castAdd] using a,b⟩

theorem earlier_spanned_zero (ht : t=0) {q} (hq : q<L) : P.glue.Spanned q ↔ A.Spanned q := by
  refine ⟨?_,fun h => P.lift_spanned h⟩
  rintro ⟨b,hm,hb⟩
  have eb : b.val < L := by
    by_contra! h
    exact (by omega : ¬0<t) (P.split_spanned.mp ⟨b,by omega,h⟩)
  obtain ⟨x,e,hx⟩ := P.left_piece eb (lt_trans hm hq)
  exact ⟨x,by simpa only [hx,Fin.val_castAdd] using hm,by simpa only [e,Fin.val_castAdd] using hb⟩

theorem firstFree_iff : FirstFree P.glue L ↔ t=0 ∧ A.Irreducible := by
  constructor
  · rintro ⟨f,h⟩
    have z : t=0 := Nat.eq_zero_of_not_pos (P.split_spanned.not.mp f)
    exact ⟨z,fun q qp ql => (P.earlier_spanned_zero z ql).mp (h q qp ql)⟩
  · rintro ⟨r,h⟩
    exact ⟨P.split_spanned.not.mpr (by omega),fun q qp ql => P.lift_spanned (h q qp ql)⟩

private theorem lift_free_cut {q} (ql : q<L) (f : ¬A.Spanned q) : Admissible P.glue q := by
  apply (admissible_iff_outer _ _).mpr
  intro b hm hb
  by_cases h : L ≤ b.val
  · exact (admissible_iff_outer _ _).mp P.admissible b (by omega) h
  · obtain ⟨x,e,hx⟩ := P.left_piece (Nat.lt_of_not_ge h) (lt_trans hm ql)
    exact (f ⟨x,by simpa only [hx,Fin.val_castAdd] using hm,by simpa only [e,Fin.val_castAdd] using hb⟩).elim

private theorem right_unused : t<B.weight ↔ ∃ y, B.mate y=y ∧ y ∉ Set.range P.right := by
  classical
  let S := Finset.univ.image P.right
  have mem (x) : x∈S ↔ x∈Set.range P.right := by simp [S, Set.mem_range]
  have sub : S ⊆ B.singletons := by
    intro x hx; obtain ⟨i,rfl⟩ := (mem x).mp hx; exact (B.mem_singletons _).mpr (P.fr i)
  have eq : S.card=t := by simp [S, Finset.card_image_of_injective _ P.mr.injective]
  constructor
  · intro h
    have ns : ¬B.singletons ⊆ S := by
      intro s; have := Finset.card_le_card s; change t<B.singletons.card at h; omega
    obtain ⟨y,hy,ny⟩ := Finset.not_subset.mp ns
    exact ⟨y,(B.mem_singletons _).mp hy,(mem y).not.mp ny⟩
  · rintro ⟨y,hy,ny⟩
    have ss : S ⊂ B.singletons := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun e =>
      ny ((mem y).mp (e.symm ▸ (B.mem_singletons _).mpr hy))⟩
    simpa only [← eq,Fragment.weight] using Finset.card_lt_card ss

/-- If no right singleton goes to the exterior, any admissible cut of the
left child is also admissible in the parent. A left-internal spanning pair
contains all left singletons, including the openings of all the links. -/
private theorem lift_cut_saturated (sat : ¬t<B.weight) {q} (ql : q<L) (cut : Admissible A q) :
    Admissible P.glue q := by
  apply (admissible_iff_outer _ _).mpr
  intro b hm hb
  by_cases eb : L ≤ b.val
  · exact (admissible_iff_outer _ _).mp P.admissible b (by omega) eb
  obtain ⟨x,rfl,em⟩ := P.left_piece (Nat.lt_of_not_ge eb) (lt_trans hm ql)
  rw [em] at hm
  have out := (admissible_iff_outer _ _).mp cut x hm hb
  constructor
  · intro s
    refine Fin.addCases (fun y hy => ?_) (fun z hz => ?_) s
    · obtain ⟨fy,_⟩ := (P.fixed_left_iff y).mp hy
      rw [em]; exact out.1 y fy
    · exact (sat (P.right_unused.mpr ⟨z,(P.fixed_right_iff z).mp hz⟩)).elim
  · rintro d ⟨nd,xd⟩
    rw [em] at nd
    by_cases dl : d.val<L
    · obtain ⟨y,rfl,en⟩ := P.left_piece dl (lt_trans nd (A.mate x).isLt)
      rw [en] at nd
      exact out.2 y ⟨nd,xd⟩
    · let c : P.glue.Chord := ⟨d, by change (P.glue.mate d).val ≤ d.val; change (P.glue.mate d).val < (A.mate x).val at nd; have := (A.mate x).isLt; omega⟩
      obtain ⟨i,eq⟩ := (P.spanning_iff c).mp ⟨lt_trans nd (A.mate x).isLt,Nat.le_of_not_gt dl⟩
      have de : d=(P.right i).natAdd L := (congrArg Subtype.val eq).symm
      rw [de,glue_right,mateR_link] at nd
      exact (not_lt_of_ge (out.1 _ (P.fl i)).1.le) nd

theorem earliest_iff (pos : 0<t) (hk : 0<P.glue.weight) (ha : A.Valid) :
    Earliest P.glue L ↔ A.Irreducible ∧ t<B.weight := by
  constructor
  · rintro ⟨_,early⟩
    refine ⟨fun q hp hq => Classical.byContradiction (fun h => early q hp hq (P.lift_free_cut hq h)),?_⟩
    by_contra! sat
    by_cases h : 2≤L
    · obtain ⟨q,hp,hq,cut⟩ := exists_admissible A ha.2 h
      exact early q hp hq (P.lift_cut_saturated (by omega) hq cut)
    · have := P.le_left; have := P.le_right; have := A.weight_le
      rw [P.weight_glue] at hk; omega
  · rintro ⟨irr,unused⟩
    refine ⟨P.admissible,fun q hp hq cut => ?_⟩
    obtain ⟨x,hm,hb⟩ := irr q hp hq
    obtain ⟨y,hy,ny⟩ := P.right_unused.mp unused
    have ne : A.mate x ≠ x := by intro e; rw [e] at hm; omega
    have hx := (admissible_iff_outer _ _).mp cut (x.castAdd R) (by rw [P.internal_mate ne]; exact hm) hb
    have contra := (hx.1 (y.natAdd L) ((P.fixed_right_iff _).mpr ⟨hy,ny⟩)).2
    change L+y.val < x.val at contra
    have := x.isLt; omega

end LinkPlan
end NabergallChordalDiagrams
