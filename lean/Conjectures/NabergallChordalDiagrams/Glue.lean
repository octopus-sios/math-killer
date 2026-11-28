module

public import Conjectures.NabergallChordalDiagrams.Split

@[expose] public section

/-!
# Gluing two intervals at their marked strands

Links are indexed from left to right. Their endpoints use an initial
segment of the singletons of the left word and a final segment of those
of the right word. The choices of endpoint functions carry no multiplicity.
-/

namespace NabergallChordalDiagrams

variable {L R t : ℕ} {A : Fragment L} {B : Fragment R}

structure LinkPlan (A : Fragment L) (B : Fragment R) (t : ℕ) where
  left : Fin t → Fin L
  right : Fin t → Fin R
  ml : StrictMono left
  mr : StrictMono right
  fl : ∀ i, A.mate (left i) = left i
  fr : ∀ i, B.mate (right i) = right i
  initial : ∀ x, A.mate x = x → x ∉ Set.range left → ∀ i, left i < x
  final : ∀ x, B.mate x = x → x ∉ Set.range right → ∀ i, x < right i

private theorem ordered_initial_unique {α : Type*} [LinearOrder α] {fix : α → Prop}
    (f g : Fin t → α) (mf : StrictMono f) (mg : StrictMono g)
    (ff : ∀ i, fix (f i)) (fg : ∀ i, fix (g i))
    (hf : ∀ x, fix x → x ∉ Set.range f → ∀ i, f i < x)
    (hg : ∀ x, fix x → x ∉ Set.range g → ∀ i, g i < x) : f = g := by
  classical
  let S := Finset.univ.image f
  let T := Finset.univ.image g
  have cf : S.card = t := by simp [S, Finset.card_image_of_injective _ mf.injective]
  have cg : T.card = t := by simp [T, Finset.card_image_of_injective _ mg.injective]
  have eq : S = T := by
    by_cases h : S ⊆ T
    · exact Finset.eq_of_subset_of_card_le h (by omega)
    · apply Eq.symm
      apply Finset.eq_of_subset_of_card_le _ (by omega)
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨j,_,rfl⟩
      by_contra! hj
      have hj' : g j ∉ Set.range f := fun ⟨i,hi⟩ => hj (hi ▸ Finset.mem_image_of_mem _ (Finset.mem_univ i))
      obtain ⟨y,hy,hy'⟩ := Finset.not_subset.mp h
      rcases Finset.mem_image.mp hy with ⟨i,_,rfl⟩
      have hi' : f i ∉ Set.range g := fun ⟨j,hj⟩ => hy' (hj ▸ Finset.mem_image_of_mem _ (Finset.mem_univ j))
      exact lt_asymm (hf _ (fg _) hj' i) (hg _ (ff _) hi' j)
  apply (Finset.orderEmbOfFin_unique cf (fun x => Finset.mem_image_of_mem _ (Finset.mem_univ x)) mf).trans
  exact (Finset.orderEmbOfFin_unique cf (fun x => eq ▸ Finset.mem_image_of_mem g (Finset.mem_univ x)) mg).symm

instance : Subsingleton (LinkPlan A B t) where
  allEq P Q := by
    have hl := ordered_initial_unique (fix := fun x => A.mate x = x) _ _ P.ml Q.ml P.fl Q.fl P.initial Q.initial
    have hr := ordered_initial_unique (α := (Fin R)ᵒᵈ) (fix := fun x => B.mate x = x)
      (fun i => P.right (Fin.rev i)) (fun i => Q.right (Fin.rev i))
      (fun _ _ h => P.mr (Fin.rev_lt_rev.mpr h)) (fun _ _ h => Q.mr (Fin.rev_lt_rev.mpr h))
      (fun i => P.fr _) (fun i => Q.fr _)
      (fun x hx hn i => P.final x hx (fun ⟨j,e⟩ => hn ⟨Fin.rev j, (show P.right j.rev.rev = (x : Fin R) from by simpa only [Fin.rev_rev] using e)⟩) _)
      (fun x hx hn i => Q.final x hx (fun ⟨j,e⟩ => hn ⟨Fin.rev j, (show Q.right j.rev.rev = (x : Fin R) from by simpa only [Fin.rev_rev] using e)⟩) _)
    have hr' : P.right = Q.right := funext fun i => by simpa using congrFun hr i.rev
    cases P; cases Q; cases hl; cases hr'; rfl

private def tip (A : Fragment L) : Fin A.weight ↪o Fin L := A.singletons.orderEmbOfFin rfl

private theorem tip_fixed (A : Fragment L) (i : Fin A.weight) : A.mate (tip A i) = tip A i :=
  (A.mem_singletons _).mp (A.singletons.orderEmbOfFin_mem rfl i)

private theorem exists_tip (A : Fragment L) {x} (h : A.mate x=x) : ∃ i, tip A i=x := by
  have hx := (A.mem_singletons x).mpr h
  let e := A.singletons.orderIsoOfFin (k := A.weight) rfl
  exact ⟨e.symm ⟨x,hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x,hx⟩)⟩

/-- Pair the first `t` left singletons with the last `t` right singletons in order. -/
@[no_expose] def LinkPlan.canonical (A : Fragment L) (B : Fragment R) (t : ℕ)
    (hl : t ≤ A.weight) (hr : t ≤ B.weight) : LinkPlan A B t where
  left i := tip A ⟨i.val, lt_of_lt_of_le i.isLt hl⟩
  right i := tip B ⟨B.weight-t+i.val, by have := i.isLt; omega⟩
  ml := fun _ _ h => (tip A).strictMono h
  mr := fun i j h => (tip B).strictMono (by change _+i.val < _+j.val; exact Nat.add_lt_add_left h _)
  fl _ := tip_fixed _ _
  fr _ := tip_fixed _ _
  initial x hx hn i := by
    obtain ⟨j,rfl⟩ := exists_tip A hx
    apply (tip A).strictMono
    change i.val < j.val
    by_contra! h
    have hj : j.val < t := lt_of_le_of_lt h i.isLt
    exact hn ⟨⟨j.val,hj⟩, rfl⟩
  final x hx hn i := by
    obtain ⟨j,rfl⟩ := exists_tip B hx
    apply (tip B).strictMono
    change j.val < B.weight-t+i.val
    by_contra! h
    have hj := j.isLt
    let q : Fin t := ⟨j.val-(B.weight-t), by omega⟩
    apply hn
    exact ⟨q, congrArg (tip B) (Fin.ext (by dsimp [q]; omega))⟩

namespace LinkPlan

variable (P : LinkPlan A B t)

noncomputable def mateL (x : Fin L) : Fin (L+R) := by
  classical
  exact if h : x ∈ Set.range P.left then (P.right h.choose).natAdd L else (A.mate x).castAdd R

noncomputable def mateR (y : Fin R) : Fin (L+R) := by
  classical
  exact if h : y ∈ Set.range P.right then (P.left h.choose).castAdd R else (B.mate y).natAdd L

@[simp] theorem mateL_link (i : Fin t) : P.mateL (P.left i) = (P.right i).natAdd L := by
  let h : P.left i ∈ Set.range P.left := ⟨i,rfl⟩
  have e := P.ml.injective h.choose_spec
  simp only [mateL, dite_eq_left h, e]

@[simp] theorem mateR_link (i : Fin t) : P.mateR (P.right i) = (P.left i).castAdd R := by
  let h : P.right i ∈ Set.range P.right := ⟨i,rfl⟩
  have e := P.mr.injective h.choose_spec
  simp only [mateR, dite_eq_left h, e]

theorem mateL_rest {x} (h : x ∉ Set.range P.left) : P.mateL x = (A.mate x).castAdd R := by
  simp [mateL,h]

theorem mateR_rest {x} (h : x ∉ Set.range P.right) : P.mateR x = (B.mate x).natAdd L := by
  simp [mateR,h]

theorem mateL_out {x} (h : x ∉ Set.range P.left) : A.mate x ∉ Set.range P.left := by
  rintro ⟨i,e⟩
  exact h ⟨i, by simpa only [P.fl, Fragment.mate_mate] using congrArg A.mate e⟩

theorem mateR_out {x} (h : x ∉ Set.range P.right) : B.mate x ∉ Set.range P.right := by
  rintro ⟨i,e⟩
  exact h ⟨i, by simpa only [P.fr, Fragment.mate_mate] using congrArg B.mate e⟩

noncomputable def glue : Fragment (L+R) := ⟨Fin.addCases P.mateL P.mateR, by
  intro p
  refine Fin.addCases (fun x => ?_) (fun y => ?_) p
  · by_cases h : x ∈ Set.range P.left
    · rcases h with ⟨i,rfl⟩; simp
    · simp [P.mateL_rest h, P.mateL_rest (P.mateL_out h)]
  · by_cases h : y ∈ Set.range P.right
    · rcases h with ⟨i,rfl⟩; simp
    · simp [P.mateR_rest h, P.mateR_rest (P.mateR_out h)]⟩

@[simp] theorem glue_left (x : Fin L) : P.glue.mate (x.castAdd R) = P.mateL x := by
  simp [glue, Fragment.mate]

@[simp] theorem glue_right (y : Fin R) : P.glue.mate (y.natAdd L) = P.mateR y := by
  simp [glue, Fragment.mate]

end LinkPlan

@[simp] theorem left_pos (x : Fin L) : (leftWindow L R).pos x = x.castAdd R := by
  apply Fin.ext; simp [leftWindow]

@[simp] theorem right_pos (x : Fin R) : (rightWindow L R).pos x = x.natAdd L := rfl

theorem left_contains (p : Fin (L+R)) : (leftWindow L R).Contains p ↔ p.val < L := by
  simp [Window.Contains, leftWindow]

theorem right_contains (p : Fin (L+R)) : (rightWindow L R).Contains p ↔ L ≤ p.val := by
  simp [Window.Contains, rightWindow, p.isLt]

namespace LinkPlan
variable (P : LinkPlan A B t)

@[simp] theorem restrict_left : (leftWindow L R).restrict P.glue = A := by
  apply Fragment.ext_mate
  intro x
  apply (leftWindow L R).pos_injective
  rw [Window.pos_restrict_mate]
  by_cases h : x ∈ Set.range P.left
  · obtain ⟨i,rfl⟩ := h
    simp [left_contains, P.fl]
  · simp [left_contains, P.mateL_rest h]

@[simp] theorem restrict_right : (rightWindow L R).restrict P.glue = B := by
  apply Fragment.ext_mate
  intro x
  apply (rightWindow L R).pos_injective
  rw [Window.pos_restrict_mate]
  by_cases h : x ∈ Set.range P.right
  · obtain ⟨i,rfl⟩ := h
    simp [right_contains, P.fr]
  · simp [right_contains, P.mateR_rest h]

/-- Each strand joining left and right is named by its closing position. -/
def linkVertex (i : Fin t) : P.glue.Chord :=
  ⟨(P.right i).natAdd L, by
    rw [glue_right, mateR_link]
    change (P.left i).val ≤ L+(P.right i).val; have := (P.left i).isLt; omega⟩

theorem spanning_iff (c : P.glue.Chord) :
    ((P.glue.mate c.val).val < L ∧ L ≤ c.val.val) ↔ ∃ i, P.linkVertex i = c := by
  constructor
  · intro ⟨hl,hr⟩
    let y : Fin R := ⟨c.val.val-L, by have := c.val.isLt; omega⟩
    have e : y.natAdd L = c.val := Fin.ext (by change L+(c.val.val-L)=_; omega)
    by_cases h : y ∈ Set.range P.right
    · rcases h with ⟨i,hi⟩
      exact ⟨i, Subtype.ext (by change (P.right i).natAdd L = _; rw [hi,e])⟩
    · rw [← e, glue_right, P.mateR_rest h] at hl
      change L+_ < L at hl; omega
  · rintro ⟨i,rfl⟩
    change (P.glue.mate ((P.right i).natAdd L)).val < L ∧ L ≤ L+(P.right i).val
    rw [glue_right, mateR_link]
    exact ⟨(P.left i).isLt, Nat.le_add_right _ _⟩

private theorem link_link (i j : Fin t) (hne : i ≠ j) :
    P.glue.graph.Adj (P.linkVertex i) (P.linkVertex j) := by
  have help (u v : Fin t) (huv : u < v) :
      P.glue.start (P.linkVertex u).val < P.glue.start (P.linkVertex v).val ∧
      P.glue.start (P.linkVertex v).val < L+R+(P.linkVertex u).val.val ∧
      L+R+(P.linkVertex u).val.val < L+R+(P.linkVertex v).val.val := by
    have el := P.ml huv; have er := P.mr huv
    change (P.left u).val < (P.left v).val at el
    change (P.right u).val < (P.right v).val at er
    have ltU := (P.left u).isLt; have ltV := (P.left v).isLt
    simp only [linkVertex, Fragment.start, glue_right, mateR_link, Fin.ext_iff,
      Fin.val_castAdd, Fin.val_natAdd]
    split <;> split <;> omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact Or.inl (help _ _ h)
  · exact Or.inr (help _ _ h)

theorem fixed_left_iff (x : Fin L) :
    P.glue.mate (x.castAdd R) = x.castAdd R ↔ A.mate x = x ∧ x ∉ Set.range P.left := by
  by_cases h : x ∈ Set.range P.left
  · obtain ⟨i,rfl⟩ := h
    have hs : P.left i ∈ Set.range P.left := ⟨i,rfl⟩
    simp only [glue_left, mateL_link, hs, not_true_eq_false, and_false, iff_false, Fin.ext_iff,
      Fin.val_natAdd, Fin.val_castAdd]
    have := (P.left i).isLt; omega
  · simp [P.mateL_rest h, h]

theorem fixed_right_iff (y : Fin R) :
    P.glue.mate (y.natAdd L) = y.natAdd L ↔ B.mate y = y ∧ y ∉ Set.range P.right := by
  by_cases h : y ∈ Set.range P.right
  · obtain ⟨i,rfl⟩ := h
    have hs : P.right i ∈ Set.range P.right := ⟨i,rfl⟩
    simp only [glue_right, mateR_link, hs, not_true_eq_false, and_false, iff_false, Fin.ext_iff,
      Fin.val_natAdd, Fin.val_castAdd]
    have := (P.left i).isLt; omega
  · simp [P.mateR_rest h, h]

private theorem link_fixed (i : Fin t) (c : P.glue.Chord) (hf : P.glue.mate c.val = c.val) :
    P.glue.graph.Adj (P.linkVertex i) c := by
  have haux (x : Fin (L+R)) (h : P.glue.mate x=x) :
      (P.left i).val < x.val ∧ x.val < L+(P.right i).val := by
    revert h
    refine Fin.addCases (fun a ha => ?_) (fun b hb => ?_) x
    · obtain ⟨fa,hn⟩ := (P.fixed_left_iff _).mp ha
      exact ⟨P.initial a fa hn i, by change a.val < _; have := a.isLt; omega⟩
    · obtain ⟨fb,hn⟩ := (P.fixed_right_iff _).mp hb
      exact ⟨by change _ < L+b.val; have := (P.left i).isLt; omega,
        Nat.add_lt_add_left (P.final b fb hn i) L⟩
  have h := haux _ hf
  have hn : P.glue.mate (P.linkVertex i).val ≠ (P.linkVertex i).val := by
    intro e
    have hh := congrArg Fin.val e
    change (P.glue.mate ((P.right i).natAdd L)).val = L+(P.right i).val at hh
    rw [glue_right, mateR_link] at hh
    change (P.left i).val = _ at hh
    have := (P.left i).isLt; omega
  have hh := P.glue.adj_internal_at (P.linkVertex i) hn c.val
  rw [Fragment.chordAt_right, ite_eq_left hf] at hh
  apply hh.mpr
  simpa only [linkVertex, glue_right, mateR_link, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] using h

theorem admissible : Admissible P.glue L := by
  intro c hc d hd hne
  rcases hc with hc | hc <;> rcases hd with hd | hd
  · exact (P.glue.adj_fixed _ _ hc hd).mpr hne
  · obtain ⟨i,rfl⟩ := (P.spanning_iff _).mp hd
    exact (P.link_fixed _ _ hc).symm
  · obtain ⟨i,rfl⟩ := (P.spanning_iff _).mp hc
    exact P.link_fixed _ _ hd
  · obtain ⟨i,rfl⟩ := (P.spanning_iff _).mp hc
    obtain ⟨j,rfl⟩ := (P.spanning_iff _).mp hd
    exact P.link_link _ _ (fun h => hne (congrArg _ h))

theorem valid (ha : A.Valid) (hb : B.Valid) (i : 0 < A.weight) (j : 0 < B.weight) :
    P.glue.Valid :=
  valid_of_restrictions P.glue P.admissible (by simpa using ha) (by simpa using hb)
    (by simpa using i) (by simpa using j)

end LinkPlan
end NabergallChordalDiagrams
