import Conjectures.NabergallChordalDiagrams.Glue
import Mathlib.Algebra.BigOperators.Fin

/-! # The admissible split bijection, including its weight statistic -/

namespace NabergallChordalDiagrams

variable {N L R t : ℕ}

theorem link_contains_singleton (F : Fragment N) {g : ℕ} (ha : Admissible F g)
    (c : F.Chord) (hl : (F.mate c.val).val < g) (hr : g ≤ c.val.val)
    (p : Fin N) (hp : F.mate p = p) : F.mate c.val < p ∧ p < c.val := by
  let d : F.Chord := ⟨p,hp.le⟩
  have hc : F.mate c.val ≠ c.val := by
    intro e; rw [e] at hl; omega
  have hd : c ≠ d := by
    rintro rfl; exact hc hp
  have h := ha c (.inr ⟨hl,hr⟩) d (.inl hp) hd
  have hh := (F.adj_internal_at c hc p).mp (by rwa [show F.chordAt p = d from F.chordAt_right d])
  simpa [hp] using hh

theorem links_same_order (F : Fragment N) {g : ℕ} (ha : Admissible F g)
    (c d : F.Chord) (hc : (F.mate c.val).val < g ∧ g ≤ c.val.val)
    (hd : (F.mate d.val).val < g ∧ g ≤ d.val.val) (h : F.mate c.val < F.mate d.val) :
    c.val < d.val := by
  have hn : c ≠ d := fun e => (lt_irrefl _ (e ▸ h))
  have cn : F.mate c.val ≠ c.val := by intro e; rw [e] at hc; omega
  have dn : F.mate d.val ≠ d.val := by intro e; rw [e] at hd; omega
  have adj := ha _ (.inr hc) _ (.inr hd) hn
  change Cross (F.start c.val) (N+c.val.val) (F.start d.val) (N+d.val.val) at adj
  simp only [Fragment.start, ite_eq_right cn, ite_eq_right dn, Cross, Nat.add_lt_add_iff_left] at adj
  change _ < (F.mate d.val).val at h
  change _ < d.val.val
  omega

namespace CutData
variable (F : Fragment (L+R))

def openings : Finset (Fin L) := Finset.univ.filter fun x => L ≤ (F.mate (x.castAdd R)).val
def links := (openings F).card
def opening : Fin (links F) ↪o Fin L := (openings F).orderEmbOfFin rfl

theorem opening_spec (i : Fin (links F)) : L ≤ (F.mate ((opening F i).castAdd R)).val := by
  have h := (openings F).orderEmbOfFin_mem rfl i
  exact (Finset.mem_filter.mp h).2

theorem mem_opening_iff (x : Fin L) :
    x ∈ Set.range (opening F) ↔ L ≤ (F.mate (x.castAdd R)).val := by
  refine ⟨fun ⟨i,e⟩ => e ▸ opening_spec F i, fun h => ?_⟩
  let e := (openings F).orderIsoOfFin (k := links F) rfl
  let u : openings F := ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩⟩
  exact ⟨e.symm u, congrArg Subtype.val (e.apply_symm_apply u)⟩

def closing (i : Fin (links F)) : Fin R :=
  ⟨(F.mate ((opening F i).castAdd R)).val-L, by
    have := (F.mate ((opening F i).castAdd R)).isLt; have := opening_spec F i; omega⟩

theorem mate_opening (i : Fin (links F)) :
    F.mate ((opening F i).castAdd R) = (closing F i).natAdd L := Fin.ext (by
  change _ = L+(_-L); have := opening_spec F i; omega)

theorem mate_closing (i : Fin (links F)) :
    F.mate ((closing F i).natAdd L) = (opening F i).castAdd R := by
  rw [← mate_opening, Fragment.mate_mate]

theorem mem_closing_iff (y : Fin R) : y ∈ Set.range (closing F) ↔ (F.mate (y.natAdd L)).val < L := by
  constructor
  · rintro ⟨i,rfl⟩
    rw [mate_closing]; exact (opening F i).isLt
  · intro h
    let x : Fin L := ⟨(F.mate (y.natAdd L)).val,h⟩
    have e : x.castAdd R = F.mate (y.natAdd L) := Fin.ext rfl
    have em : F.mate (x.castAdd R) = y.natAdd L := by rw [e, Fragment.mate_mate]
    have hx : x ∈ Set.range (opening F) := (mem_opening_iff _ _).mpr (by rw [em]; exact Nat.le_add_right _ _)
    obtain ⟨i,hi⟩ := hx
    have ee := mate_opening F i
    rw [hi,em] at ee
    exact ⟨i, Fin.ext (by have q := congrArg Fin.val ee; change L+_ = L+_ at q; omega)⟩

theorem mate_left_rest (x : Fin L) (h : x ∉ Set.range (opening F)) :
    F.mate (x.castAdd R) = (((leftWindow L R).restrict F).mate x).castAdd R := by
  have h' := (mem_opening_iff F x).not.mp h
  have e := (leftWindow L R).pos_restrict_mate F x
  simpa [left_contains, show (F.mate (x.castAdd R)).val < L by omega] using e.symm

theorem mate_right_rest (x : Fin R) (h : x ∉ Set.range (closing F)) :
    F.mate (x.natAdd L) = (((rightWindow L R).restrict F).mate x).natAdd L := by
  have h' := (mem_closing_iff F x).not.mp h
  have e := (rightWindow L R).pos_restrict_mate F x
  simpa [right_contains, show L ≤ (F.mate (x.natAdd L)).val by omega] using e.symm

def vertex (i : Fin (links F)) : F.Chord :=
  ⟨(closing F i).natAdd L, by rw [mate_closing]; change (opening F i).val ≤ L+_; have := (opening F i).isLt; omega⟩

theorem vertex_spans (i : Fin (links F)) : (F.mate (vertex F i).val).val < L ∧ L ≤ (vertex F i).val.val := by
  change (F.mate ((closing F i).natAdd L)).val < L ∧ L ≤ L+_
  rw [mate_closing]
  exact ⟨(opening F i).isLt,Nat.le_add_right _ _⟩

def plan (ha : Admissible F L) :
    LinkPlan ((leftWindow L R).restrict F) ((rightWindow L R).restrict F) (links F) where
  left := opening F
  right := closing F
  ml := (opening F).strictMono
  mr i j h := by
    have h' : F.mate (vertex F i).val < F.mate (vertex F j).val := by
      simpa only [vertex, mate_closing, Fin.lt_def, Fin.val_castAdd] using (opening F).strictMono h
    have hh := links_same_order F ha _ _ (vertex_spans F i) (vertex_spans F j) h'
    change L+(closing F i).val < L+(closing F j).val at hh
    exact Nat.lt_of_add_lt_add_left hh
  fl i := by
    apply ((leftWindow L R).restrict_fixed_iff F _).mpr
    right
    simp [left_contains, mate_opening]
  fr i := by
    apply ((rightWindow L R).restrict_fixed_iff F _).mpr
    right
    simp [right_contains, mate_closing]
  initial x hx hn i := by
    have e := (mate_left_rest F x hn).trans (congrArg (Fin.castAdd R) hx)
    have h := (link_contains_singleton F ha _ (vertex_spans F i).1 (vertex_spans F i).2 _ e).1
    simpa only [vertex,mate_closing,Fin.lt_def,Fin.val_castAdd] using h
  final x hx hn i := by
    have e := (mate_right_rest F x hn).trans (congrArg (Fin.natAdd L) hx)
    have h := (link_contains_singleton F ha _ (vertex_spans F i).1 (vertex_spans F i).2 _ e).2
    change L+x.val < L+(closing F i).val at h
    exact Nat.lt_of_add_lt_add_left h

@[simp] theorem plan_glue (ha : Admissible F L) : (plan F ha).glue = F := by
  apply Fragment.ext_mate
  intro p
  refine Fin.addCases (fun x => ?_) (fun y => ?_) p
  · by_cases hx : x ∈ Set.range (plan F ha).left
    · obtain ⟨i,rfl⟩ := hx
      simp only [LinkPlan.glue_left, LinkPlan.mateL_link]
      exact (mate_opening F i).symm
    · rw [LinkPlan.glue_left, (plan F ha).mateL_rest hx]
      exact (mate_left_rest F x hx).symm
  · by_cases hy : y ∈ Set.range (plan F ha).right
    · obtain ⟨i,rfl⟩ := hy
      simp only [LinkPlan.glue_right, LinkPlan.mateR_link]
      exact (mate_closing F i).symm
    · rw [LinkPlan.glue_right, (plan F ha).mateR_rest hy]
      exact (mate_right_rest F y hy).symm

end CutData

namespace LinkPlan

variable {A : Fragment L} {B : Fragment R} (P : LinkPlan A B t)

private theorem bound {s n} {Q : Fragment n} {f : Fin s → Fin n}
    (h : StrictMono f) (hf : ∀ i, Q.mate (f i)=f i) : s ≤ Q.weight := by
  classical
  have hs : Finset.univ.image f ⊆ Q.singletons := by
    intro x hx; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
    exact (Q.mem_singletons _).mpr (hf _)
  simpa only [Fragment.weight,Finset.card_image_of_injective _ h.injective, Finset.card_univ, Fintype.card_fin]
    using Finset.card_le_card hs

include P in
theorem le_left : t ≤ A.weight := bound P.ml P.fl
include P in
theorem le_right : t ≤ B.weight := bound P.mr P.fr

@[simp] theorem links_glue : CutData.links P.glue = t := by
  classical
  have s : CutData.openings P.glue = Finset.univ.image P.left := by
    ext x
    by_cases h : x ∈ Set.range P.left
    · obtain ⟨i,rfl⟩ := h
      simp [CutData.openings]
    · have h' : ¬∃ i, P.left i=x := h
      simp [CutData.openings,P.mateL_rest h,h']
  simp [CutData.links, s, Finset.card_image_of_injective _ P.ml.injective]

private theorem weight_sum {n} (F : Fragment n) :
    F.weight = ∑ p, if F.mate p=p then 1 else 0 := by
  simp [Fragment.weight, Fragment.singletons]

private theorem count_rest {s n} {Q : Fragment n} {f : Fin s → Fin n}
    (h : StrictMono f) (hf : ∀ i, Q.mate (f i)=f i) [DecidablePred (· ∈ Set.range f)] :
    (∑ x, if Q.mate x=x ∧ x ∉ Set.range f then 1 else 0) = Q.weight - s := by
  classical
  let T := Finset.univ.image f
  have hs : T ⊆ Q.singletons := by
    intro x hx; obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx; exact (Q.mem_singletons _).mpr (hf _)
  have e : Finset.univ.filter (fun x => Q.mate x=x ∧ x ∉ Set.range f) = Q.singletons \ T := by
    ext x; simp [T, Set.mem_range]
  rw [Finset.sum_boole, e, Finset.card_sdiff_of_subset hs]
  simp [T, Fragment.weight, Finset.card_image_of_injective _ h.injective]

theorem weight_glue : P.glue.weight = A.weight + B.weight - 2*t := by
  classical
  rw [weight_sum, Fin.sum_univ_add]
  simp_rw [P.fixed_left_iff, P.fixed_right_iff]
  rw [count_rest P.ml P.fl, count_rest P.mr P.fr]
  have := P.le_left; have := P.le_right; omega

end LinkPlan

/-- Raw children and the number of links. Both children inherit their
linear orders; there is no choice of an ordering of a clique. -/
@[ext] structure Assembly (L R : ℕ) where
  left : Fragment L
  right : Fragment R
  t : ℕ
  le_left : t ≤ left.weight
  le_right : t ≤ right.weight

namespace Assembly
variable (S : Assembly L R)
def plan := LinkPlan.canonical S.left S.right S.t S.le_left S.le_right
noncomputable def glue := S.plan.glue
end Assembly

def splitAssembly {F : Fragment (L+R)} (h : Admissible F L) : Assembly L R where
  left := (leftWindow L R).restrict F
  right := (rightWindow L R).restrict F
  t := CutData.links F
  le_left := (CutData.plan F h).le_left
  le_right := (CutData.plan F h).le_right

/-- Restricting at a specified admissible split is inverse to the ordered
gluing. This equivalence also covers zero remaining exterior strands. -/
noncomputable def assemblyEquiv (L R : ℕ) :
    {F : Fragment (L+R) // Admissible F L} ≃ Assembly L R where
  toFun F := splitAssembly F.property
  invFun S := ⟨S.glue,S.plan.admissible⟩
  left_inv F := by
    apply Subtype.ext
    change (splitAssembly F.property).plan.glue = F.val
    have e : (splitAssembly F.property).plan = CutData.plan F.val F.property := Subsingleton.elim _ _
    rw [e]
    exact CutData.plan_glue F.val F.property
  right_inv S := by
    apply Assembly.ext
    · exact S.plan.restrict_left
    · exact S.plan.restrict_right
    · exact S.plan.links_glue

end NabergallChordalDiagrams
