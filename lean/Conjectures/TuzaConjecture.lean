import Mathlib.Data.Sym.Sym2
import Mathlib.Tactic.Tauto
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators

/-!
# Edge covers of triangles by book rotation

The graph bounds are `tuza_bound_39_14` and `colored_tuza_bound_21_8`.
The foundational sections marked "Wang" adapt Sichen Wang's MIT-licensed
Lean development (https://github.com/sichen-wang/tuza-lean, revision
5cae999212a06418941fa9c909529a4ff38e1e5e) to Lean 4.35.0.

MIT License

Copyright (c) 2026 Sichen Wang

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

section
-- Wang: Basic.Geometry
/-! Triangle edges and the geometry of two and three pages. -/

namespace TuzaBound

variable {V : Type*} [DecidableEq V]

/-- The three unoriented edges on the listed vertices. -/
def triangleEdges (u v w : V) : Finset (Sym2 V) :=
  {s(u, v), s(u, w), s(v, w)}

@[simp]
theorem mem_triangleEdges {e : Sym2 V} {u v w : V} :
    e ∈ triangleEdges u v w ↔ e = s(u, v) ∨ e = s(u, w) ∨ e = s(v, w) := by
  simp [triangleEdges]

/-- A triangle is an edge set on three distinct vertices. -/
def IsTriangle (T : Finset (Sym2 V)) : Prop :=
  ∃ u v w, u ≠ v ∧ u ≠ w ∧ v ≠ w ∧ T = triangleEdges u v w

theorem isTriangle_triangleEdges {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    IsTriangle (triangleEdges u v w) :=
  ⟨u, v, w, huv, huw, hvw, rfl⟩

theorem triangleEdges_card {u v w : V}
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    (triangleEdges u v w).card = 3 := by
  have h₁ : s(u, v) ≠ s(u, w) := by
    intro h
    exact hvw (Sym2.congr_right.mp h)
  have h₂ : s(u, v) ≠ s(v, w) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · exact huv h.1
    · exact huw h.1
  have h₃ : s(u, w) ≠ s(v, w) := by
    intro h
    exact huv (Sym2.congr_left.mp h)
  simp [triangleEdges, h₁, h₂, h₃]

theorem IsTriangle.card_eq_three {T : Finset (Sym2 V)} (hT : IsTriangle T) :
    T.card = 3 := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  exact triangleEdges_card huv huw hvw

theorem IsTriangle.not_mem_diag {T : Finset (Sym2 V)}
    (hT : IsTriangle T) (z : V) : s(z, z) ∉ T := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff]
  aesop

theorem IsTriangle.ne_of_mem {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v : V} (h : s(u, v) ∈ T) : u ≠ v := by
  rintro rfl
  exact hT.not_mem_diag u h

/-- Any two edges of a triangle have a common endpoint. -/
theorem IsTriangle.edges_incident {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {e f : Sym2 V} (he : e ∈ T) (hf : f ∈ T) :
    ∃ z : V, z ∈ e ∧ z ∈ f := by
  rcases hT with ⟨u, v, w, huv, huw, hvw, rfl⟩
  rcases mem_triangleEdges.mp he with rfl | rfl | rfl <;>
    rcases mem_triangleEdges.mp hf with rfl | rfl | rfl
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨u, by simp, by simp⟩
  · exact ⟨w, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩
  · exact ⟨w, by simp, by simp⟩
  · exact ⟨v, by simp, by simp⟩

/-- Two distinct edges incident at a vertex determine the triangle. -/
theorem IsTriangle.eq_of_spokes {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (he : s(u, v) ∈ T) (hf : s(u, w) ∈ T) :
    T = triangleEdges u v w := by
  rcases hT with ⟨a, b, c, hab, hac, hbc, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff] at he hf
  rcases he with h | h | h <;>
    rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    rcases hf with h | h | h <;>
    rcases h with ⟨hc, hd⟩ | ⟨hc, hd⟩ <;>
    subst_vars <;>
    simp_all [triangleEdges, Sym2.eq_swap, Finset.insert_comm]
  all_goals
    ext e
    simp only [Finset.mem_insert, Finset.mem_singleton]
    tauto

theorem IsTriangle.exists_third_of_mem {T : Finset (Sym2 V)}
    (hT : IsTriangle T) {u v : V} (he : s(u, v) ∈ T) :
    ∃ w, u ≠ w ∧ v ≠ w ∧ T = triangleEdges u v w := by
  rcases hT with ⟨a, b, c, hab, hac, hbc, rfl⟩
  simp only [mem_triangleEdges, Sym2.eq_iff] at he
  rcases he with h | h | h
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨c, hac, hbc, rfl⟩
    · refine ⟨c, hbc, hac, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨b, hab, hbc.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_left_comm]
    · refine ⟨b, hbc.symm, hab, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_assoc]
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · refine ⟨a, hab.symm, hac.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_left_comm]
    · refine ⟨a, hac.symm, hab.symm, ?_⟩
      ext e
      simp [triangleEdges, Sym2.eq_swap, or_comm, or_assoc]

theorem IsTriangle.eq_of_two_common_edges {T U : Finset (Sym2 V)}
    (hT : IsTriangle T) (hU : IsTriangle U) {e f : Sym2 V}
    (hef : e ≠ f) (heT : e ∈ T) (hfT : f ∈ T)
    (heU : e ∈ U) (hfU : f ∈ U) : T = U := by
  obtain ⟨u, hue, huf⟩ := hT.edges_incident heT hfT
  obtain ⟨v, rfl⟩ := Sym2.mem_iff_exists.mp hue
  obtain ⟨w, rfl⟩ := Sym2.mem_iff_exists.mp huf
  have huv : u ≠ v := hT.ne_of_mem heT
  have huw : u ≠ w := hT.ne_of_mem hfT
  have hvw : v ≠ w := by
    rintro rfl
    exact hef rfl
  exact (hT.eq_of_spokes huv huw hvw heT hfT).trans
    (hU.eq_of_spokes huv huw hvw heU hfU).symm

theorem IsTriangle.inter_card_le_one {T U : Finset (Sym2 V)}
    (hT : IsTriangle T) (hU : IsTriangle U) (hne : T ≠ U) :
    (T ∩ U).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  by_contra hef
  exact hne (hT.eq_of_two_common_edges hU hef
    (Finset.mem_inter.mp he).1 (Finset.mem_inter.mp hf).1
    (Finset.mem_inter.mp he).2 (Finset.mem_inter.mp hf).2)

/-- Triangles whose listed vertices have only the first vertex in common share no edge. -/
theorem triangleEdges_disjoint_of_five_distinct {u v w x y : V}
    (hvertices : [u, v, w, x, y].Nodup) :
    Disjoint (triangleEdges u v w) (triangleEdges u x y) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  rcases mem_triangleEdges.mp he with rfl | rfl | rfl <;>
    simp_all [mem_triangleEdges, List.nodup_cons]

/-- A triangle meeting both pages and missing their spine uses the opposite edge. -/
theorem two_page_triangle {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y : V} (hvertices : [u, v, x, y].Nodup)
    (hspine : s(u, v) ∉ T)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty) :
    T = triangleEdges u x y ∨ T = triangleEdges v x y := by
  have hdistinct : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using hvertices
  rcases hdistinct with ⟨huv, hux, huy, hvx, hvy, hxy⟩
  obtain ⟨e, he⟩ := hx
  obtain ⟨heT, heX⟩ := Finset.mem_inter.mp he
  obtain ⟨f, hf⟩ := hy
  obtain ⟨hfT, hfY⟩ := Finset.mem_inter.mp hf
  rcases mem_triangleEdges.mp heX with rfl | rfl | rfl <;>
    rcases mem_triangleEdges.mp hfY with rfl | rfl | rfl
  all_goals try exact (hspine heT).elim
  all_goals try exact (hspine hfT).elim
  · exact Or.inl (hT.eq_of_spokes hux huy hxy heT hfT)
  · obtain ⟨z, hz, hz'⟩ := hT.edges_incident heT hfT
    simp only [Sym2.mem_iff] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h <;> simp_all
  · obtain ⟨z, hz, hz'⟩ := hT.edges_incident heT hfT
    simp only [Sym2.mem_iff] at hz hz'
    rcases hz with rfl | rfl <;> rcases hz' with h | h <;> simp_all
  · exact Or.inr (hT.eq_of_spokes hvx hvy hxy heT hfT)

theorem two_page_opposite_mem {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y : V} (hvertices : [u, v, x, y].Nodup)
    (hspine : s(u, v) ∉ T)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty) : s(x, y) ∈ T := by
  rcases two_page_triangle hT hvertices hspine hx hy with rfl | rfl <;> simp

/-- A triangle meeting three distinct pages must contain their common spine. -/
theorem three_page_spine {T : Finset (Sym2 V)} (hT : IsTriangle T)
    {u v x y z : V} (hvertices : [u, v, x, y, z].Nodup)
    (hx : (T ∩ triangleEdges u v x).Nonempty)
    (hy : (T ∩ triangleEdges u v y).Nonempty)
    (hz : (T ∩ triangleEdges u v z).Nonempty) : s(u, v) ∈ T := by
  by_contra hspine
  have hfour : [u, v, x, y].Nodup := by
    simp_all [List.nodup_cons]
  obtain ⟨e, he⟩ := hz
  obtain ⟨heT, heZ⟩ := Finset.mem_inter.mp he
  rcases two_page_triangle hT hfour hspine hx hy with h | h <;>
    rw [h] at heT <;>
    rcases mem_triangleEdges.mp heT with rfl | rfl | rfl <;>
    simp_all [mem_triangleEdges, List.nodup_cons] <;> aesop

end TuzaBound
end

section
-- Wang: Basic.Packing
/-!
Finite families of edge sets. These definitions are independent of graph geometry.
Graph triangles are connected to them in the graph module.
-/

namespace TuzaBound

open Finset

variable {E : Type*} [DecidableEq E]

/-- The union of the edges used by a family. -/
def support (P : Finset (Finset E)) : Finset E := P.biUnion id

@[simp] theorem mem_support {e : E} {P : Finset (Finset E)} :
    e ∈ support P ↔ ∃ T ∈ P, e ∈ T := by
  simp [support]

@[simp] theorem support_insert (T : Finset E) (P : Finset (Finset E)) :
    support (insert T P) = T ∪ support P := by
  simp [support]

theorem support_mono {P Q : Finset (Finset E)} (h : P ⊆ Q) :
    support P ⊆ support Q := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact mem_support.mpr ⟨T, h hT, heT⟩

/-- A packing consists of members of the family that are pairwise edge-disjoint. -/
def IsPacking (F P : Finset (Finset E)) : Prop :=
  P ⊆ F ∧ (P : Set (Finset E)).Pairwise Disjoint

/-- Maximum is with respect to the number of triangles. -/
def IsMaximumPacking (F P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q → Q.card ≤ P.card

/-- A transversal meets every member in an edge. -/
def IsCover (F : Finset (Finset E)) (C : Finset E) : Prop :=
  ∀ T ∈ F, (T ∩ C).Nonempty

/-- Deleting selected edges removes every member that meets one of them. -/
def residual (F : Finset (Finset E)) (C : Finset E) : Finset (Finset E) :=
  F.filter (fun T => Disjoint T C)

@[simp] theorem mem_residual {F : Finset (Finset E)} {C T : Finset E} :
    T ∈ residual F C ↔ T ∈ F ∧ Disjoint T C := by
  simp [residual]

omit [DecidableEq E] in
theorem packing_empty (F : Finset (Finset E)) : IsPacking F ∅ := by
  simp [IsPacking, Set.Pairwise]

omit [DecidableEq E] in
theorem IsPacking.subfamily {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : Q ⊆ P) : IsPacking F Q := by
  exact ⟨hQ.trans hP.1, fun T hT U hU hne => hP.2 (hQ hT) (hQ hU) hne⟩

omit [DecidableEq E] in
theorem IsPacking.mono_family {F F' P : Finset (Finset E)}
    (hP : IsPacking F P) (hF : F ⊆ F') : IsPacking F' P :=
  ⟨hP.1.trans hF, hP.2⟩

theorem IsPacking.union {F P Q : Finset (Finset E)}
    (hP : IsPacking F P) (hQ : IsPacking F Q)
    (hd : Disjoint (support P) (support Q)) : IsPacking F (P ∪ Q) := by
  refine ⟨union_subset hP.1 hQ.1, ?_⟩
  have hcross : ∀ T ∈ P, ∀ U ∈ Q, Disjoint T U := by
    intro T hT U hU
    exact hd.mono (fun e he => mem_support.mpr ⟨T, hT, he⟩)
      (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  intro T hT U hU hne
  rcases mem_union.mp hT with hT | hT <;> rcases mem_union.mp hU with hU | hU
  · exact hP.2 hT hU hne
  · exact hcross T hT U hU
  · exact (hcross U hU T hT).symm
  · exact hQ.2 hT hU hne

theorem disjoint_of_support_disjoint {P Q : Finset (Finset E)}
    (hne : ∀ T ∈ P, T.Nonempty) (hd : Disjoint (support P) (support Q)) :
    Disjoint P Q := by
  apply disjoint_left.mpr
  intro T hT hU
  obtain ⟨e, he⟩ := hne T hT
  exact disjoint_left.mp hd (mem_support.mpr ⟨T, hT, he⟩)
    (mem_support.mpr ⟨T, hU, he⟩)

omit [DecidableEq E] in
theorem exists_maximumPacking (F : Finset (Finset E)) :
    ∃ P, IsMaximumPacking F P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P, hP, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hc⟩
  refine ⟨P, (mem_filter.mp hP).2, ?_⟩
  intro Q hQ
  exact hmax Q (mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩)

/-- One maximum packing, chosen from the finite collection of all packings. -/
noncomputable def maximumPacking (F : Finset (Finset E)) : Finset (Finset E) :=
  Classical.choose (exists_maximumPacking F)

omit [DecidableEq E] in
theorem maximumPacking_spec (F : Finset (Finset E)) :
    IsMaximumPacking F (maximumPacking F) :=
  Classical.choose_spec (exists_maximumPacking F)

/-- The maximum packing size. -/
noncomputable def packingNumber (F : Finset (Finset E)) : ℕ :=
  (maximumPacking F).card

omit [DecidableEq E] in
theorem IsPacking.card_le {F P : Finset (Finset E)} (hP : IsPacking F P) :
    P.card ≤ packingNumber F :=
  (maximumPacking_spec F).2 P hP

omit [DecidableEq E] in
theorem IsMaximumPacking.card_eq {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) : P.card = packingNumber F := by
  apply Nat.le_antisymm hP.1.card_le
  exact hP.2 _ (maximumPacking_spec F).1

omit [DecidableEq E] in
theorem IsPacking.maximum_of_card_eq {F P : Finset (Finset E)}
    (hP : IsPacking F P) (hc : P.card = packingNumber F) :
    IsMaximumPacking F P := by
  refine ⟨hP, fun Q hQ => ?_⟩
  rw [hc]
  exact hQ.card_le

theorem packing_insert {F P : Finset (Finset E)} {T : Finset E}
    (hP : IsPacking F P) (hT : T ∈ F) (hd : Disjoint T (support P)) :
    IsPacking F (insert T P) := by
  refine ⟨insert_subset hT hP.1, ?_⟩
  intro U hU V hV hne
  have hdis : ∀ U ∈ P, Disjoint T U := by
    intro U hU
    exact hd.mono_right (fun e he => mem_support.mpr ⟨U, hU, he⟩)
  simp only [mem_coe, mem_insert] at hU hV
  rcases hU with rfl | hU
  · rcases hV with rfl | hV
    · exact False.elim (hne rfl)
    · exact hdis V hV
  · rcases hV with rfl | hV
    · exact (hdis U hU).symm
    · exact hP.2 hU hV hne

theorem IsMaximumPacking.meets_support {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {T : Finset E} (hT : T ∈ F)
    (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hlt := hP.2 (insert T P) (packing_insert hP.1 hT hd)
  simp [hnot] at hlt

theorem IsMaximumPacking.support_covers {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

theorem IsPacking.disjoint_support_erase {F P : Finset (Finset E)}
    (hP : IsPacking F P) {S T : Finset E} (hS : S ∈ P)
    (hT : ∀ e ∈ T, e ∈ support P → e ∈ S) :
    Disjoint T (support (P.erase S)) := by
  apply disjoint_left.mpr
  intro e heT heP
  obtain ⟨U, hU, heU⟩ := mem_support.mp heP
  obtain ⟨hUS, hUP⟩ := mem_erase.mp hU
  have heS := hT e heT (mem_support.mpr ⟨U, hUP, heU⟩)
  exact disjoint_left.mp (hP.2 hUP hS hUS) heU heS

/-- Replacing one member of a maximum packing by two disjoint members is impossible. -/
theorem IsMaximumPacking.no_two_for_one {F P : Finset (Finset E)}
    (hP : IsMaximumPacking F P) {S T U : Finset E}
    (hS : S ∈ P) (hT : T ∈ F) (hU : U ∈ F)
    (hneT : T.Nonempty) (hneU : U.Nonempty) (hdTU : Disjoint T U)
    (hdT : Disjoint T (support (P.erase S)))
    (hdU : Disjoint U (support (P.erase S))) : False := by
  have hbase := hP.1.subfamily (erase_subset S P)
  have hfirst := packing_insert hbase hT hdT
  have hsecond : IsPacking F (insert U (insert T (P.erase S))) := by
    apply packing_insert hfirst hU
    rw [support_insert]
    exact disjoint_union_right.mpr ⟨hdTU.symm, hdU⟩
  have ht : T ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneT
    exact disjoint_left.mp hdT he (mem_support.mpr ⟨T, hmem, he⟩)
  have hu : U ∉ P.erase S := by
    intro hmem
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdU he (mem_support.mpr ⟨U, hmem, he⟩)
  have hUT : U ≠ T := by
    rintro rfl
    obtain ⟨e, he⟩ := hneU
    exact disjoint_left.mp hdTU he he
  have hbound := hP.2 _ hsecond
  have hsize := card_erase_add_one hS
  simp only [card_insert_of_notMem ht,
    card_insert_of_notMem (by simp [hu, hUT] : U ∉ insert T (P.erase S))] at hbound
  omega

theorem support_covers (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) : IsCover F (support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hF T hT
  exact ⟨e, mem_inter.mpr ⟨he, mem_support.mpr ⟨T, hT, he⟩⟩⟩

/-- Minimum transversal size; the theorems below ensure attainment for
families of nonempty edge sets, in particular for triangle families. -/
noncomputable def transversalNumber (F : Finset (Finset E)) : ℕ :=
  sInf {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}

theorem IsCover.number_le {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : transversalNumber F ≤ C.card := by
  exact csInf_le (OrderBot.bddBelow _) ⟨C, hC, rfl⟩

theorem exists_minimumCover (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, IsCover F C ∧ C.card = transversalNumber F := by
  have hex : {n : ℕ | ∃ C : Finset E, IsCover F C ∧ C.card = n}.Nonempty :=
    ⟨(support F).card, support F, support_covers F hF, rfl⟩
  exact csInf_mem hex

theorem IsCover.mono {F : Finset (Finset E)} {C D : Finset E}
    (hC : IsCover F C) (hCD : C ⊆ D) : IsCover F D := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1, hCD (mem_inter.mp he).2⟩⟩

theorem IsCover.mono_family {F F' : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) (hF : F' ⊆ F) : IsCover F' C :=
  fun T hT => hC T (hF hT)

/-- Extraneous edges never help a transversal: every cover can be restricted
to the edges that actually occur in the family. -/
theorem IsCover.inter_support {F : Finset (Finset E)} {C : Finset E}
    (hC : IsCover F C) : IsCover F (C ∩ support F) := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  obtain ⟨heT, heC⟩ := mem_inter.mp he
  exact ⟨e, mem_inter.mpr ⟨heT,
    mem_inter.mpr ⟨heC, mem_support.mpr ⟨T, hT, heT⟩⟩⟩⟩

theorem exists_minimumCover_subset_support (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.Nonempty) :
    ∃ C, C ⊆ support F ∧ IsCover F C ∧ C.card = transversalNumber F := by
  obtain ⟨C, hC, hc⟩ := exists_minimumCover F hF
  refine ⟨C ∩ support F, inter_subset_right, hC.inter_support, ?_⟩
  exact Nat.le_antisymm ((card_le_card inter_subset_left).trans_eq hc)
    hC.inter_support.number_le

theorem cover_union_residual {F : Finset (Finset E)} {C D : Finset E}
    (hD : IsCover (residual F C) D) : IsCover F (C ∪ D) := by
  intro T hT
  by_cases hd : Disjoint T C
  · obtain ⟨e, he⟩ := hD T (mem_residual.mpr ⟨hT, hd⟩)
    exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1,
      mem_union_right _ (mem_inter.mp he).2⟩⟩
  · obtain ⟨e, heT, heC⟩ := not_disjoint_iff.mp hd
    exact ⟨e, mem_inter.mpr ⟨heT, mem_union_left _ heC⟩⟩

theorem transversalNumber_le_add_residual (F : Finset (Finset E)) (C : Finset E)
    (hF : ∀ T ∈ F, T.Nonempty) :
    transversalNumber F ≤ C.card + transversalNumber (residual F C) := by
  obtain ⟨D, hD, hcard⟩ := exists_minimumCover (residual F C)
    (fun T hT => hF T (mem_residual.mp hT).1)
  calc
    transversalNumber F ≤ (C ∪ D).card := (cover_union_residual hD).number_le
    _ ≤ C.card + D.card := card_union_le C D
    _ = _ := by rw [hcard]

theorem IsPacking.card_support {F P : Finset (Finset E)} (hP : IsPacking F P) :
    (support P).card = ∑ T ∈ P, T.card := by
  exact card_biUnion hP.2

theorem IsPacking.card_support_uniform {F P : Finset (Finset E)}
    (hP : IsPacking F P) {k : ℕ} (hcard : ∀ T ∈ P, T.card = k) :
    (support P).card = k * P.card := by
  rw [hP.card_support]
  calc
    ∑ T ∈ P, T.card = ∑ _T ∈ P, k := sum_congr rfl hcard
    _ = k * P.card := by simp [Nat.mul_comm]

theorem transversalNumber_le_three_packingNumber (F : Finset (Finset E))
    (hF : ∀ T ∈ F, T.card = 3) :
    transversalNumber F ≤ 3 * packingNumber F := by
  have hne : ∀ T ∈ F, T.Nonempty := by
    intro T hT
    exact card_pos.mp (by rw [hF T hT]; decide)
  have hP := maximumPacking_spec F
  calc
    transversalNumber F ≤ (support (maximumPacking F)).card :=
      (hP.support_covers hne).number_le
    _ = 3 * packingNumber F :=
      hP.1.card_support_uniform (fun T hT => hF T (hP.1.1 hT))

/-- First maximize the number of members in S, then the total packing size. -/
def IsLexMaximumPacking (F S P : Finset (Finset E)) : Prop :=
  IsPacking F P ∧ ∀ Q, IsPacking F Q →
    (Q ∩ S).card ≤ (P ∩ S).card ∧
    ((Q ∩ S).card = (P ∩ S).card → Q.card ≤ P.card)

theorem exists_lexMaximumPacking (F S : Finset (Finset E)) :
    ∃ P, IsLexMaximumPacking F S P := by
  classical
  let candidates := F.powerset.filter (IsPacking F)
  have hc : (∅ : Finset (Finset E)) ∈ candidates := by
    simp [candidates, packing_empty]
  obtain ⟨P₀, hP₀, hmax₀⟩ := candidates.exists_max_image
    (fun P => (P ∩ S).card) ⟨∅, hc⟩
  let tied := candidates.filter (fun P => (P ∩ S).card = (P₀ ∩ S).card)
  have htied : P₀ ∈ tied := by simp [tied, hP₀]
  obtain ⟨P, hP, hmax⟩ := tied.exists_max_image Finset.card ⟨P₀, htied⟩
  obtain ⟨hPc, hPeq⟩ := mem_filter.mp hP
  refine ⟨P, (mem_filter.mp hPc).2, ?_⟩
  intro Q hQ
  have hQc : Q ∈ candidates := mem_filter.mpr ⟨mem_powerset.mpr hQ.1, hQ⟩
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    exact hmax₀ Q hQc
  · intro hQeq
    exact hmax Q (mem_filter.mpr ⟨hQc, hQeq.trans hPeq⟩)

theorem IsLexMaximumPacking.typePart_maximum {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hSF : S ⊆ F) :
    IsMaximumPacking S (P ∩ S) := by
  have hp : IsPacking S (P ∩ S) :=
    ⟨inter_subset_right, fun T hT U hU hne =>
      hP.1.2 (mem_inter.mp hT).1 (mem_inter.mp hU).1 hne⟩
  refine ⟨hp, fun Q hQ => ?_⟩
  have hbound := (hP.2 Q (hQ.mono_family hSF)).1
  simpa [inter_eq_left.mpr hQ.1] using hbound

theorem IsLexMaximumPacking.meets_support {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) {T : Finset E}
    (hT : T ∈ F) (hne : T.Nonempty) : (T ∩ support P).Nonempty := by
  by_contra hn
  have hd : Disjoint T (support P) := disjoint_iff_inter_eq_empty.mpr
    (not_nonempty_iff_eq_empty.mp hn)
  have hnot : T ∉ P := by
    intro hmem
    obtain ⟨e, he⟩ := hne
    exact disjoint_left.mp hd he (mem_support.mpr ⟨T, hmem, he⟩)
  have hins := packing_insert hP.1 hT hd
  have hlex := hP.2 (insert T P) hins
  have hmono : (P ∩ S).card ≤ (insert T P ∩ S).card :=
    card_le_card (inter_subset_inter (subset_insert T P) Subset.rfl)
  have heq := Nat.le_antisymm hlex.1 hmono
  have hcard := hlex.2 heq
  simp [hnot] at hcard

theorem IsLexMaximumPacking.support_covers {F S P : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hF : ∀ T ∈ F, T.Nonempty) :
    IsCover F (support P) :=
  fun T hT => hP.meets_support hT (hF T hT)

/-- Any packing with the same two optimal counts retains the same maximality. -/
theorem IsLexMaximumPacking.of_same_counts {F S P Q : Finset (Finset E)}
    (hP : IsLexMaximumPacking F S P) (hQ : IsPacking F Q)
    (hfirst : (Q ∩ S).card = (P ∩ S).card) (hsecond : Q.card = P.card) :
    IsLexMaximumPacking F S Q := by
  refine ⟨hQ, fun U hU => ?_⟩
  obtain ⟨hu₁, hu₂⟩ := hP.2 U hU
  rw [hfirst, hsecond]
  exact ⟨hu₁, hu₂⟩

end TuzaBound
end

section
-- Wang: Basic.Graph
/-! The connection between finite edge families and ordinary finite simple graphs. -/

namespace TuzaBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All actual triangles whose edges belong to the given edge set. -/
noncomputable def trianglesOn (A : Finset (Sym2 V)) : Finset (Finset (Sym2 V)) := by
  classical
  exact univ.filter (fun T => IsTriangle T ∧ T ⊆ A)

@[simp] theorem mem_trianglesOn {A T : Finset (Sym2 V)} :
    T ∈ trianglesOn A ↔ IsTriangle T ∧ T ⊆ A := by
  classical
  simp [trianglesOn]

theorem trianglesOn_card {A T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    T.card = 3 := (mem_trianglesOn.mp hT).1.card_eq_three

theorem trianglesOn_nonempty {A T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    T.Nonempty := card_pos.mp (by rw [trianglesOn_card hT]; decide)

theorem trianglesOn_mono {A B : Finset (Sym2 V)} (h : A ⊆ B) :
    trianglesOn A ⊆ trianglesOn B := by
  intro T hT
  obtain ⟨ht, hta⟩ := mem_trianglesOn.mp hT
  exact mem_trianglesOn.mpr ⟨ht, hta.trans h⟩

/-- Edge deletion removes precisely the triangles meeting a deleted edge. -/
theorem trianglesOn_sdiff (A C : Finset (Sym2 V)) :
    trianglesOn (A \ C) = residual (trianglesOn A) C := by
  ext T
  simp only [mem_trianglesOn, mem_residual]
  constructor
  · rintro ⟨hT, hsub⟩
    refine ⟨⟨hT, fun e he => (mem_sdiff.mp (hsub he)).1⟩, disjoint_left.mpr ?_⟩
    intro e heT heC
    exact (mem_sdiff.mp (hsub heT)).2 heC
  · rintro ⟨⟨hT, hsub⟩, hd⟩
    refine ⟨hT, fun e he => mem_sdiff.mpr ⟨hsub he, ?_⟩⟩
    exact fun heC => disjoint_left.mp hd he heC

/-- The edge set of a finite simple graph. -/
noncomputable def graphEdges (G : SimpleGraph V) : Finset (Sym2 V) := by
  classical
  exact G.edgeSet.toFinset

omit [DecidableEq V] in
@[simp] theorem mem_graphEdges {G : SimpleGraph V} {e : Sym2 V} :
    e ∈ graphEdges G ↔ e ∈ G.edgeSet := by
  classical
  simp [graphEdges]

omit [DecidableEq V] in
@[simp] theorem pair_mem_graphEdges {G : SimpleGraph V} {u v : V} :
    s(u, v) ∈ graphEdges G ↔ G.Adj u v := by
  simp

/-- The family used to define the graph's packing and transversal numbers. -/
noncomputable def graphTriangles (G : SimpleGraph V) : Finset (Finset (Sym2 V)) :=
  trianglesOn (graphEdges G)

/-- Membership means exactly three pairwise adjacent vertices and their three edges. -/
theorem mem_graphTriangles_iff {G : SimpleGraph V} {T : Finset (Sym2 V)} :
    T ∈ graphTriangles G ↔
      ∃ u v w, G.Adj u v ∧ G.Adj u w ∧ G.Adj v w ∧ T = triangleEdges u v w := by
  constructor
  · intro hT
    obtain ⟨⟨u, v, w, huv, huw, hvw, rfl⟩, hsub⟩ := mem_trianglesOn.mp hT
    refine ⟨u, v, w, ?_, ?_, ?_, rfl⟩
    all_goals apply pair_mem_graphEdges.mp; apply hsub; simp
  · rintro ⟨u, v, w, huv, huw, hvw, rfl⟩
    apply mem_trianglesOn.mpr
    refine ⟨isTriangle_triangleEdges huv.ne huw.ne hvw.ne, ?_⟩
    intro e he
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · exact pair_mem_graphEdges.mpr huv
    · exact pair_mem_graphEdges.mpr huw
    · exact pair_mem_graphEdges.mpr hvw

/-- The representation agrees with mathlib's standard three-vertex clique predicate. -/
theorem triangleEdges_mem_graphTriangles_iff {G : SimpleGraph V} {u v w : V} :
    triangleEdges u v w ∈ graphTriangles G ↔ G.IsNClique 3 {u, v, w} := by
  rw [SimpleGraph.is3Clique_triple_iff]
  constructor
  · intro h
    have hsub := (mem_trianglesOn.mp h).2
    exact ⟨pair_mem_graphEdges.mp (hsub (by simp)),
      pair_mem_graphEdges.mp (hsub (by simp)),
      pair_mem_graphEdges.mp (hsub (by simp))⟩
  · rintro ⟨hab, hac, hbc⟩
    exact mem_graphTriangles_iff.mpr ⟨u, v, w, hab, hac, hbc, rfl⟩

/-- The paper's ν(G). -/
noncomputable def nu (G : SimpleGraph V) : ℕ := packingNumber (graphTriangles G)

/-- The paper's τ(G). -/
noncomputable def tau (G : SimpleGraph V) : ℕ := transversalNumber (graphTriangles G)

theorem graph_trivial_bound (G : SimpleGraph V) : tau G ≤ 3 * nu G :=
  transversalNumber_le_three_packingNumber _ (fun _ hT => trianglesOn_card hT)

/-- The finite-family cover condition is exactly the usual requirement on
every triple of pairwise adjacent vertices. -/
theorem graph_cover_iff_adj (G : SimpleGraph V) (C : Finset (Sym2 V)) :
    IsCover (graphTriangles G) C ↔
      ∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u, v) ∈ C ∨ s(u, w) ∈ C ∨ s(v, w) ∈ C := by
  constructor
  · intro hC u v w huv huw hvw
    obtain ⟨e, he⟩ := hC (triangleEdges u v w)
      (mem_graphTriangles_iff.mpr ⟨u, v, w, huv, huw, hvw, rfl⟩)
    obtain ⟨heT, heC⟩ := mem_inter.mp he
    rcases mem_triangleEdges.mp heT with rfl | rfl | rfl
    · exact Or.inl heC
    · exact Or.inr (Or.inl heC)
    · exact Or.inr (Or.inr heC)
  · intro hC T hT
    obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := mem_graphTriangles_iff.mp hT
    rcases hC u v w huv huw hvw with he | he | he
    · exact ⟨s(u, v), mem_inter.mpr ⟨by simp, he⟩⟩
    · exact ⟨s(u, w), mem_inter.mpr ⟨by simp, he⟩⟩
    · exact ⟨s(v, w), mem_inter.mpr ⟨by simp, he⟩⟩

theorem graphTriangles_support_subset (G : SimpleGraph V) :
    support (graphTriangles G) ⊆ graphEdges G := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp hT).2 heT

/-- A minimum cover can be chosen from the graph's edges. -/
theorem exists_graph_minimumCover (G : SimpleGraph V) :
    ∃ C, C ⊆ graphEdges G ∧ IsCover (graphTriangles G) C ∧ C.card = tau G := by
  obtain ⟨C, hsub, hC, hc⟩ := exists_minimumCover_subset_support (graphTriangles G)
    (fun _ hT => trianglesOn_nonempty hT)
  exact ⟨C, hsub.trans (graphTriangles_support_subset G), hC, hc⟩

/-- An upper bound on the formal τ is equivalent to an ordinary graph-edge
transversal of that size. -/
theorem tau_le_iff (G : SimpleGraph V) (n : ℕ) :
    tau G ≤ n ↔ ∃ C, C ⊆ graphEdges G ∧
      IsCover (graphTriangles G) C ∧ C.card ≤ n := by
  constructor
  · intro h
    obtain ⟨C, hsub, hC, hc⟩ := exists_graph_minimumCover G
    exact ⟨C, hsub, hC, hc ▸ h⟩
  · rintro ⟨C, _, hC, hc⟩
    exact hC.number_le.trans hc

/-- The formal ν is the maximum size over actual edge-disjoint graph triangles. -/
theorem le_nu_iff (G : SimpleGraph V) (n : ℕ) :
    n ≤ nu G ↔ ∃ P, IsPacking (graphTriangles G) P ∧ n ≤ P.card := by
  constructor
  · intro h
    exact ⟨maximumPacking (graphTriangles G), (maximumPacking_spec _).1, h⟩
  · rintro ⟨P, hP, hc⟩
    exact hc.trans hP.card_le

end TuzaBound
end

section
-- Wang: Basic.Coloring
/-! Red and blue edges in finite families of three-edge sets. -/

namespace TuzaBound

open Finset

variable {E : Type*} [DecidableEq E]

/-- The red edges used by a family. -/
def redEdges (R : Finset E) (P : Finset (Finset E)) : Finset E :=
  support P ∩ R

/-- Every edge outside the specified red set is blue. -/
def blueEdges (R : Finset E) (P : Finset (Finset E)) : Finset E :=
  support P \ R

/-- Each member has exactly three edges, exactly one of which is red. -/
def ColoredFamily (F : Finset (Finset E)) (R : Finset E) : Prop :=
  ∀ T ∈ F, T.card = 3 ∧ (T ∩ R).card = 1

@[simp] theorem mem_redEdges {R : Finset E} {P : Finset (Finset E)} {e : E} :
    e ∈ redEdges R P ↔ e ∈ support P ∧ e ∈ R := by
  simp [redEdges]

@[simp] theorem mem_blueEdges {R : Finset E} {P : Finset (Finset E)} {e : E} :
    e ∈ blueEdges R P ↔ e ∈ support P ∧ e ∉ R := by
  simp [blueEdges]

theorem redEdges_subset_support (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ⊆ support P := inter_subset_left

theorem redEdges_subset_red (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ⊆ R := inter_subset_right

theorem blueEdges_subset_support (R : Finset E) (P : Finset (Finset E)) :
    blueEdges R P ⊆ support P := sdiff_subset

theorem redEdges_disjoint_blueEdges (R : Finset E) (P : Finset (Finset E)) :
    Disjoint (redEdges R P) (blueEdges R P) := by
  apply disjoint_left.mpr
  intro e heR heB
  exact (mem_blueEdges.mp heB).2 (mem_redEdges.mp heR).2

theorem blueEdges_disjoint_red (R : Finset E) (P : Finset (Finset E)) :
    Disjoint (blueEdges R P) R := by
  apply disjoint_left.mpr
  intro e heB heR
  exact (mem_blueEdges.mp heB).2 heR

@[simp] theorem redEdges_union_blueEdges (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P ∪ blueEdges R P = support P := by
  ext e
  by_cases he : e ∈ R <;> simp [redEdges, blueEdges, he]

theorem card_blueEdges_add_card_redEdges (R : Finset E) (P : Finset (Finset E)) :
    (blueEdges R P).card + (redEdges R P).card = (support P).card := by
  exact card_sdiff_add_card_inter (support P) R

theorem redEdges_eq_biUnion (R : Finset E) (P : Finset (Finset E)) :
    redEdges R P = P.biUnion (fun T => T ∩ R) := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heR⟩ := mem_redEdges.mp he
    obtain ⟨T, hT, heT⟩ := mem_support.mp heP
    exact mem_biUnion.mpr ⟨T, hT, mem_inter.mpr ⟨heT, heR⟩⟩
  · intro he
    obtain ⟨T, hT, heTR⟩ := mem_biUnion.mp he
    obtain ⟨heT, heR⟩ := mem_inter.mp heTR
    exact mem_redEdges.mpr ⟨mem_support.mpr ⟨T, hT, heT⟩, heR⟩

theorem ColoredFamily.subfamily {F F' : Finset (Finset E)} {R : Finset E}
    (hF : ColoredFamily F R) (hsub : F' ⊆ F) : ColoredFamily F' R :=
  fun T hT => hF T (hsub hT)

theorem ColoredFamily.residual {F : Finset (Finset E)} {R C : Finset E}
    (hF : ColoredFamily F R) : ColoredFamily (residual F C) R :=
  hF.subfamily (filter_subset _ _)

theorem ColoredFamily.member_nonempty {F : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hT : T ∈ F) : T.Nonempty := by
  apply card_pos.mp
  rw [(hF T hT).1]
  decide

theorem ColoredFamily.member_blue_card {F : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hT : T ∈ F) : (T \ R).card = 2 := by
  have hsum := card_sdiff_add_card_inter T R
  obtain ⟨hthree, hone⟩ := hF T hT
  omega

theorem ColoredFamily.red_eq_singleton {F : Finset (Finset E)} {R T : Finset E}
    {e : E} (hF : ColoredFamily F R) (hT : T ∈ F) (heT : e ∈ T) (heR : e ∈ R) :
    T ∩ R = {e} := by
  obtain ⟨r, hr⟩ := card_eq_one.mp (hF T hT).2
  have he : e ∈ ({r} : Finset E) := hr ▸ mem_inter.mpr ⟨heT, heR⟩
  have her : e = r := mem_singleton.mp he
  subst e
  exact hr

/-- Different members of a packing have different singleton red intersections. -/
theorem IsPacking.red_inter_injective {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) {T U : Finset E}
    (hT : T ∈ P) (hU : U ∈ P) (heq : T ∩ R = U ∩ R) : T = U := by
  by_contra hne
  have hn : (T ∩ R).Nonempty := card_pos.mp (by rw [(hF T (hP.1 hT)).2]; decide)
  obtain ⟨e, he⟩ := hn
  have heU : e ∈ U ∩ R := heq ▸ he
  exact disjoint_left.mp (hP.2 hT hU hne) (mem_inter.mp he).1 (mem_inter.mp heU).1

theorem IsPacking.card_redEdges {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) :
    (redEdges R P).card = P.card := by
  rw [redEdges_eq_biUnion]
  have hd : (P : Set (Finset E)).Pairwise
      (fun T U => Disjoint (T ∩ R) (U ∩ R)) := by
    intro T hT U hU hne
    exact (hP.2 hT hU hne).mono inter_subset_left inter_subset_left
  rw [card_biUnion hd]
  calc
    ∑ T ∈ P, (T ∩ R).card = ∑ _T ∈ P, 1 := by
      apply sum_congr rfl
      intro T hT
      exact (hF T (hP.1 hT)).2
    _ = P.card := by simp

theorem IsPacking.card_blueEdges {F P : Finset (Finset E)} {R : Finset E}
    (hP : IsPacking F P) (hF : ColoredFamily F R) :
    (blueEdges R P).card = 2 * P.card := by
  have hsum := card_blueEdges_add_card_redEdges R P
  have hred := hP.card_redEdges hF
  have hsupport := hP.card_support_uniform (fun T hT => (hF T (hP.1 hT)).1)
  omega

/-- A residual member meets the parent support precisely in its unique red
edge. Maximality supplies a nonempty intersection; the color count identifies it. -/
theorem residual_inter_support_eq_inter_red {F P : Finset (Finset E)}
    {R T : Finset E} (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hT : T ∈ residual F (blueEdges R P)) : T ∩ support P = T ∩ R := by
  obtain ⟨hTF, hdis⟩ := mem_residual.mp hT
  have hsub : T ∩ support P ⊆ T ∩ R := by
    intro e he
    obtain ⟨heT, heP⟩ := mem_inter.mp he
    refine mem_inter.mpr ⟨heT, ?_⟩
    by_contra heR
    exact disjoint_left.mp hdis heT (mem_blueEdges.mpr ⟨heP, heR⟩)
  apply Subset.antisymm hsub
  intro e he
  obtain ⟨f, hf⟩ := hP.meets_support hTF (hF.member_nonempty hTF)
  have hsmall : (T ∩ R).card ≤ 1 := by rw [(hF T hTF).2]
  have hef : e = f := card_le_one.mp hsmall e he f (hsub hf)
  subst e
  exact hf

/-- The residual consists of the family members meeting the parent support
exactly in their red edge. -/
theorem mem_residual_blueEdges_iff {F P : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P) :
    T ∈ residual F (blueEdges R P) ↔ T ∈ F ∧ T ∩ support P = T ∩ R := by
  constructor
  · intro hT
    exact ⟨(mem_residual.mp hT).1, residual_inter_support_eq_inter_red hF hP hT⟩
  · rintro ⟨hTF, heq⟩
    refine mem_residual.mpr ⟨hTF, disjoint_left.mpr ?_⟩
    intro e heT heB
    obtain ⟨heP, heR⟩ := mem_blueEdges.mp heB
    have he : e ∈ T ∩ R := heq ▸ mem_inter.mpr ⟨heT, heP⟩
    exact heR (mem_inter.mp he).2

theorem residual_red_subset_parent_red {F P : Finset (Finset E)} {R T : Finset E}
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hT : T ∈ residual F (blueEdges R P)) : T ∩ R ⊆ redEdges R P := by
  intro e he
  have heP : e ∈ T ∩ support P :=
    (residual_inter_support_eq_inter_red hF hP hT).symm ▸ he
  exact mem_redEdges.mpr ⟨(mem_inter.mp heP).2, (mem_inter.mp he).2⟩

theorem IsPacking.redEdges_subset_parent {F P Q : Finset (Finset E)}
    {R : Finset E} (hQ : IsPacking (residual F (blueEdges R P)) Q)
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P) :
    redEdges R Q ⊆ redEdges R P := by
  intro e he
  obtain ⟨heQ, heR⟩ := mem_redEdges.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
  exact residual_red_subset_parent_red hF hP (hQ.1 hT)
    (mem_inter.mpr ⟨heT, heR⟩)

/-- Blue residual edges avoid the parent support. -/
theorem IsPacking.blueEdges_disjoint_parent_support {F P Q : Finset (Finset E)}
    {R : Finset E} (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Disjoint (blueEdges R Q) (support P) := by
  apply disjoint_left.mpr
  intro e heQ heP
  obtain ⟨heQ, heR⟩ := mem_blueEdges.mp heQ
  obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
  have hdis := (mem_residual.mp (hQ.1 hT)).2
  exact disjoint_left.mp hdis heT (mem_blueEdges.mpr ⟨heP, heR⟩)

theorem IsPacking.support_inter_parent_eq_redEdges {F P Q : Finset (Finset E)}
    {R : Finset E} (hQ : IsPacking (residual F (blueEdges R P)) Q)
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P) :
    support Q ∩ support P = redEdges R Q := by
  ext e
  constructor
  · intro he
    obtain ⟨heQ, heP⟩ := mem_inter.mp he
    refine mem_redEdges.mpr ⟨heQ, ?_⟩
    by_contra heR
    exact disjoint_left.mp hQ.blueEdges_disjoint_parent_support
      (mem_blueEdges.mpr ⟨heQ, heR⟩) heP
  · intro he
    exact mem_inter.mpr ⟨(mem_redEdges.mp he).1,
      (mem_redEdges.mp (hQ.redEdges_subset_parent hF hP he)).1⟩

/-- Packing members whose red edge occurs in no other member of the family. -/
noncomputable def privateRedPages (F : Finset (Finset E)) (R : Finset E)
    (P : Finset (Finset E)) : Finset (Finset E) := by
  classical
  exact P.filter (fun T => ∀ U ∈ F, U ∩ R = T ∩ R → U = T)

@[simp] theorem mem_privateRedPages {F P : Finset (Finset E)} {R T : Finset E} :
    T ∈ privateRedPages F R P ↔ T ∈ P ∧ ∀ U ∈ F, U ∩ R = T ∩ R → U = T := by
  classical
  simp [privateRedPages]

theorem privateRedPages_subset (F : Finset (Finset E)) (R : Finset E)
    (P : Finset (Finset E)) : privateRedPages F R P ⊆ P := by
  intro T hT
  exact (mem_privateRedPages.mp hT).1

/-- A cover may omit these private red edges if it contains the corresponding
blue edges. Only their own triangles could lose a selected red edge. -/
theorem IsCover.sdiff_privateRed {F P U : Finset (Finset E)} {R C : Finset E}
    (hC : IsCover F C) (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hU : U ⊆ privateRedPages F R P) (hblue : blueEdges R U ⊆ C) :
    IsCover F (C \ redEdges R U) := by
  intro T hT
  obtain ⟨e, he⟩ := hC T hT
  obtain ⟨heT, heC⟩ := mem_inter.mp he
  by_cases heU : e ∈ redEdges R U
  · obtain ⟨heSupport, heR⟩ := mem_redEdges.mp heU
    obtain ⟨S, hS, heS⟩ := mem_support.mp heSupport
    obtain ⟨hSP, hprivate⟩ := mem_privateRedPages.mp (hU hS)
    have hTS : T = S := hprivate T hT
      ((hF.red_eq_singleton hT heT heR).trans
        (hF.red_eq_singleton (hP.1 hSP) heS heR).symm)
    subst T
    have hblueCard := hF.member_blue_card (hP.1 hSP)
    obtain ⟨f, hf⟩ := card_pos.mp (show 0 < (S \ R).card by omega)
    obtain ⟨hfS, hfR⟩ := mem_sdiff.mp hf
    have hfC := hblue (mem_blueEdges.mpr ⟨mem_support.mpr ⟨S, hS, hfS⟩, hfR⟩)
    exact ⟨f, mem_inter.mpr ⟨hfS, mem_sdiff.mpr ⟨hfC,
      fun hfRed => hfR (mem_redEdges.mp hfRed).2⟩⟩⟩
  · exact ⟨e, mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heC, heU⟩⟩⟩

theorem card_sdiff_privateRed {F P U : Finset (Finset E)} {R C : Finset E}
    (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hU : U ⊆ privateRedPages F R P) (hred : redEdges R U ⊆ C) :
    (C \ redEdges R U).card + U.card = C.card := by
  have hpack := hP.subfamily (hU.trans (privateRedPages_subset F R P))
  have hcard := card_sdiff_add_card_inter C (redEdges R U)
  rw [inter_eq_right.mpr hred, hpack.card_redEdges hF] at hcard
  exact hcard

/-- The second colored cover is the parent blue edges and a residual maximum
packing, with every residual-private red edge deleted. -/
theorem second_colored_cover {F P Q : Finset (Finset E)} {R : Finset E}
    (hF : ColoredFamily F R) (hP : IsPacking F P)
    (hQ : IsMaximumPacking (residual F (blueEdges R P)) Q) :
    transversalNumber F + (privateRedPages (residual F (blueEdges R P)) R Q).card
      ≤ 2 * P.card + 3 * Q.card := by
  let S := residual F (blueEdges R P)
  let U := privateRedPages S R Q
  have hS : ColoredFamily S R := hF.residual
  have hU : U ⊆ privateRedPages S R Q := Subset.refl _
  have hUP : U ⊆ Q := privateRedPages_subset S R Q
  have hcover : IsCover S (support Q) :=
    hQ.support_covers (fun _ hT => hS.member_nonempty hT)
  have hblue : blueEdges R U ⊆ support Q :=
    (blueEdges_subset_support _ _).trans (support_mono hUP)
  have hred : redEdges R U ⊆ support Q :=
    (redEdges_subset_support _ _).trans (support_mono hUP)
  have hremoved := hcover.sdiff_privateRed hS hQ.1 hU hblue
  have hsize := card_sdiff_privateRed hS hQ.1 hU hred
  have hQsize := hQ.1.card_support_uniform (fun T hT => (hS T (hQ.1.1 hT)).1)
  have hPblue := hP.card_blueEdges hF
  have hbound := (cover_union_residual hremoved).number_le
  have hunion := card_union_le (blueEdges R P) (support Q \ redEdges R U)
  change transversalNumber F + U.card ≤ _
  omega

end TuzaBound
end

section
-- Wang: Colored.Family
/-! The complete family of triangles with one red edge. -/

namespace TuzaBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The complete family of triangles with exactly one red edge.
The ambient graph has edge set A; membership in R means red. -/
noncomputable def oneRedTriangles (A R : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (trianglesOn A).filter (fun T => (T ∩ R).card = 1)

@[simp] theorem mem_oneRedTriangles {A R T : Finset (Sym2 V)} :
    T ∈ oneRedTriangles A R ↔ IsTriangle T ∧ T ⊆ A ∧ (T ∩ R).card = 1 := by
  classical
  simp [oneRedTriangles, and_assoc]

theorem oneRedTriangles_colored (A R : Finset (Sym2 V)) :
    ColoredFamily (oneRedTriangles A R) R := by
  intro T hT
  obtain ⟨ht, _, hr⟩ := mem_oneRedTriangles.mp hT
  exact ⟨ht.card_eq_three, hr⟩

/-- Deleting any edge set preserves completeness of the colored family. -/
theorem oneRedTriangles_sdiff (A R C : Finset (Sym2 V)) :
    oneRedTriangles (A \ C) R = residual (oneRedTriangles A R) C := by
  classical
  ext T
  simp only [oneRedTriangles, mem_filter, trianglesOn_sdiff, mem_residual]
  tauto

theorem oneRedTriangles_subset {A R : Finset (Sym2 V)} :
    oneRedTriangles A R ⊆ trianglesOn A := by
  classical
  exact filter_subset _ _

end TuzaBound
end

section
-- Wang: Construction.Types
/-! Triangle types relative to the edges of a maximum packing. -/

namespace TuzaBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Type j means exactly j edges in the fixed old edge set O. -/
noncomputable def typeFamily (A O : Finset (Sym2 V)) (j : ℕ) :
    Finset (Finset (Sym2 V)) := by
  classical
  exact (trianglesOn A).filter (fun T => (T ∩ O).card = j)

@[simp] theorem mem_typeFamily {A O T : Finset (Sym2 V)} {j : ℕ} :
    T ∈ typeFamily A O j ↔ T ∈ trianglesOn A ∧ (T ∩ O).card = j := by
  classical
  simp [typeFamily]

theorem typeFamily_subset (A O : Finset (Sym2 V)) (j : ℕ) :
    typeFamily A O j ⊆ trianglesOn A := by
  classical
  exact filter_subset _ _

theorem typeFamily_sdiff (A O C : Finset (Sym2 V)) (j : ℕ) :
    typeFamily (A \ C) O j = residual (typeFamily A O j) C := by
  classical
  ext T
  simp only [typeFamily, mem_filter, trianglesOn_sdiff, mem_residual]
  tauto

theorem typeOne_colored (A O : Finset (Sym2 V)) :
    ColoredFamily (typeFamily A O 1) O := by
  intro T hT
  obtain ⟨ht, hc⟩ := mem_typeFamily.mp hT
  exact ⟨trianglesOn_card ht, hc⟩

/-- In a triangle, two old edges are equivalent to one new edge. -/
theorem typeTwo_eq_oneRed (A O : Finset (Sym2 V)) :
    typeFamily A O 2 = oneRedTriangles A (A \ O) := by
  ext T
  simp only [mem_typeFamily, mem_oneRedTriangles, mem_trianglesOn]
  constructor
  · rintro ⟨⟨hT, hsub⟩, hold⟩
    refine ⟨hT, hsub, ?_⟩
    have heq : T ∩ (A \ O) = T \ O := by
      ext e
      simp only [mem_inter, mem_sdiff]
      constructor
      · tauto
      · exact fun ⟨he, hno⟩ => ⟨he, hsub he, hno⟩
    rw [heq]
    have hpartition := card_sdiff_add_card_inter T O
    have hcard := hT.card_eq_three
    omega
  · rintro ⟨hT, hsub, hnew⟩
    refine ⟨⟨hT, hsub⟩, ?_⟩
    have heq : T ∩ (A \ O) = T \ O := by
      ext e
      simp only [mem_inter, mem_sdiff]
      constructor
      · tauto
      · exact fun ⟨he, hno⟩ => ⟨he, hsub he, hno⟩
    rw [heq] at hnew
    have hpartition := card_sdiff_add_card_inter T O
    have hcard := hT.card_eq_three
    omega

theorem typeTwo_colored (A O : Finset (Sym2 V)) :
    ColoredFamily (typeFamily A O 2) (A \ O) := by
  rw [typeTwo_eq_oneRed]
  exact oneRedTriangles_colored _ _

theorem new_edge_forces_typeTwo {A O T : Finset (Sym2 V)}
    (hT : T ∈ trianglesOn A) (hold : 2 ≤ (T ∩ O).card)
    {e : Sym2 V} (he : e ∈ T \ O) : T ∈ typeFamily A O 2 := by
  refine mem_typeFamily.mpr ⟨hT, ?_⟩
  have hnew : 0 < (T \ O).card := card_pos.mpr ⟨e, he⟩
  have hpartition := card_sdiff_add_card_inter T O
  have hcard := trianglesOn_card hT
  omega

theorem maximumPacking_old_nonempty {A : Finset (Sym2 V)}
    {P : Finset (Finset (Sym2 V))} (hP : IsMaximumPacking (trianglesOn A) P)
    {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn A) :
    1 ≤ (T ∩ support P).card := by
  exact card_pos.mpr (hP.meets_support hT (trianglesOn_nonempty hT))

/-- After deleting a maximum packing of type-1 triangles, every remaining
triangle has at least two old edges. -/
theorem old_card_ge_two_after_typeOne {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsMaximumPacking (typeFamily A (support P) 1) Q)
    {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn (A \ support Q)) :
    2 ≤ (T ∩ support P).card := by
  rw [trianglesOn_sdiff] at hT
  obtain ⟨ht, hd⟩ := mem_residual.mp hT
  have hpos := maximumPacking_old_nonempty hP ht
  by_contra hn
  have hone : (T ∩ support P).card = 1 := by omega
  have htype : T ∈ typeFamily A (support P) 1 := mem_typeFamily.mpr ⟨ht, hone⟩
  obtain ⟨e, he⟩ := hQ.meets_support htype (trianglesOn_nonempty ht)
  exact disjoint_left.mp hd (mem_inter.mp he).1 (mem_inter.mp he).2

/-- The old edges left after deleting the type-1 packing are counted exactly. -/
theorem remaining_old_card {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (support P \ support Q).card + Q.card = 3 * P.card := by
  have hred := hQ.card_redEdges (typeOne_colored A (support P))
  have hpartition := card_sdiff_add_card_inter (support P) (support Q)
  have hp := hP.card_support_uniform (fun T hT => trianglesOn_card (hP.1 hT))
  change (support Q ∩ support P).card = Q.card at hred
  rw [inter_comm] at hred
  omega

/-- A packing in the remaining graph can be combined with the deleted packing. -/
theorem deleted_packing_card_add_le {A : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (trianglesOn (A \ support P)) Q) :
    P.card + Q.card ≤ packingNumber (trianglesOn A) := by
  have hQ' : IsPacking (trianglesOn A) Q :=
    hQ.mono_family (trianglesOn_mono sdiff_subset)
  have hd : Disjoint (support P) (support Q) := by
    apply disjoint_left.mpr
    intro e heP heQ
    obtain ⟨T, hT, heT⟩ := mem_support.mp heQ
    exact (mem_sdiff.mp ((mem_trianglesOn.mp (hQ.1 hT)).2 heT)).2 heP
  have hPQ := hP.union hQ' hd
  have hdis := disjoint_of_support_disjoint
    (fun T hT => trianglesOn_nonempty (hP.1 hT)) hd
  simpa [card_union_of_disjoint hdis] using hPQ.card_le

end TuzaBound
end

section
-- Wang: Books.Families
/-! Finite page choices in books. -/

namespace TuzaBound

namespace Books

open Finset

variable {E I : Type*} [DecidableEq E] [Fintype I]

/-- One page is selected for each index. -/
def ChoosesPages (pages : I → Finset (Finset E)) (f : I → Finset E) : Prop :=
  ∀ i, f i ∈ pages i

/-- The family obtained by choosing one page from each book. -/
def choice (f : I → Finset E) : Finset (Finset E) :=
  Finset.univ.image f

@[simp] theorem mem_choice {f : I → Finset E} {T : Finset E} :
    T ∈ choice f ↔ ∃ i, f i = T := by
  simp [choice]

/-- Distinct books may share original vertices, but not edges. -/
def DisjointSupports (pages : I → Finset (Finset E)) : Prop :=
  Pairwise (fun i j => Disjoint (support (pages i)) (support (pages j)))

omit [Fintype I] in
theorem page_subset_support {pages : I → Finset (Finset E)} {i : I}
    {T : Finset E} (hT : T ∈ pages i) : T ⊆ support (pages i) := by
  intro e he
  exact mem_support.mpr ⟨T, hT, he⟩

omit [DecidableEq E] [Fintype I] in
theorem exists_choice {pages : I → Finset (Finset E)}
    (hne : ∀ i, (pages i).Nonempty) :
    ∃ f, ChoosesPages pages f := by
  classical
  choose f hf using hne
  exact ⟨f, hf⟩

omit [Fintype I] in
theorem choices_pairwise_disjoint {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages) {f : I → Finset E}
    (hf : ChoosesPages pages f) : Pairwise (fun i j => Disjoint (f i) (f j)) := by
  intro i j hij
  exact (hd hij).mono (page_subset_support (hf i)) (page_subset_support (hf j))

omit [Fintype I] in
/-- Nonempty pages in different books cannot become the same chosen page. -/
theorem choice_injective {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty) {f : I → Finset E}
    (hf : ChoosesPages pages f) : Function.Injective f := by
  intro i j hij
  by_contra hneij
  have hdis := choices_pairwise_disjoint hd hf hneij
  obtain ⟨e, he⟩ := hne i (f i) (hf i)
  exact Finset.disjoint_left.mp hdis he (hij ▸ he)

theorem card_choice {pages : I → Finset (Finset E)}
    (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty) {f : I → Finset E}
    (hf : ChoosesPages pages f) : (choice f).card = Fintype.card I := by
  rw [choice, Finset.card_image_of_injective _ (choice_injective hd hne hf)]
  exact Finset.card_univ

/-- Every page choice is a packing when all pages belong to the family and
the supports of distinct books are disjoint. -/
theorem choice_isPacking {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hF : ∀ i, pages i ⊆ F) (hd : DisjointSupports pages)
    {f : I → Finset E} (hf : ChoosesPages pages f) :
    IsPacking F (choice f) := by
  refine ⟨?_, ?_⟩
  · intro T hT
    obtain ⟨i, rfl⟩ := mem_choice.mp hT
    exact hF i (hf i)
  · intro T hT U hU hTU
    obtain ⟨i, rfl⟩ := mem_choice.mp hT
    obtain ⟨j, rfl⟩ := mem_choice.mp hU
    apply choices_pairwise_disjoint hd hf
    intro hij
    exact hTU (congrArg f hij)

/-- A known upper bound on every packing makes all full page choices maximum. -/
theorem choice_isMaximumPacking {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hF : ∀ i, pages i ⊆ F) (hd : DisjointSupports pages)
    (hne : ∀ i T, T ∈ pages i → T.Nonempty)
    (hbound : ∀ P, IsPacking F P → P.card ≤ Fintype.card I)
    {f : I → Finset E} (hf : ChoosesPages pages f) :
    IsMaximumPacking F (choice f) := by
  refine ⟨choice_isPacking hF hd hf, ?_⟩
  intro P hP
  rw [card_choice hd hne hf]
  exact hbound P hP

/-- Every page choice meets each member of the family. -/
def EveryChoiceMeets (F : Finset (Finset E))
    (pages : I → Finset (Finset E)) : Prop :=
  ∀ f, ChoosesPages pages f → ∀ T ∈ F, ∃ i, ¬ Disjoint T (f i)

/-- Maximum page choices give the required maximality when family members
are nonempty. -/
theorem everyChoiceMeets_of_maximum {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hne : ∀ T ∈ F, T.Nonempty)
    (hmax : ∀ f, ChoosesPages pages f → IsMaximumPacking F (choice f)) :
    EveryChoiceMeets F pages := by
  intro f hf T hT
  obtain ⟨e, he⟩ := (hmax f hf).meets_support hT (hne T hT)
  obtain ⟨U, hU, heU⟩ := mem_support.mp (Finset.mem_inter.mp he).2
  obtain ⟨i, rfl⟩ := mem_choice.mp hU
  refine ⟨i, ?_⟩
  intro hdis
  exact Finset.disjoint_left.mp hdis (Finset.mem_inter.mp he).1 heU

/-- If every full page choice meets a family member, one book has all its
pages meeting that member. -/
theorem exists_book_all_pages_meet {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)} (hchoice : EveryChoiceMeets F pages)
    {T : Finset E} (hT : T ∈ F) :
    ∃ i, ∀ U ∈ pages i, ¬ Disjoint T U := by
  classical
  by_contra hnone
  push Not at hnone
  choose f hf hdis using hnone
  obtain ⟨i, hi⟩ := hchoice f hf T hT
  exact hi (hdis i)

theorem exists_book_all_pages_meet_of_maximum {F : Finset (Finset E)}
    {pages : I → Finset (Finset E)}
    (hne : ∀ T ∈ F, T.Nonempty)
    (hmax : ∀ f, ChoosesPages pages f → IsMaximumPacking F (choice f))
    {T : Finset E} (hT : T ∈ F) :
    ∃ i, ∀ U ∈ pages i, ¬ Disjoint T U :=
  exists_book_all_pages_meet (everyChoiceMeets_of_maximum hne hmax) hT

end Books

end TuzaBound
end

section
-- Wang: Books.Cover
/-!
Books with one to three pages and their covers: Lemma 2.2.

A two-page cover includes the opposite vertex pair. Restricting the cover to the
graph's edges preserves coverage and can only reduce its size.
-/

namespace TuzaBound

open Finset
open scoped BigOperators

variable {V : Type*}

/-- Books with one, two, or three distinct pages and their actual vertices. -/
inductive Book (V : Type*) where
  | single (u v x : V) (vertices : [u, v, x].Nodup)
  | double (u v x y : V) (vertices : [u, v, x, y].Nodup)
  | triple (u v x y z : V) (vertices : [u, v, x, y, z].Nodup)

namespace Book

def spine : Book V → Sym2 V
  | .single u v _ _ => s(u, v)
  | .double u v _ _ _ => s(u, v)
  | .triple u v _ _ _ _ => s(u, v)

/-- Only a two-page book has an opposite edge relevant to its cover. -/
def opposite : Book V → Option (Sym2 V)
  | .single .. => none
  | .double _ _ x y _ => some s(x, y)
  | .triple .. => none

def pageCount : Book V → ℕ
  | .single .. => 1
  | .double .. => 2
  | .triple .. => 3

variable [DecidableEq V]

def pages : Book V → Finset (Finset (Sym2 V))
  | .single u v x _ => {triangleEdges u v x}
  | .double u v x y _ => {triangleEdges u v x, triangleEdges u v y}
  | .triple u v x y z _ =>
      {triangleEdges u v x, triangleEdges u v y, triangleEdges u v z}

def cover : Book V → Finset (Sym2 V)
  | .single u v x _ => triangleEdges u v x
  | .double u v x y _ => {s(u, v), s(x, y)}
  | .triple u v _ _ _ _ => {s(u, v)}

omit [DecidableEq V] in
@[simp] theorem opposite_double (u v x y : V) (h : [u, v, x, y].Nodup) :
    (Book.double u v x y h).opposite = some s(x, y) := rfl

@[simp] theorem cover_double (u v x y : V) (h : [u, v, x, y].Nodup) :
    (Book.double u v x y h).cover = {s(u, v), s(x, y)} := rfl

private theorem wBooksCover_pages_ne {u v x y : V} (h : [u, v, x, y].Nodup) :
    triangleEdges u v x ≠ triangleEdges u v y := by
  have hd : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using h
  intro heq
  have hx : s(u, x) ∈ triangleEdges u v y := heq ▸ (by simp)
  simp only [mem_triangleEdges, Sym2.eq_iff] at hx
  aesop

theorem pages_nonempty (b : Book V) : b.pages.Nonempty := by
  cases b <;> simp [pages]

theorem pages_card (b : Book V) : b.pages.card = b.pageCount := by
  cases b with
  | single u v x h => simp [pages, pageCount]
  | double u v x y h => simp [pages, pageCount, wBooksCover_pages_ne h]
  | triple u v x y z h =>
    have hxy : [u, v, x, y].Nodup := by simp_all [List.nodup_cons]
    have hxz : [u, v, x, z].Nodup := by simp_all [List.nodup_cons]
    have hyz : [u, v, y, z].Nodup := by simp_all [List.nodup_cons]
    simp [pages, pageCount, wBooksCover_pages_ne hxy, wBooksCover_pages_ne hxz, wBooksCover_pages_ne hyz]

theorem pages_card_le_three (b : Book V) : b.pages.card ≤ 3 := by
  rw [pages_card]
  cases b <;> simp [pageCount]

theorem page_isTriangle (b : Book V) {T : Finset (Sym2 V)} (hT : T ∈ b.pages) :
    IsTriangle T := by
  cases b with
  | single u v x h =>
    simp only [pages, mem_singleton] at hT
    subst T
    apply isTriangle_triangleEdges <;> simp_all [List.nodup_cons]
  | double u v x y h =>
    simp only [pages, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl <;>
      apply isTriangle_triangleEdges <;> simp_all [List.nodup_cons]
  | triple u v x y z h =>
    simp only [pages, mem_insert, mem_singleton] at hT
    rcases hT with rfl | rfl | rfl <;>
      apply isTriangle_triangleEdges <;> simp_all [List.nodup_cons]

theorem spine_mem_page (b : Book V) {T : Finset (Sym2 V)} (hT : T ∈ b.pages) :
    b.spine ∈ T := by
  cases b <;> simp_all [pages, spine] <;> aesop

theorem cover_card_add_pages_card_le_four (b : Book V) :
    b.cover.card + b.pages.card ≤ 4 := by
  rw [pages_card]
  cases b with
  | single u v x h =>
    have huv : u ≠ v := by simp_all [List.nodup_cons]
    have hux : u ≠ x := by simp_all [List.nodup_cons]
    have hvx : v ≠ x := by simp_all [List.nodup_cons]
    simp [cover, pageCount, triangleEdges_card huv hux hvx]
  | double u v x y h =>
    have hc : ({s(u, v), s(x, y)} : Finset (Sym2 V)).card ≤ 2 := card_le_two
    simp only [cover, pageCount]
    omega
  | triple u v x y z h => simp [cover, pageCount]

/-- Meeting every page of an actual book forces a triangle to meet its cover. -/
theorem meets_cover (b : Book V) {T : Finset (Sym2 V)} (hT : IsTriangle T)
    (hmeet : ∀ U ∈ b.pages, (T ∩ U).Nonempty) : (T ∩ b.cover).Nonempty := by
  cases b with
  | single u v x h => exact hmeet (triangleEdges u v x) (by simp [pages])
  | double u v x y h =>
    by_cases he : s(u, v) ∈ T
    · exact ⟨s(u, v), mem_inter.mpr ⟨he, by simp [cover]⟩⟩
    · have hop := two_page_opposite_mem hT h he
        (hmeet (triangleEdges u v x) (by simp [pages]))
        (hmeet (triangleEdges u v y) (by simp [pages]))
      exact ⟨s(x, y), mem_inter.mpr ⟨hop, by simp [cover]⟩⟩
  | triple u v x y z h =>
    have he := three_page_spine hT h
      (hmeet (triangleEdges u v x) (by simp [pages]))
      (hmeet (triangleEdges u v y) (by simp [pages]))
      (hmeet (triangleEdges u v z) (by simp [pages]))
    exact ⟨s(u, v), mem_inter.mpr ⟨he, by simp [cover]⟩⟩

theorem meets_cover_of_not_disjoint (b : Book V) {T : Finset (Sym2 V)}
    (hT : IsTriangle T) (hmeet : ∀ U ∈ b.pages, ¬ Disjoint T U) :
    (T ∩ b.cover).Nonempty := by
  apply b.meets_cover hT
  intro U hU
  obtain ⟨e, heT, heU⟩ := not_disjoint_iff.mp (hmeet U hU)
  exact ⟨e, mem_inter.mpr ⟨heT, heU⟩⟩

/-- Every nonempty family of at most three actual triangles with a common edge
has one of the three book representations above, with that precise spine. -/
theorem exists_representation (S : Finset (Finset (Sym2 V))) (e : Sym2 V)
    (hne : S.Nonempty) (hcard : S.card ≤ 3)
    (htri : ∀ T ∈ S, IsTriangle T) (hspine : ∀ T ∈ S, e ∈ T) :
    ∃ b : Book V, b.pages = S ∧ b.spine = e := by
  obtain ⟨u, v, rfl⟩ : ∃ u v, e = s(u, v) :=
    Sym2.inductionOn e (fun u v => ⟨u, v, rfl⟩)
  have huv : u ≠ v := by
    obtain ⟨T, hT⟩ := hne
    exact (htri T hT).ne_of_mem (hspine T hT)
  have hr (T : Finset (Sym2 V)) (hT : T ∈ S) :
      ∃ x, u ≠ x ∧ v ≠ x ∧ T = triangleEdges u v x :=
    (htri T hT).exists_third_of_mem (hspine T hT)
  have hcpos : 0 < S.card := card_pos.mpr hne
  have hc : S.card = 1 ∨ S.card = 2 ∨ S.card = 3 := by omega
  rcases hc with hc | hc | hc
  · obtain ⟨T, rfl⟩ := card_eq_one.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    have hv : [u, v, x].Nodup := by simp [List.nodup_cons, huv, hux, hvx]
    exact ⟨.single u v x hv, rfl, rfl⟩
  · obtain ⟨T, U, hTU, rfl⟩ := card_eq_two.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    obtain ⟨y, huy, hvy, rfl⟩ := hr U (by simp)
    have hxy : x ≠ y := by rintro rfl; exact hTU rfl
    have hv : [u, v, x, y].Nodup := by
      simp [List.nodup_cons, huv, hux, huy, hvx, hvy, hxy]
    exact ⟨.double u v x y hv, rfl, rfl⟩
  · obtain ⟨T, U, W, hTU, hTW, hUW, rfl⟩ := card_eq_three.mp hc
    obtain ⟨x, hux, hvx, rfl⟩ := hr T (by simp)
    obtain ⟨y, huy, hvy, rfl⟩ := hr U (by simp)
    obtain ⟨z, huz, hvz, rfl⟩ := hr W (by simp)
    have hxy : x ≠ y := by rintro rfl; exact hTU rfl
    have hxz : x ≠ z := by rintro rfl; exact hTW rfl
    have hyz : y ≠ z := by rintro rfl; exact hUW rfl
    have hv : [u, v, x, y, z].Nodup := by
      simp [List.nodup_cons, huv, hux, huy, huz, hvx, hvy, hvz, hxy, hxz, hyz]
    exact ⟨.triple u v x y z hv, rfl, rfl⟩

theorem pages_card_of_opposite {b : Book V} {e : Sym2 V}
    (hop : b.opposite = some e) : b.pages.card = 2 := by
  rw [b.pages_card]
  cases b <;> simp_all [Book.opposite, Book.pageCount]

end Book

variable [DecidableEq V] {I : Type*} [Fintype I]

/-- The union of the actual per-book covers, counting repeated edges only once. -/
def bookFamilyCover (books : I → Book V) : Finset (Sym2 V) :=
  univ.biUnion (fun i => (books i).cover)

theorem bookFamilyCover_covers (books : I → Book V)
    (F : Finset (Finset (Sym2 V))) (htri : ∀ T ∈ F, IsTriangle T)
    (hmeet : ∀ T ∈ F, ∃ i, ∀ U ∈ (books i).pages, ¬ Disjoint T U) :
    IsCover F (bookFamilyCover books) := by
  intro T hT
  obtain ⟨i, hi⟩ := hmeet T hT
  obtain ⟨e, he⟩ := (books i).meets_cover_of_not_disjoint (htri T hT) hi
  exact ⟨e, mem_inter.mpr ⟨(mem_inter.mp he).1,
    mem_biUnion.mpr ⟨i, mem_univ _, (mem_inter.mp he).2⟩⟩⟩

theorem bookFamilyCover_card (books : I → Book V) :
    (bookFamilyCover books).card + (∑ i, (books i).pages.card) ≤
      4 * Fintype.card I := by
  have hu : (bookFamilyCover books).card ≤ ∑ i, (books i).cover.card :=
    card_biUnion_le
  have hs : (∑ i, (books i).cover.card) + (∑ i, (books i).pages.card) ≤
      4 * Fintype.card I := by
    rw [← sum_add_distrib]
    calc
      (∑ i, ((books i).cover.card + (books i).pages.card)) ≤ ∑ _i : I, 4 :=
        sum_le_sum (fun i _ => (books i).cover_card_add_pages_card_le_four)
      _ = 4 * Fintype.card I := by simp [Nat.mul_comm]
  omega

/-- Represent each page family as a book and combine the book covers. -/
theorem exists_cover_of_small_common_spine_books
    (F : Finset (Finset (Sym2 V))) (pages : I → Finset (Finset (Sym2 V)))
    (hne : ∀ i, (pages i).Nonempty) (hcard : ∀ i, (pages i).card ≤ 3)
    (hpages : ∀ i T, T ∈ pages i → IsTriangle T)
    (hspine : ∀ i, ∃ e, ∀ T ∈ pages i, e ∈ T)
    (htri : ∀ T ∈ F, IsTriangle T) (hchoice : Books.EveryChoiceMeets F pages) :
    ∃ C : Finset (Sym2 V), IsCover F C ∧
      C.card + (∑ i, (pages i).card) ≤ 4 * Fintype.card I := by
  classical
  choose spine hs using hspine
  have hb (i : I) : ∃ b : Book V, b.pages = pages i ∧ b.spine = spine i :=
    Book.exists_representation (pages i) (spine i) (hne i) (hcard i) (hpages i) (hs i)
  choose books hbpages hbspine using hb
  refine ⟨bookFamilyCover books, ?_, ?_⟩
  · apply bookFamilyCover_covers books F htri
    intro T hT
    obtain ⟨i, hi⟩ := Books.exists_book_all_pages_meet hchoice hT
    exact ⟨i, by simpa only [hbpages i] using hi⟩
  · simpa only [hbpages] using bookFamilyCover_card books

end TuzaBound
end

section
-- Wang: Construction.FirstCover
/-!
The first book cover uses a maximum packing and a packing of type-1 triangles.
A two-for-one exchange shows that distinct type-1 pages have distinct parents.
-/

namespace TuzaBound
namespace FirstCover

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : Finset (Sym2 V)} {P Q : Finset (Finset (Sym2 V))}

def children (P Q : Finset (Finset (Sym2 V))) (p : Finset (Sym2 V)) :
    Finset (Finset (Sym2 V)) := Q.filter (fun q => q ∩ support P ⊆ p)

def pages (P Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ P}) :
    Finset (Finset (Sym2 V)) := insert p.val (children P Q p.val)

omit [Fintype V] in
@[simp] theorem mem_children {p q : Finset (Sym2 V)} :
    q ∈ children P Q p ↔ q ∈ Q ∧ q ∩ support P ⊆ p := by
  simp [children]

omit [Fintype V] in
@[simp] theorem mem_pages {p : {T // T ∈ P}} {T : Finset (Sym2 V)} :
    T ∈ pages P Q p ↔ T = p.val ∨ (T ∈ Q ∧ T ∩ support P ⊆ p.val) := by
  simp [pages]

theorem old_inter_nonempty (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {q : Finset (Sym2 V)} (hq : q ∈ Q) : (q ∩ support P).Nonempty := by
  apply card_pos.mp
  rw [(mem_typeFamily.mp (hQ.1 hq)).2]
  decide

theorem exists_parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : ∃ p : {T // T ∈ P}, q.val ∩ support P ⊆ p.val := by
  obtain ⟨e, heq⟩ := card_eq_one.mp (mem_typeFamily.mp (hQ.1 q.property)).2
  have he : e ∈ q.val ∩ support P := by rw [heq]; simp
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_inter.mp he).2
  refine ⟨⟨p, hp⟩, ?_⟩
  rw [heq]
  exact singleton_subset_iff.mpr hep

noncomputable def parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : {T // T ∈ P} := Classical.choose (exists_parent hQ q)

theorem parent_spec (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (q : {T // T ∈ Q}) : q.val ∩ support P ⊆ (parent hQ q).val :=
  Classical.choose_spec (exists_parent hQ q)

theorem owner_unique (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) {q : Finset (Sym2 V)}
    (hq : q ∈ Q) (p p' : {T // T ∈ P})
    (hp : q ∩ support P ⊆ p.val) (hp' : q ∩ support P ⊆ p'.val) : p = p' := by
  by_contra hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  obtain ⟨e, he⟩ := old_inter_nonempty hQ hq
  exact disjoint_left.mp (hP.2 p.property p'.property hval) (hp he) (hp' he)

theorem parent_unique (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (q : {T // T ∈ Q})
    (p : {T // T ∈ P}) (hp : q.val ∩ support P ⊆ p.val) : p = parent hQ q :=
  owner_unique hP hQ q.property p (parent hQ q) hp (parent_spec hQ q)

theorem parent_injective (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Function.Injective (parent hQ) := by
  intro q q' heq
  by_contra hne
  have hval : q.val ≠ q'.val := fun h => hne (Subtype.ext h)
  have hqt := (mem_typeFamily.mp (hQ.1 q.property)).1
  have hq't := (mem_typeFamily.mp (hQ.1 q'.property)).1
  have havoid : Disjoint q.val (support (P.erase (parent hQ q).val)) := by
    apply hP.1.disjoint_support_erase (parent hQ q).property
    intro e heq heP
    exact parent_spec hQ q (mem_inter.mpr ⟨heq, heP⟩)
  have havoid' : Disjoint q'.val (support (P.erase (parent hQ q).val)) := by
    apply hP.1.disjoint_support_erase (parent hQ q).property
    intro e heq' heP
    have h := parent_spec hQ q' (mem_inter.mpr ⟨heq', heP⟩)
    simpa only [← heq] using h
  exact hP.no_two_for_one (parent hQ q).property hqt hq't
    (trianglesOn_nonempty hqt) (trianglesOn_nonempty hq't)
    (hQ.2 q.property q'.property hval) havoid havoid'

theorem child_not_parent (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {q : Finset (Sym2 V)} (hq : q ∈ Q) : q ∉ P := by
  intro hp
  have heq : q ∩ support P = q := by
    apply inter_eq_left.mpr
    intro e he
    exact mem_support.mpr ⟨q, hp, he⟩
  have hc := (mem_typeFamily.mp (hQ.1 hq)).2
  have ht := trianglesOn_card (mem_typeFamily.mp (hQ.1 hq)).1
  rw [heq] at hc
  omega

theorem children_card_le_one (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    (children P Q p.val).card ≤ 1 := by
  apply card_le_one.mpr
  intro q hq q' hq'
  obtain ⟨hqQ, hqp⟩ := mem_children.mp hq
  obtain ⟨hq'Q, hq'p⟩ := mem_children.mp hq'
  have h₁ := parent_unique hP.1 hQ ⟨q, hqQ⟩ p hqp
  have h₂ := parent_unique hP.1 hQ ⟨q', hq'Q⟩ p hq'p
  exact congrArg Subtype.val (parent_injective hP hQ (h₁.symm.trans h₂))

theorem parent_not_child (hQ : IsPacking (typeFamily A (support P) 1) Q)
    (p : {T // T ∈ P}) : p.val ∉ children P Q p.val := by
  intro hp
  exact child_not_parent hQ (mem_children.mp hp).1 p.property

omit [Fintype V] in
theorem pages_nonempty (P Q : Finset (Finset (Sym2 V))) (p : {T // T ∈ P}) :
    (pages P Q p).Nonempty := ⟨p.val, mem_insert_self _ _⟩

theorem pages_subset_family (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    pages P Q p ⊆ trianglesOn A := by
  intro T hT
  rcases mem_pages.mp hT with rfl | ⟨hTQ, _⟩
  · exact hP.1 p.property
  · exact (mem_typeFamily.mp (hQ.1 hTQ)).1

theorem pages_card_le_two (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    (pages P Q p).card ≤ 2 := by
  have hle := children_card_le_one hP hQ p
  rw [pages, card_insert_of_notMem (parent_not_child hQ p)]
  omega

theorem book_inter_parent_subset (_hQ : IsPacking (typeFamily A (support P) 1) Q)
    (p : {T // T ∈ P}) : support (pages P Q p) ∩ support P ⊆ p.val := by
  intro e he
  obtain ⟨heb, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp heb
  rcases mem_pages.mp hT with rfl | ⟨_, hsub⟩
  · exact heT
  · exact hsub (mem_inter.mpr ⟨heT, heP⟩)

theorem supports_disjoint (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Books.DisjointSupports (pages P Q) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hd := hP.1.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases mem_pages.mp hT with rfl | ⟨hTQ, hsubT⟩
  · have hep' := book_inter_parent_subset hQ p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hd heT hep'
  · rcases mem_pages.mp hU with rfl | ⟨hUQ, hsubU⟩
    · have hep := book_inter_parent_subset hQ p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hd hep heU
    · have hTU : T ≠ U := by
        intro hEq
        subst U
        exact hne (owner_unique hP.1 hQ hTQ p p' hsubT hsubU)
      exact disjoint_left.mp (hQ.2 hTQ hUQ hTU) heT heU

theorem choices_maximum (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q)
    {f : {T // T ∈ P} → Finset (Sym2 V)} (hf : Books.ChoosesPages (pages P Q) f) :
    IsMaximumPacking (trianglesOn A) (Books.choice f) := by
  apply Books.choice_isMaximumPacking (pages_subset_family hP.1 hQ)
    (supports_disjoint hP hQ)
    (fun p T hT => trianglesOn_nonempty (pages_subset_family hP.1 hQ p hT)) ?_ hf
  intro K hK
  simpa using hP.2 K hK

theorem everyChoiceMeets (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Books.EveryChoiceMeets (trianglesOn A) (pages P Q) :=
  Books.everyChoiceMeets_of_maximum (fun _ hT => trianglesOn_nonempty hT)
    (fun _ hf => choices_maximum hP hQ hf)

theorem children_pairwise_disjoint (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    Pairwise (fun p p' : {T // T ∈ P} =>
      Disjoint (children P Q p.val) (children P Q p'.val)) := by
  intro p p' hne
  apply disjoint_left.mpr
  intro q hq hq'
  obtain ⟨hqQ, hsub⟩ := mem_children.mp hq
  obtain ⟨_, hsub'⟩ := mem_children.mp hq'
  exact hne (owner_unique hP hQ hqQ p p' hsub hsub')

theorem children_biUnion (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    univ.biUnion (fun p : {T // T ∈ P} => children P Q p.val) = Q := by
  ext q
  constructor
  · intro hq
    obtain ⟨p, _, hp⟩ := mem_biUnion.mp hq
    exact (mem_children.mp hp).1
  · intro hq
    exact mem_biUnion.mpr ⟨parent hQ ⟨q, hq⟩, mem_univ _,
      mem_children.mpr ⟨hq, parent_spec hQ ⟨q, hq⟩⟩⟩

theorem sum_children_card (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (∑ p : {T // T ∈ P}, (children P Q p.val).card) = Q.card := by
  conv_rhs => rw [← children_biUnion hQ]
  symm
  apply card_biUnion
  intro p _ p' _ hne
  exact children_pairwise_disjoint hP hQ hne

theorem sum_pages_card (hP : IsPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    (∑ p : {T // T ∈ P}, (pages P Q p).card) = P.card + Q.card := by
  have hc : ∀ p : {T // T ∈ P}, (pages P Q p).card = (children P Q p.val).card + 1 := by
    intro p
    exact card_insert_of_notMem (parent_not_child hQ p)
  calc
    (∑ p : {T // T ∈ P}, (pages P Q p).card) =
        ∑ p : {T // T ∈ P}, ((children P Q p.val).card + 1) := sum_congr rfl (fun p _ => hc p)
    _ = P.card + Q.card := by rw [sum_add_distrib, sum_children_card hP hQ]; simp [Nat.add_comm]

theorem pages_common_edge (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) (p : {T // T ∈ P}) :
    ∃ e, ∀ T ∈ pages P Q p, e ∈ T := by
  by_cases hn : (children P Q p.val).Nonempty
  · obtain ⟨q, hq⟩ := hn
    obtain ⟨hqQ, hsubq⟩ := mem_children.mp hq
    obtain ⟨e, he⟩ := old_inter_nonempty hQ hqQ
    refine ⟨e, ?_⟩
    intro T hT
    rcases mem_pages.mp hT with rfl | ⟨hTQ, hsubT⟩
    · exact hsubq he
    · have hTchild := mem_children.mpr ⟨hTQ, hsubT⟩
      have hTq : T = q := card_le_one.mp (children_card_le_one hP hQ p) T hTchild q hq
      subst T
      exact (mem_inter.mp he).1
  · have hempty := not_nonempty_iff_eq_empty.mp hn
    obtain ⟨e, he⟩ := trianglesOn_nonempty (hP.1.1 p.property)
    refine ⟨e, ?_⟩
    intro T hT
    have ht : T = p.val := by simpa [pages, hempty] using hT
    subst T
    exact he

/-- The first cover saves one edge for every packed type-1 triangle. -/
theorem exists_first_cover (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    ∃ C : Finset (Sym2 V), IsCover (trianglesOn A) C ∧ C.card + Q.card ≤ 3 * P.card := by
  obtain ⟨C, hC, hbound⟩ := exists_cover_of_small_common_spine_books
    (trianglesOn A) (pages P Q) (pages_nonempty P Q)
    (fun p => (pages_card_le_two hP hQ p).trans (by decide))
    (fun p T hT => (mem_trianglesOn.mp (pages_subset_family hP.1 hQ p hT)).1)
    (pages_common_edge hP hQ) (fun T hT => (mem_trianglesOn.mp hT).1)
    (everyChoiceMeets hP hQ)
  rw [sum_pages_card hP.1 hQ] at hbound
  simp only [Fintype.card_coe] at hbound
  exact ⟨C, hC, by omega⟩

theorem transversalNumber_add_typeOne_packing_le (hP : IsMaximumPacking (trianglesOn A) P)
    (hQ : IsPacking (typeFamily A (support P) 1) Q) :
    transversalNumber (trianglesOn A) + Q.card ≤ 3 * P.card := by
  obtain ⟨C, hC, hbound⟩ := exists_first_cover hP hQ
  have ht := hC.number_le
  omega

end FirstCover
end TuzaBound
end

section
-- Wang: Construction.Setup
/-! Haxell's packing construction and the complete residual colored family. -/

namespace TuzaBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The three packing choices made before constructing the residual family.
`initial`, `first`, and `rest` are the paper's P, A, and P', respectively. -/
structure Construction (edges : Finset (Sym2 V)) where
  initial : Finset (Finset (Sym2 V))
  initial_maximum : IsMaximumPacking (trianglesOn edges) initial
  first : Finset (Finset (Sym2 V))
  first_maximum : IsMaximumPacking (typeFamily edges (support initial) 1) first
  rest : Finset (Finset (Sym2 V))
  rest_lexMaximum : IsLexMaximumPacking (trianglesOn (edges \ support first))
    (typeFamily (edges \ support first) (support initial) 2) rest

theorem exists_construction (edges : Finset (Sym2 V)) : Nonempty (Construction edges) := by
  obtain ⟨P, hP⟩ := exists_maximumPacking (trianglesOn edges)
  obtain ⟨A, hA⟩ := exists_maximumPacking (typeFamily edges (support P) 1)
  obtain ⟨P', hP'⟩ := exists_lexMaximumPacking (trianglesOn (edges \ support A))
    (typeFamily (edges \ support A) (support P) 2)
  exact ⟨⟨P, hP, A, hA, P', hP'⟩⟩

namespace Construction

variable {edges : Finset (Sym2 V)} (c : Construction edges)

def old : Finset (Sym2 V) := support c.initial
def remainingEdges : Finset (Sym2 V) := edges \ support c.first
def oldRemaining : Finset (Sym2 V) := c.old \ support c.first
noncomputable def typeTwo : Finset (Finset (Sym2 V)) :=
  c.rest ∩ typeFamily c.remainingEdges c.old 2
def newEdges : Finset (Sym2 V) := support c.rest \ c.old

theorem first_packing : IsPacking (trianglesOn edges) c.first :=
  c.first_maximum.1.mono_family (typeFamily_subset _ _ _)

theorem rest_packing : IsPacking (trianglesOn c.remainingEdges) c.rest :=
  c.rest_lexMaximum.1

theorem old_subset_edges : c.old ⊆ edges := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp (c.initial_maximum.1.1 hT)).2 heT

theorem rest_support_subset : support c.rest ⊆ c.remainingEdges := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  exact (mem_trianglesOn.mp (c.rest_packing.1 hT)).2 heT

theorem oldRemaining_subset_remaining : c.oldRemaining ⊆ c.remainingEdges := by
  intro e he
  exact mem_sdiff.mpr ⟨c.old_subset_edges (mem_sdiff.mp he).1, (mem_sdiff.mp he).2⟩

theorem remaining_old_ge_two {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn c.remainingEdges) :
    2 ≤ (T ∩ c.old).card :=
  old_card_ge_two_after_typeOne c.initial_maximum c.first_maximum hT

theorem remaining_new_le_one {T : Finset (Sym2 V)} (hT : T ∈ trianglesOn c.remainingEdges) :
    (T \ c.old).card ≤ 1 := by
  have hold := c.remaining_old_ge_two hT
  have hcard := trianglesOn_card hT
  have hp := card_sdiff_add_card_inter T c.old
  omega

theorem typeTwo_maximum :
    IsMaximumPacking (typeFamily c.remainingEdges c.old 2) c.typeTwo :=
  c.rest_lexMaximum.typePart_maximum (typeFamily_subset _ _ _)

theorem typeTwo_subset_rest : c.typeTwo ⊆ c.rest := inter_subset_left

theorem newEdges_subset_remaining : c.newEdges ⊆ c.remainingEdges :=
  sdiff_subset.trans c.rest_support_subset

theorem newEdges_disjoint_old : Disjoint c.newEdges c.old := sdiff_disjoint

theorem newEdges_eq_red_typeTwo :
    c.newEdges = redEdges (c.remainingEdges \ c.old) c.typeTwo := by
  ext e
  constructor
  · intro he
    obtain ⟨heP, heO⟩ := mem_sdiff.mp he
    obtain ⟨T, hT, heT⟩ := mem_support.mp heP
    have hactual := c.rest_packing.1 hT
    have htype := new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
      (mem_sdiff.mpr ⟨heT, heO⟩)
    exact mem_redEdges.mpr ⟨mem_support.mpr ⟨T, mem_inter.mpr ⟨hT, htype⟩, heT⟩,
      mem_sdiff.mpr ⟨c.newEdges_subset_remaining he, heO⟩⟩
  · intro he
    obtain ⟨heB, heR⟩ := mem_redEdges.mp he
    exact mem_sdiff.mpr ⟨support_mono c.typeTwo_subset_rest heB, (mem_sdiff.mp heR).2⟩

theorem card_newEdges : c.newEdges.card = c.typeTwo.card := by
  rw [c.newEdges_eq_red_typeTwo]
  exact c.typeTwo_maximum.1.card_redEdges (typeTwo_colored _ _)

theorem first_rest_card_le : c.first.card + c.rest.card ≤ c.initial.card := by
  have h := deleted_packing_card_add_le c.first_packing c.rest_packing
  rwa [← c.initial_maximum.card_eq] at h

theorem oldRemaining_card : c.oldRemaining.card + c.first.card = 3 * c.initial.card :=
  remaining_old_card c.initial_maximum.1 c.first_maximum.1

theorem rest_covers : IsCover (trianglesOn c.remainingEdges) (support c.rest) :=
  c.rest_lexMaximum.support_covers (fun _ hT => trianglesOn_nonempty hT)

/-- The paper's complete residual family S. -/
noncomputable def specialFamily : Finset (Finset (Sym2 V)) :=
  oneRedTriangles (c.newEdges ∪ (c.oldRemaining \ support c.rest)) c.newEdges

theorem specialFamily_colored : ColoredFamily c.specialFamily c.newEdges :=
  oneRedTriangles_colored _ _

theorem special_edges_subset :
    c.newEdges ∪ (c.oldRemaining \ support c.rest) ⊆ c.remainingEdges :=
  union_subset c.newEdges_subset_remaining
    (sdiff_subset.trans c.oldRemaining_subset_remaining)

theorem specialFamily_subset_triangles : c.specialFamily ⊆ trianglesOn c.remainingEdges := by
  intro T hT
  obtain ⟨ht, hsub, _⟩ := mem_oneRedTriangles.mp hT
  exact mem_trianglesOn.mpr ⟨ht, hsub.trans c.special_edges_subset⟩

/-- Selecting the old edges of P' leaves precisely S. -/
theorem specialFamily_eq_residual :
    c.specialFamily = residual (trianglesOn c.remainingEdges) (support c.rest ∩ c.old) := by
  ext T
  constructor
  · intro hT
    refine mem_residual.mpr ⟨c.specialFamily_subset_triangles hT, disjoint_left.mpr ?_⟩
    intro e heT heSelected
    obtain ⟨heRest, heOld⟩ := mem_inter.mp heSelected
    have he := (mem_oneRedTriangles.mp hT).2.1 heT
    rcases mem_union.mp he with heNew | heBlue
    · exact (mem_sdiff.mp heNew).2 heOld
    · exact (mem_sdiff.mp heBlue).2 heRest
  · intro hT
    obtain ⟨hactual, hd⟩ := mem_residual.mp hT
    obtain ⟨e, he⟩ := c.rest_covers T hactual
    obtain ⟨heT, heRest⟩ := mem_inter.mp he
    have heNotOld : e ∉ c.old := by
      intro heOld
      exact disjoint_left.mp hd heT (mem_inter.mpr ⟨heRest, heOld⟩)
    have heNew : e ∈ c.newEdges := mem_sdiff.mpr ⟨heRest, heNotOld⟩
    have hunique := card_le_one.mp (c.remaining_new_le_one hactual)
    apply mem_oneRedTriangles.mpr
    refine ⟨(mem_trianglesOn.mp hactual).1, ?_, ?_⟩
    · intro f hf
      by_cases hfOld : f ∈ c.old
      · have hfRemain := (mem_trianglesOn.mp hactual).2 hf
        have hfRest : f ∉ support c.rest := by
          intro hfr
          exact disjoint_left.mp hd hf (mem_inter.mpr ⟨hfr, hfOld⟩)
        exact mem_union_right _ (mem_sdiff.mpr
          ⟨mem_sdiff.mpr ⟨hfOld, (mem_sdiff.mp hfRemain).2⟩, hfRest⟩)
      · have hfe := hunique f (mem_sdiff.mpr ⟨hf, hfOld⟩)
          e (mem_sdiff.mpr ⟨heT, heNotOld⟩)
        exact mem_union_left _ (hfe.symm ▸ heNew)
    · apply card_eq_one.mpr
      refine ⟨e, ?_⟩
      ext f
      constructor
      · intro hf
        obtain ⟨hfT, hfNew⟩ := mem_inter.mp hf
        exact mem_singleton.mpr (hunique f
          (mem_sdiff.mpr ⟨hfT, (mem_sdiff.mp hfNew).2⟩)
          e (mem_sdiff.mpr ⟨heT, heNotOld⟩))
      · intro hf
        rw [mem_singleton.mp hf]
        exact mem_inter.mpr ⟨heT, heNew⟩

theorem specialFamily_subset_typeTwo :
    c.specialFamily ⊆ typeFamily c.remainingEdges c.old 2 := by
  intro T hT
  have hactual := c.specialFamily_subset_triangles hT
  have hred := (mem_oneRedTriangles.mp hT).2.2
  obtain ⟨e, he⟩ := card_pos.mp (show 0 < (T ∩ c.newEdges).card by omega)
  obtain ⟨heT, heNew⟩ := mem_inter.mp he
  exact new_edge_forces_typeTwo hactual (c.remaining_old_ge_two hactual)
    (mem_sdiff.mpr ⟨heT, (mem_sdiff.mp heNew).2⟩)

/-- The embedding used to apply the unique-red exchange in the larger graph. -/
theorem specialFamily_subset_typeTwo_residual :
    c.specialFamily ⊆ residual (typeFamily c.remainingEdges c.old 2)
      (blueEdges (c.remainingEdges \ c.old) c.typeTwo) := by
  intro T hT
  refine mem_residual.mpr ⟨c.specialFamily_subset_typeTwo hT, ?_⟩
  have hd := (mem_residual.mp (c.specialFamily_eq_residual ▸ hT)).2
  apply hd.mono_right
  intro e he
  obtain ⟨heB, heNotRed⟩ := mem_blueEdges.mp he
  have heRest := support_mono c.typeTwo_subset_rest heB
  refine mem_inter.mpr ⟨heRest, ?_⟩
  by_contra heNotOld
  exact heNotRed (mem_sdiff.mpr ⟨c.rest_support_subset heRest, heNotOld⟩)

theorem inter_oldRemaining {T : Finset (Sym2 V)} (hT : T ⊆ c.remainingEdges) :
    T ∩ c.oldRemaining = T ∩ c.old := by
  ext e
  constructor
  · intro he
    exact mem_inter.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).1⟩
  · intro he
    obtain ⟨heT, heOld⟩ := mem_inter.mp he
    exact mem_inter.mpr ⟨heT, mem_sdiff.mpr ⟨heOld, (mem_sdiff.mp (hT heT)).2⟩⟩

theorem typeFamily_oldRemaining (j : ℕ) :
    typeFamily c.remainingEdges c.oldRemaining j = typeFamily c.remainingEdges c.old j := by
  ext T
  simp only [mem_typeFamily]
  constructor <;> rintro ⟨hT, hc⟩
  · exact ⟨hT, (c.inter_oldRemaining (mem_trianglesOn.mp hT).2) ▸ hc⟩
  · exact ⟨hT, (c.inter_oldRemaining (mem_trianglesOn.mp hT).2).symm ▸ hc⟩

theorem remaining_sdiff_oldRemaining :
    c.remainingEdges \ c.oldRemaining = c.remainingEdges \ c.old := by
  ext e
  simp only [remainingEdges, oldRemaining, mem_sdiff]
  tauto

theorem remaining_oldRemaining_ge_two {T : Finset (Sym2 V)}
    (hT : T ∈ trianglesOn c.remainingEdges) : 2 ≤ (T ∩ c.oldRemaining).card := by
  rw [c.inter_oldRemaining (mem_trianglesOn.mp hT).2]
  exact c.remaining_old_ge_two hT

theorem old_not_diag {e : Sym2 V} (he : e ∈ c.old) : ¬ e.IsDiag := by
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  intro hd
  have hloop : s(e.diagElem hd, e.diagElem hd) ∈ T :=
    (congrArg (fun f : Sym2 V => f ∈ T) (Sym2.diag_diagElem hd)).mpr heT
  exact (mem_trianglesOn.mp (c.initial_maximum.1.1 hT)).1.not_mem_diag _ hloop

theorem newEdges_not_diag {e : Sym2 V} (he : e ∈ c.newEdges) : ¬ e.IsDiag := by
  obtain ⟨T, hT, heT⟩ := mem_support.mp (mem_sdiff.mp he).1
  intro hd
  have hloop : s(e.diagElem hd, e.diagElem hd) ∈ T :=
    (congrArg (fun f : Sym2 V => f ∈ T) (Sym2.diag_diagElem hd)).mpr heT
  exact (mem_trianglesOn.mp (c.rest_packing.1 hT)).1.not_mem_diag _ hloop

variable {c}

theorem rest_red_eq_sdiff (p : {T // T ∈ c.rest}) :
    p.val ∩ c.newEdges = p.val \ c.old := by
  ext e
  constructor
  · intro he
    exact mem_sdiff.mpr ⟨(mem_inter.mp he).1, (mem_sdiff.mp (mem_inter.mp he).2).2⟩
  · intro he
    obtain ⟨hep, heO⟩ := mem_sdiff.mp he
    exact mem_inter.mpr ⟨hep, mem_sdiff.mpr ⟨mem_support.mpr ⟨p.val, p.property, hep⟩, heO⟩⟩

theorem typeTwo_red_card (p : {T // T ∈ c.typeTwo}) :
    (p.val ∩ c.newEdges).card = 1 := by
  rw [rest_red_eq_sdiff (c := c) ⟨p.val, c.typeTwo_subset_rest p.property⟩]
  change (p.val \ c.old).card = 1
  have ho := (mem_typeFamily.mp (mem_inter.mp p.property).2).2
  have ht := trianglesOn_card (c.rest_packing.1 (c.typeTwo_subset_rest p.property))
  have hs := card_sdiff_add_card_inter p.val c.old
  omega

theorem typeTwo_red_nonempty (p : {T // T ∈ c.typeTwo}) :
    (p.val ∩ c.newEdges).Nonempty := card_pos.mp (by rw [typeTwo_red_card p]; decide)

noncomputable def typeTwoSpine (p : {T // T ∈ c.typeTwo}) : Sym2 V :=
  Classical.choose (typeTwo_red_nonempty p)

theorem typeTwoSpine_mem (p : {T // T ∈ c.typeTwo}) :
    typeTwoSpine p ∈ p.val ∩ c.newEdges :=
  Classical.choose_spec (typeTwo_red_nonempty p)

end Construction

end TuzaBound
end

section
-- Wang: Colored.Exchange
/-! The two-for-one exchange: Lemma 2.1. -/

namespace TuzaBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem red_edges_eq {T R : Finset (Sym2 V)}
    (hcard : (T ∩ R).card = 1) {e f : Sym2 V}
    (he : e ∈ T) (heR : e ∈ R) (hf : f ∈ T) (hfR : f ∈ R) : e = f := by
  exact Finset.card_le_one.mp (Nat.le_of_eq hcard)
    e (mem_inter.mpr ⟨he, heR⟩) f (mem_inter.mpr ⟨hf, hfR⟩)

/-- The two-for-one exchange in Lemma 2.1 of the manuscript. -/
theorem unique_residual_triangle {A R : Finset (Sym2 V)}
    {P : Finset (Finset (Sym2 V))} {u v x y : V}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hparent : triangleEdges u v x ∈ P)
    (hpage : triangleEdges u v y ∈
      residual (oneRedTriangles A R) (blueEdges R P))
    (hspine : s(u, v) ∈ R)
    (hoppA : s(x, y) ∈ A) (hoppR : s(x, y) ∈ R)
    (hoppNew : s(x, y) ∉ redEdges R P) :
    ∀ T ∈ residual (oneRedTriangles A R) (blueEdges R P),
      s(u, v) ∈ T → T = triangleEdges u v y := by
  classical
  obtain ⟨hX, hXA, hXR⟩ := mem_oneRedTriangles.mp (hP.1.1 hparent)
  obtain ⟨hpageF, hpageDisj⟩ := mem_residual.mp hpage
  obtain ⟨hY, hYA, hYR⟩ := mem_oneRedTriangles.mp hpageF
  have huv : u ≠ v := hX.ne_of_mem (by simp)
  have hux : u ≠ x := hX.ne_of_mem (by simp)
  have hvx : v ≠ x := hX.ne_of_mem (by simp)
  have huy : u ≠ y := hY.ne_of_mem (by simp)
  have hvy : v ≠ y := hY.ne_of_mem (by simp)

  have huxNotRed : s(u, x) ∉ R := by
    intro hred
    have heq := red_edges_eq hXR (by simp) hred (by simp) hspine
    exact hvx (Sym2.congr_right.mp heq).symm
  have huyNotRed : s(u, y) ∉ R := by
    intro hred
    have heq := red_edges_eq hYR (by simp) hred (by simp) hspine
    exact hvy (Sym2.congr_right.mp heq).symm
  have huxBlue : s(u, x) ∈ blueEdges R P := by
    exact mem_sdiff.mpr ⟨mem_support.mpr ⟨triangleEdges u v x, hparent, by simp⟩,
      huxNotRed⟩
  have hxy : x ≠ y := by
    intro h
    exact disjoint_left.mp hpageDisj (by simp [h]) huxBlue
  have huyOutside : s(u, y) ∉ support P := by
    intro hs
    exact disjoint_left.mp hpageDisj (by simp)
      (mem_sdiff.mpr ⟨hs, huyNotRed⟩)
  have hxyOutside : s(x, y) ∉ support P := by
    intro hs
    exact hoppNew (mem_inter.mpr ⟨hs, hoppR⟩)

  intro T hT huvT
  have hTreal := (mem_oneRedTriangles.mp (mem_residual.mp hT).1).1
  obtain ⟨z, huz, hvz, rfl⟩ := hTreal.exists_third_of_mem huvT
  by_contra hne
  obtain ⟨hTF, hTDisj⟩ := mem_residual.mp hT
  obtain ⟨hZ, hZA, hZR⟩ := mem_oneRedTriangles.mp hTF
  have hxz : x ≠ z := by
    intro h
    exact disjoint_left.mp hTDisj (by simp [h]) huxBlue
  have hyz : y ≠ z := by
    intro h
    apply hne
    subst z
    rfl

  have hnew : triangleEdges u x y ∈ oneRedTriangles A R := by
    apply mem_oneRedTriangles.mpr
    refine ⟨isTriangle_triangleEdges hux huy hxy, ?_, ?_⟩
    · intro e he
      rcases mem_triangleEdges.mp he with rfl | rfl | rfl
      · exact hXA (by simp)
      · exact hYA (by simp)
      · exact hoppA
    · have hinter : triangleEdges u x y ∩ R = {s(x, y)} := by
        ext e
        simp only [mem_inter, mem_triangleEdges, mem_singleton]
        constructor
        · rintro ⟨he, hr⟩
          rcases he with rfl | rfl | rfl
          · exact (huxNotRed hr).elim
          · exact (huyNotRed hr).elim
          · rfl
        · rintro rfl
          exact ⟨Or.inr (Or.inr rfl), hoppR⟩
      simp [hinter]

  have hvertices : [u, x, y, v, z].Nodup := by
    simp [List.nodup_cons, hux, huy, huv, huz, hxy, hvx.symm, hxz,
      hvy.symm, hyz, hvz]
  have hnewDisj : Disjoint (triangleEdges u x y) (triangleEdges u v z) :=
    triangleEdges_disjoint_of_five_distinct hvertices
  have hnewRest : Disjoint (triangleEdges u x y)
      (support (P.erase (triangleEdges u v x))) := by
    apply hP.1.disjoint_support_erase hparent
    intro e he hs
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · simp
    · exact (huyOutside hs).elim
    · exact (hxyOutside hs).elim
  have hotherRest : Disjoint (triangleEdges u v z)
      (support (P.erase (triangleEdges u v x))) := by
    apply hP.1.disjoint_support_erase hparent
    intro e he hs
    have hr : e ∈ R := by
      by_contra hr
      exact disjoint_left.mp hTDisj he (mem_sdiff.mpr ⟨hs, hr⟩)
    have heq := red_edges_eq hZR he hr (by simp) hspine
    rw [heq]
    simp
  exact hP.no_two_for_one hparent hnew hTF
    ⟨s(u, x), by simp⟩ ⟨s(u, v), by simp⟩ hnewDisj hnewRest hotherRest

end TuzaBound
end

section
-- Wang: Books.Layered
/-!
Two-layer books obtained by pairing a maximum packing with a residual packing.
-/

namespace TuzaBound
namespace Layered

open Finset

variable {E : Type*} [DecidableEq E]

noncomputable def pairedParents (R : Finset E) (P Q : Finset (Finset E)) :
    Finset (Finset E) := by
  classical
  exact P.filter (fun p => ∃ q ∈ Q, p ∩ R = q ∩ R)

def children (R : Finset E) (Q : Finset (Finset E)) (p : Finset E) :
    Finset (Finset E) := Q.filter (fun q => q ∩ R = p ∩ R)

def twoLayerPages (R : Finset E) (P Q : Finset (Finset E))
    (p : {T // T ∈ P}) : Finset (Finset E) := insert p.val (children R Q p.val)

@[simp] theorem mem_pairedParents {R : Finset E} {P Q : Finset (Finset E)}
    {p : Finset E} :
    p ∈ pairedParents R P Q ↔ p ∈ P ∧ ∃ q ∈ Q, p ∩ R = q ∩ R := by
  classical
  simp [pairedParents]

@[simp] theorem mem_children {R : Finset E} {Q : Finset (Finset E)}
    {p q : Finset E} : q ∈ children R Q p ↔ q ∈ Q ∧ q ∩ R = p ∩ R := by
  simp [children]

@[simp] theorem mem_twoLayerPages {R : Finset E} {P Q : Finset (Finset E)}
    {p : {T // T ∈ P}} {T : Finset E} :
    T ∈ twoLayerPages R P Q p ↔ T = p.val ∨ (T ∈ Q ∧ T ∩ R = p.val ∩ R) := by
  simp [twoLayerPages]

theorem pairedParents_subset (R : Finset E) (P Q : Finset (Finset E)) :
    pairedParents R P Q ⊆ P := by
  intro p hp
  exact (mem_pairedParents.mp hp).1

variable {F P Q : Finset (Finset E)} {R : Finset E}

theorem exists_parent (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    ∃ p : {T // T ∈ P}, p.val ∩ R = q.val ∩ R := by
  have hq := hQ.1 q.property
  have hqF := (mem_residual.mp hq).1
  have hn : (q.val ∩ R).Nonempty := card_pos.mp (by rw [(hF q.val hqF).2]; decide)
  obtain ⟨e, he⟩ := hn
  have heP := residual_red_subset_parent_red hF hP hq he
  obtain ⟨p, hp, hep⟩ := mem_support.mp (mem_redEdges.mp heP).1
  refine ⟨⟨p, hp⟩, ?_⟩
  have hpone := hF.red_eq_singleton (hP.1.1 hp) hep (mem_inter.mp he).2
  have hqone := hF.red_eq_singleton hqF (mem_inter.mp he).1 (mem_inter.mp he).2
  exact hpone.trans hqone.symm

noncomputable def parent (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    {T // T ∈ P} := Classical.choose (exists_parent hF hP hQ q)

theorem parent_spec (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q}) :
    (parent hF hP hQ q).val ∩ R = q.val ∩ R :=
  Classical.choose_spec (exists_parent hF hP hQ q)

theorem parent_unique (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (q : {T // T ∈ Q})
    (p : {T // T ∈ P}) (heq : p.val ∩ R = q.val ∩ R) :
    p = parent hF hP hQ q := by
  apply Subtype.ext
  exact hP.1.red_inter_injective hF p.property (parent hF hP hQ q).property
    (heq.trans (parent_spec hF hP hQ q).symm)

theorem parent_injective (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Function.Injective (parent hF hP hQ) := by
  intro q₁ q₂ heq
  apply Subtype.ext
  apply hQ.red_inter_injective hF.residual q₁.property q₂.property
  calc
    q₁.val ∩ R = (parent hF hP hQ q₁).val ∩ R := (parent_spec hF hP hQ q₁).symm
    _ = (parent hF hP hQ q₂).val ∩ R := by rw [heq]
    _ = q₂.val ∩ R := parent_spec hF hP hQ q₂

theorem pairedParents_eq_image (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    pairedParents R P Q = Q.attach.image (fun q => (parent hF hP hQ q).val) := by
  classical
  ext p
  constructor
  · intro hp
    obtain ⟨hpP, q, hq, heq⟩ := mem_pairedParents.mp hp
    have hpq := parent_unique hF hP hQ ⟨q, hq⟩ ⟨p, hpP⟩ heq
    exact mem_image.mpr ⟨⟨q, hq⟩, mem_attach _ _, (congrArg Subtype.val hpq).symm⟩
  · intro hp
    obtain ⟨q, _, rfl⟩ := mem_image.mp hp
    exact mem_pairedParents.mpr ⟨(parent hF hP hQ q).property,
      q.val, q.property, parent_spec hF hP hQ q⟩

theorem pairedParents_card (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    (pairedParents R P Q).card = Q.card := by
  classical
  rw [pairedParents_eq_image hF hP hQ]
  have hinj : Function.Injective (fun q => (parent hF hP hQ q).val) := by
    intro q₁ q₂ heq
    exact parent_injective hF hP hQ (Subtype.ext heq)
  rw [card_image_of_injective _ hinj, card_attach]

theorem residual_packing_card_le (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) : Q.card ≤ P.card := by
  rw [← pairedParents_card hF hP hQ]
  exact card_le_card (pairedParents_subset R P Q)

/-- A residual page cannot be an original parent page: its two blue edges
avoid the parent support. -/
theorem residual_member_not_parent (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) {q : Finset E} (hq : q ∈ Q) :
    q ∉ P := by
  intro hqP
  have hqF := (mem_residual.mp (hQ.1 hq)).1
  have hn : (q \ R).Nonempty := card_pos.mp (by rw [hF.member_blue_card hqF]; decide)
  obtain ⟨e, he⟩ := hn
  obtain ⟨heq, heR⟩ := mem_sdiff.mp he
  exact disjoint_left.mp hQ.blueEdges_disjoint_parent_support
    (mem_blueEdges.mpr ⟨mem_support.mpr ⟨q, hq, heq⟩, heR⟩)
    (mem_support.mpr ⟨q, hqP, heq⟩)

theorem pages_nonempty (R : Finset E) (P Q : Finset (Finset E))
    (p : {T // T ∈ P}) : (twoLayerPages R P Q p).Nonempty := by
  exact ⟨p.val, mem_insert_self _ _⟩

theorem pages_subset_family (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    twoLayerPages R P Q p ⊆ F := by
  intro T hT
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, _⟩
  · exact hP.1.1 p.property
  · exact (mem_residual.mp (hQ.1 hTQ)).1

theorem pages_members_nonempty (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    (T : Finset E) (hT : T ∈ twoLayerPages R P Q p) : T.Nonempty :=
  hF.member_nonempty (pages_subset_family hP hQ p hT)

/-- All parent-support edges of a book belong to that book's parent. -/
theorem book_inter_parent_subset (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    support (twoLayerPages R P Q p) ∩ support P ⊆ p.val := by
  intro e he
  obtain ⟨hebook, heP⟩ := mem_inter.mp he
  obtain ⟨T, hT, heT⟩ := mem_support.mp hebook
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, hred⟩
  · exact heT
  · have heTR : e ∈ T ∩ R :=
      residual_inter_support_eq_inter_red hF hP (hQ.1 hTQ) ▸
        mem_inter.mpr ⟨heT, heP⟩
    exact (mem_inter.mp (hred ▸ heTR)).1

theorem supports_disjoint (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    Books.DisjointSupports (twoLayerPages R P Q) := by
  intro p p' hne
  have hval : p.val ≠ p'.val := fun h => hne (Subtype.ext h)
  have hdparents := hP.1.2 p.property p'.property hval
  apply disjoint_left.mpr
  intro e he he'
  obtain ⟨T, hT, heT⟩ := mem_support.mp he
  obtain ⟨U, hU, heU⟩ := mem_support.mp he'
  rcases mem_twoLayerPages.mp hT with rfl | ⟨hTQ, hTR⟩
  · have hep' := book_inter_parent_subset hF hP hQ p'
      (mem_inter.mpr ⟨he', mem_support.mpr ⟨p.val, p.property, heT⟩⟩)
    exact disjoint_left.mp hdparents heT hep'
  · rcases mem_twoLayerPages.mp hU with rfl | ⟨hUQ, hUR⟩
    · have hep := book_inter_parent_subset hF hP hQ p
        (mem_inter.mpr ⟨he, mem_support.mpr ⟨p'.val, p'.property, heU⟩⟩)
      exact disjoint_left.mp hdparents hep heU
    · have hTU : T ≠ U := by
        intro heq
        apply hval
        apply hP.1.red_inter_injective hF p.property p'.property
        calc
          p.val ∩ R = T ∩ R := hTR.symm
          _ = U ∩ R := by rw [heq]
          _ = p'.val ∩ R := hUR
      exact disjoint_left.mp (hQ.2 hTQ hUQ hTU) heT heU

theorem choices_maximum (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q)
    {f : {T // T ∈ P} → Finset E}
    (hf : Books.ChoosesPages (twoLayerPages R P Q) f) :
    IsMaximumPacking F (Books.choice f) := by
  apply Books.choice_isMaximumPacking (pages_subset_family hP hQ)
    (supports_disjoint hF hP hQ) (pages_members_nonempty hF hP hQ) ?_ hf
  intro K hK
  simpa using hP.2 K hK

theorem children_card_le_one (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : Finset E) :
    (children R Q p).card ≤ 1 := by
  apply card_le_one.mpr
  intro T hT U hU
  obtain ⟨hTQ, hTR⟩ := mem_children.mp hT
  obtain ⟨hUQ, hUR⟩ := mem_children.mp hU
  exact hQ.red_inter_injective hF.residual hTQ hUQ (hTR.trans hUR.symm)

theorem children_nonempty_iff_paired (p : {T // T ∈ P}) :
    (children R Q p.val).Nonempty ↔ p.val ∈ pairedParents R P Q := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨hqQ, heq⟩ := mem_children.mp hq
    exact mem_pairedParents.mpr ⟨p.property, q, hqQ, heq.symm⟩
  · intro hp
    obtain ⟨_, q, hqQ, heq⟩ := mem_pairedParents.mp hp
    exact ⟨q, mem_children.mpr ⟨hqQ, heq.symm⟩⟩

theorem parent_not_child (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P}) :
    p.val ∉ children R Q p.val := by
  intro hp
  exact residual_member_not_parent hF hQ (mem_children.mp hp).1 p.property

theorem pages_card_paired (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    (hp : p.val ∈ pairedParents R P Q) : (twoLayerPages R P Q p).card = 2 := by
  have hpos := card_pos.mpr ((children_nonempty_iff_paired p).mpr hp)
  have hle := children_card_le_one hF hQ p.val
  rw [twoLayerPages, card_insert_of_notMem (parent_not_child hF hQ p)]
  omega

theorem pages_eq_singleton_unpaired (p : {T // T ∈ P})
    (hp : p.val ∉ pairedParents R P Q) : twoLayerPages R P Q p = {p.val} := by
  have hempty : children R Q p.val = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    intro hn
    exact hp ((children_nonempty_iff_paired p).mp hn)
  simp [twoLayerPages, hempty]

theorem pages_card_unpaired (p : {T // T ∈ P})
    (hp : p.val ∉ pairedParents R P Q) : (twoLayerPages R P Q p).card = 1 := by
  rw [pages_eq_singleton_unpaired p hp, card_singleton]

theorem pages_eq_pair (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    {q : Finset E} (hq : q ∈ Q) (heq : q ∩ R = p.val ∩ R) :
    twoLayerPages R P Q p = {p.val, q} := by
  have hchild : children R Q p.val = {q} := by
    ext T
    constructor
    · intro hT
      obtain ⟨hTQ, hTR⟩ := mem_children.mp hT
      exact mem_singleton.mpr
        (hQ.red_inter_injective hF.residual hTQ hq (hTR.trans heq.symm))
    · intro hT
      have hTq := mem_singleton.mp hT
      subst T
      exact mem_children.mpr ⟨hq, heq⟩
  rw [twoLayerPages, hchild]

/-- If an actual red edge occurs only in its parent within the entire family,
that parent has no residual page. -/
theorem unique_red_parent_unpaired (hF : ColoredFamily F R)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) (p : {T // T ∈ P})
    {e : E} (hep : e ∈ p.val) (heR : e ∈ R)
    (hunique : ∀ T ∈ F, e ∈ T → T = p.val) : p.val ∉ pairedParents R P Q := by
  intro hp
  obtain ⟨_, q, hq, heq⟩ := mem_pairedParents.mp hp
  have heqR : e ∈ q ∩ R := heq ▸ mem_inter.mpr ⟨hep, heR⟩
  have hqp := hunique q (mem_residual.mp (hQ.1 hq)).1 (mem_inter.mp heqR).1
  exact residual_member_not_parent hF hQ hq (hqp ▸ p.property)

end Layered
end TuzaBound
end

section
-- Wang: Basic.Arithmetic
/-! The arithmetic combining the colored and full-graph covers. -/

namespace TuzaBound

/-- Arithmetic in the first colored-cover comparison, with denominators cleared. -/
theorem colored_bound_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hsecond : t + r ≤ 2 * p + 3 * a) (hra : r ≤ a) :
    3 * t + 2 * u ≤ 8 * p := by
  omega

/-- Arithmetic after applying the first colored estimate to the residual family. -/
theorem colored_refined_arithmetic {t p a r u : ℕ}
    (hfirst : t + 2 * a + u ≤ 3 * p + r)
    (hresidual : 3 * t + 2 * r ≤ 6 * p + 8 * a) :
    4 * t + u ≤ 9 * p + 6 * a := by
  omega

/-- Equations (3)--(6), combined with weights 20, 8, 19, and 12. -/
theorem four_bounds_arithmetic {t n a b c d h : ℕ}
    (hfirst : t + a ≤ 3 * n)
    (hcut : 8 * t + 8 * c ≤ 12 * n + 20 * a + 12 * b + 3 * h)
    (hbooks : t + c + d ≤ 3 * n)
    (hcolored : 4 * t + 4 * b + h ≤ 12 * n + 9 * c + 6 * d) :
    59 * t + d ≤ 165 * n := by
  omega

end TuzaBound
end

section
-- Wang: Colored.Covers
/-! The two colored covering bounds: Lemma 2.3. -/

namespace TuzaBound

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem paired_geometry {A R : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (q : {T // T ∈ Q}) :
    ∃ u v x y,
      (Layered.parent (oneRedTriangles_colored A R) hP hQ q).val = triangleEdges u v x ∧
      q.val = triangleEdges u v y ∧ s(u, v) ∈ R ∧ [u, v, x, y].Nodup := by
  classical
  let hF := oneRedTriangles_colored A R
  let p := Layered.parent hF hP hQ q
  have hpF := hP.1.1 p.property
  have hqF := (mem_residual.mp (hQ.1 q.property)).1
  have hn : (p.val ∩ R).Nonempty := card_pos.mp (by rw [(hF p.val hpF).2]; decide)
  obtain ⟨e, he⟩ := hn
  obtain ⟨⟨u, v⟩, rfl⟩ := Sym2.mk_surjective e
  have heq : s(u, v) ∈ q.val ∩ R := Layered.parent_spec hF hP hQ q ▸ he
  have hpReal := (mem_oneRedTriangles.mp hpF).1
  have hqReal := (mem_oneRedTriangles.mp hqF).1
  have huv := hpReal.ne_of_mem (mem_inter.mp he).1
  obtain ⟨x, hux, hvx, hpx⟩ := hpReal.exists_third_of_mem (mem_inter.mp he).1
  obtain ⟨y, huy, hvy, hqy⟩ := hqReal.exists_third_of_mem (mem_inter.mp heq).1
  have hxy : x ≠ y := by
    intro h
    have hpq : p.val = q.val := by rw [hpx, hqy, h]
    exact Layered.residual_member_not_parent hF hQ q.property (hpq ▸ p.property)
  refine ⟨u, v, x, y, hpx, hqy, (mem_inter.mp he).2, ?_⟩
  simp [List.nodup_cons, huv, hux, huy, hvx, hvy, hxy]

/-- A fixed opposite edge handles every triangle that misses the chosen red spines.
If it is needed, the associated residual page has a private red edge. -/
private theorem wColoredCovers_paired_extra {A R : Finset (Sym2 V)}
    {P Q : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (q : {T // T ∈ Q}) :
    ∃ e : Sym2 V, ∀ T ∈ oneRedTriangles A R,
      ¬ Disjoint T (Layered.parent (oneRedTriangles_colored A R) hP hQ q).val →
      ¬ Disjoint T q.val → Disjoint T (redEdges R P) →
      e ∈ T ∧ ∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q.val ∩ R → W = q.val := by
  classical
  let hF := oneRedTriangles_colored A R
  let p := Layered.parent hF hP hQ q
  obtain ⟨u, v, x, y, hp, hq, hred, hvertices⟩ := paired_geometry hP hQ q
  refine ⟨s(x, y), ?_⟩
  intro T hT hTp hTq hdR
  have hparent : triangleEdges u v x ∈ P := hp ▸ p.property
  have hpage : triangleEdges u v y ∈
      residual (oneRedTriangles A R) (blueEdges R P) := hq ▸ hQ.1 q.property
  have hspineP : s(u, v) ∈ redEdges R P :=
    mem_redEdges.mpr ⟨mem_support.mpr ⟨triangleEdges u v x, hparent, by simp⟩, hred⟩
  have havoid : s(u, v) ∉ T := fun h => disjoint_left.mp hdR h hspineP
  obtain ⟨ep, hep, hepp⟩ := not_disjoint_iff.mp hTp
  obtain ⟨eq, heq, heqq⟩ := not_disjoint_iff.mp hTq
  have hx : (T ∩ triangleEdges u v x).Nonempty :=
    ⟨ep, mem_inter.mpr ⟨hep, hp ▸ hepp⟩⟩
  have hy : (T ∩ triangleEdges u v y).Nonempty :=
    ⟨eq, mem_inter.mpr ⟨heq, hq ▸ heqq⟩⟩
  have hreal := (mem_oneRedTriangles.mp hT).1
  have hopp := two_page_opposite_mem hreal hvertices havoid hx hy
  have hoppA := (mem_oneRedTriangles.mp hT).2.1 hopp
  have hoppNew : s(x, y) ∉ redEdges R P := fun h => disjoint_left.mp hdR hopp h
  have hoppR : s(x, y) ∈ R := by
    obtain ⟨f, hf⟩ := card_pos.mp (by rw [(hF T hT).2]; decide)
    obtain ⟨hfT, hfR⟩ := mem_inter.mp hf
    have hparentRed : ∀ e ∈ triangleEdges u v x, e ∈ R → e ∈ redEdges R P := by
      intro e he heR
      exact mem_redEdges.mpr ⟨mem_support.mpr ⟨_, hparent, he⟩, heR⟩
    have hchildRed : ∀ e ∈ triangleEdges u v y, e ∈ R → e ∈ redEdges R P := by
      intro e he heR
      exact residual_red_subset_parent_red hF hP hpage (mem_inter.mpr ⟨he, heR⟩)
    rcases two_page_triangle hreal hvertices havoid hx hy with h | h <;>
      rw [h] at hfT <;> rcases mem_triangleEdges.mp hfT with rfl | rfl | rfl
    · exact (disjoint_left.mp hdR (by simp [h])
        (hparentRed _ (by simp) hfR)).elim
    · exact (disjoint_left.mp hdR (by simp [h])
        (hchildRed _ (by simp) hfR)).elim
    · exact hfR
    · exact (disjoint_left.mp hdR (by simp [h])
        (hparentRed _ (by simp) hfR)).elim
    · exact (disjoint_left.mp hdR (by simp [h])
        (hchildRed _ (by simp) hfR)).elim
    · exact hfR
  refine ⟨hopp, ?_⟩
  intro W hW hWR
  have huvQ : s(u, v) ∈ q.val ∩ R := mem_inter.mpr ⟨by simp [hq], hred⟩
  have huvW : s(u, v) ∈ W := (mem_inter.mp (hWR.symm ▸ huvQ)).1
  exact (unique_residual_triangle hP hparent hpage hred hoppA hoppR hoppNew W hW huvW).trans hq.symm

private theorem wColoredCovers_exists_first_cover_base {A R : Finset (Sym2 V)}
    {P Q J : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hJQ : J ⊆ Q)
    (hJ : ∀ q ∈ Q,
      (∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q ∩ R → W = q) → q ∈ J) :
    ∃ C, IsCover (oneRedTriangles A R) C ∧
      support (P \ Layered.pairedParents R P Q) ⊆ C ∧ redEdges R P ⊆ C ∧
      C.card + 2 * Q.card ≤ 3 * P.card + J.card := by
  classical
  let hF := oneRedTriangles_colored A R
  choose opposite hopposite using
    (fun q : {T // T ∈ Q} => wColoredCovers_paired_extra hP hQ q)
  let W := P \ Layered.pairedParents R P Q
  let extras := J.attach.image (fun q => opposite ⟨q.val, hJQ q.property⟩)
  let base := blueEdges R W ∪ redEdges R P
  let C := base ∪ extras
  have hredC : redEdges R P ⊆ C := by
    intro e he
    exact mem_union_left _ (mem_union_right _ he)
  have hsingleC : support W ⊆ C := by
    intro e he
    apply mem_union_left
    by_cases hr : e ∈ R
    · exact mem_union_right _ (mem_redEdges.mpr
        ⟨support_mono sdiff_subset he, hr⟩)
    · exact mem_union_left _ (mem_blueEdges.mpr ⟨he, hr⟩)
  have hcover : IsCover (oneRedTriangles A R) C := by
    intro T hT
    by_contra hn
    have hd : Disjoint T C := disjoint_left.mpr (fun e heT heC =>
      hn ⟨e, mem_inter.mpr ⟨heT, heC⟩⟩)
    obtain ⟨p, hp⟩ := Books.exists_book_all_pages_meet_of_maximum
      (pages := Layered.twoLayerPages R P Q)
      (fun _ hS => hF.member_nonempty hS)
      (fun _ hf => Layered.choices_maximum hF hP hQ hf) hT
    have hTp := hp p.val (Layered.mem_twoLayerPages.mpr (Or.inl rfl))
    by_cases hpaired : p.val ∈ Layered.pairedParents R P Q
    · obtain ⟨_, q, hqQ, hpq⟩ := Layered.mem_pairedParents.mp hpaired
      have hchosen := Layered.parent_unique hF hP hQ ⟨q, hqQ⟩ p hpq
      have hTq := hp q (Layered.mem_twoLayerPages.mpr (Or.inr ⟨hqQ, hpq.symm⟩))
      have hTp' : ¬ Disjoint T (Layered.parent hF hP hQ ⟨q, hqQ⟩).val := by
        rw [← hchosen]
        exact hTp
      obtain ⟨heT, hprivate⟩ := hopposite ⟨q, hqQ⟩ T hT hTp' hTq (hd.mono_right hredC)
      have hqJ := hJ q hqQ hprivate
      have heExtra : opposite ⟨q, hqQ⟩ ∈ extras :=
        mem_image.mpr ⟨⟨q, hqJ⟩, mem_attach _ _, rfl⟩
      exact disjoint_left.mp hd heT (mem_union_right _ heExtra)
    · obtain ⟨e, heT, hep⟩ := not_disjoint_iff.mp hTp
      have heW : e ∈ support W :=
        mem_support.mpr ⟨p.val, mem_sdiff.mpr ⟨p.property, hpaired⟩, hep⟩
      exact disjoint_left.mp hd heT (hsingleC heW)
  have hWpacking := hP.1.subfamily (sdiff_subset : W ⊆ P)
  have hblue : (blueEdges R W).card = 2 * W.card := hWpacking.card_blueEdges hF
  have hred : (redEdges R P).card = P.card := hP.1.card_redEdges hF
  have hWcard : W.card + Q.card = P.card := by
    have h := card_sdiff_add_card_eq_card (Layered.pairedParents_subset R P Q)
    rw [Layered.pairedParents_card hF hP hQ] at h
    exact h
  have hextras : extras.card ≤ J.card := by
    calc
      extras.card ≤ J.attach.card := card_image_le
      _ = J.card := card_attach
  have hcard : C.card ≤ (blueEdges R W).card + (redEdges R P).card + J.card := by
    calc
      C.card ≤ base.card + extras.card := card_union_le _ _
      _ ≤ (blueEdges R W).card + (redEdges R P).card + J.card :=
        Nat.add_le_add (card_union_le _ _) hextras
  refine ⟨C, hcover, hsingleC, hredC, ?_⟩
  omega

/-- The first cover includes one opposite edge for each private residual page.
Every opposite edge that is actually needed is assigned to such a page by
`wColoredCovers_paired_extra`; counting additional private pages only enlarges the bound. -/
theorem exists_first_colored_cover {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    ∃ C, IsCover (oneRedTriangles A R) C ∧
      C.card + 2 * Q.card + U.card ≤ 3 * P.card +
        (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card := by
  classical
  let hF := oneRedTriangles_colored A R
  let J := privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q
  have hJQ : J ⊆ Q := privateRedPages_subset _ _ _
  have hJ : ∀ q ∈ Q,
      (∀ W ∈ residual (oneRedTriangles A R) (blueEdges R P),
        W ∩ R = q ∩ R → W = q) → q ∈ J := by
    intro q hq hp
    exact mem_privateRedPages.mpr ⟨hq, hp⟩
  obtain ⟨C, hC, hsingle, hred, hcard⟩ := wColoredCovers_exists_first_cover_base hP hQ hJQ hJ
  have hUP : U ⊆ P := hU.trans (privateRedPages_subset _ _ _)
  have hUunpaired : U ⊆ P \ Layered.pairedParents R P Q := by
    intro p hp
    obtain ⟨hpP, hprivate⟩ := mem_privateRedPages.mp (hU hp)
    refine mem_sdiff.mpr ⟨hpP, ?_⟩
    intro hpaired
    obtain ⟨_, q, hq, hpq⟩ := Layered.mem_pairedParents.mp hpaired
    have hqp := hprivate q (mem_residual.mp (hQ.1 hq)).1 hpq.symm
    exact Layered.residual_member_not_parent hF hQ hq (hqp.symm ▸ hpP)
  have hblueU : blueEdges R U ⊆ C :=
    (blueEdges_subset_support _ _).trans ((support_mono hUunpaired).trans hsingle)
  have hredU : redEdges R U ⊆ C := by
    intro e he
    obtain ⟨heU, heR⟩ := mem_redEdges.mp he
    exact hred (mem_redEdges.mpr ⟨support_mono hUP heU, heR⟩)
  have hremoved := hC.sdiff_privateRed hF hP.1 hU hblueU
  have hsize := card_sdiff_privateRed hF hP.1 hU hredU
  refine ⟨C \ redEdges R U, hremoved, ?_⟩
  change (C \ redEdges R U).card + 2 * Q.card + U.card ≤ 3 * P.card + J.card
  omega

theorem first_colored_cover {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    transversalNumber (oneRedTriangles A R) + 2 * Q.card + U.card ≤ 3 * P.card +
      (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card := by
  obtain ⟨C, hC, hc⟩ := exists_first_colored_cover hP hQ hU
  exact (Nat.add_le_add_right (Nat.add_le_add_right hC.number_le _) _).trans hc

/-- The first colored bound: equation (1). -/
theorem colored_bound {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsMaximumPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    3 * transversalNumber (oneRedTriangles A R) + 2 * U.card ≤ 8 * P.card := by
  have hfirst := first_colored_cover hP hQ.1 hU
  have hsecond := second_colored_cover (oneRedTriangles_colored A R) hP.1 hQ
  have hr := card_le_card
    (privateRedPages_subset (residual (oneRedTriangles A R) (blueEdges R P)) R Q)
  exact colored_bound_arithmetic hfirst hsecond hr

/-- Apply the first bound to the family left after deleting the parent blue edges. -/
theorem colored_refined {A R : Finset (Sym2 V)}
    {P Q U : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsMaximumPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hU : U ⊆ privateRedPages (oneRedTriangles A R) R P) :
    4 * transversalNumber (oneRedTriangles A R) + U.card ≤
      9 * P.card + 6 * Q.card := by
  have hfirst := first_colored_cover hP hQ.1 hU
  have hQ' : IsMaximumPacking (oneRedTriangles (A \ blueEdges R P) R) Q := by
    rw [oneRedTriangles_sdiff]
    exact hQ
  have hlocal :
      3 * transversalNumber (residual (oneRedTriangles A R) (blueEdges R P)) +
        2 * (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card
      ≤ 8 * Q.card := by
    rw [← oneRedTriangles_sdiff A R (blueEdges R P)]
    exact colored_bound hQ' (maximumPacking_spec _) (Subset.refl _)
  have hdelete := transversalNumber_le_add_residual (oneRedTriangles A R) (blueEdges R P)
    (fun _ hT => (oneRedTriangles_colored A R).member_nonempty hT)
  have hblue : (blueEdges R P).card = 2 * P.card :=
    hP.1.card_blueEdges (oneRedTriangles_colored A R)
  have hresidual : 3 * transversalNumber (oneRedTriangles A R) +
      2 * (privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q).card
      ≤ 6 * P.card + 8 * Q.card := by omega
  exact colored_refined_arithmetic hfirst hresidual

end TuzaBound
end

section
-- Wang: Probability.Average
/-! Finite rational averages and uniformly chosen Boolean vertex colorings. -/

namespace TuzaBound

open scoped BigOperators

variable {Ω : Type*} {Ω' : Type*} {I : Type*} {V : Type*}

/-- The uniform average on a finite type, with values in the rationals. -/
def finiteAverage [Fintype Ω] (f : Ω → ℚ) : ℚ :=
  (∑ ω, f ω) / Fintype.card Ω

/-- The uniform average over all Boolean vertex colorings. -/
def bitAverage [Fintype V] [DecidableEq V] (f : (V → Bool) → ℚ) : ℚ :=
  finiteAverage f

theorem finiteAverage_equiv [Fintype Ω] [Fintype Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℚ) :
    finiteAverage (fun ω => f (e ω)) = finiteAverage f := by
  unfold finiteAverage
  rw [e.sum_comp, Fintype.card_congr e]

theorem finiteAverage_const [Fintype Ω] [Nonempty Ω] (c : ℚ) :
    finiteAverage (fun _ : Ω => c) = c := by
  have hn : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [finiteAverage, hn]

theorem finiteAverage_add [Fintype Ω] (f g : Ω → ℚ) :
    finiteAverage (fun ω => f ω + g ω) = finiteAverage f + finiteAverage g := by
  simp only [finiteAverage, Finset.sum_add_distrib, add_div]

theorem finiteAverage_finset_sum [Fintype Ω] (s : Finset I) (f : I → Ω → ℚ) :
    finiteAverage (fun ω => ∑ i ∈ s, f i ω) =
      ∑ i ∈ s, finiteAverage (f i) := by
  unfold finiteAverage
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteAverage_sum [Fintype Ω] [Fintype I] (f : I → Ω → ℚ) :
    finiteAverage (fun ω => ∑ i, f i ω) = ∑ i, finiteAverage (f i) := by
  exact finiteAverage_finset_sum Finset.univ f

theorem finiteAverage_mono [Fintype Ω] (f g : Ω → ℚ)
    (h : ∀ ω, f ω ≤ g ω) : finiteAverage f ≤ finiteAverage g := by
  unfold finiteAverage
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun ω _ => h ω)
    (by positivity)

/-- Some outcome costs no more than its uniform finite average. -/
theorem exists_le_finiteAverage [Fintype Ω] [Nonempty Ω] (f : Ω → ℚ) :
    ∃ ω, f ω ≤ finiteAverage f := by
  classical
  obtain ⟨ω, _, hω⟩ :=
    Finset.exists_min_image (Finset.univ : Finset Ω) f Finset.univ_nonempty
  refine ⟨ω, ?_⟩
  have hn : (0 : ℚ) < Fintype.card Ω := by
    exact_mod_cast Fintype.card_pos
  apply (le_div_iff₀ hn).2
  calc
    f ω * (Fintype.card Ω : ℚ) = ∑ _ : Ω, f ω := by simp [mul_comm]
    _ ≤ ∑ a : Ω, f a := Finset.sum_le_sum fun a ha => hω a ha

/-- Finite-sum accounting: pointwise charges and individual average bounds
produce one outcome obeying the sum of the budgets. -/
theorem exists_le_sum_of_average_le [Fintype Ω] [Nonempty Ω]
    (s : Finset I) (cost : Ω → ℚ) (base : ℚ)
    (charge : I → Ω → ℚ) (budget : I → ℚ)
    (hcost : ∀ ω, cost ω ≤ base + ∑ i ∈ s, charge i ω)
    (hcharge : ∀ i ∈ s, finiteAverage (charge i) ≤ budget i) :
    ∃ ω, cost ω ≤ base + ∑ i ∈ s, budget i := by
  obtain ⟨ω, hω⟩ := exists_le_finiteAverage cost
  refine ⟨ω, hω.trans ?_⟩
  calc
    finiteAverage cost ≤
        finiteAverage (fun ω => base + ∑ i ∈ s, charge i ω) :=
      finiteAverage_mono _ _ hcost
    _ = base + ∑ i ∈ s, finiteAverage (charge i) := by
      rw [finiteAverage_add, finiteAverage_const, finiteAverage_finset_sum]
    _ ≤ base + ∑ i ∈ s, budget i :=
      add_le_add_right (Finset.sum_le_sum hcharge) base

private theorem wProbabilityAverage_finiteAverage_prod_fst [Fintype Ω] [Fintype Ω']
    [Nonempty Ω] [Nonempty Ω'] (f : Ω → ℚ) :
    finiteAverage (fun p : Ω × Ω' => f p.1) = finiteAverage f := by
  have ha : (Fintype.card Ω : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hb : (Fintype.card Ω' : ℚ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold finiteAverage
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  field_simp

/-- Uniform Boolean colorings restrict uniformly to any list of distinct
vertices.  This is the finite independence statement used below. -/
theorem bitAverage_restrict [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
    (v : I → V) (hv : Function.Injective v) (f : (I → Bool) → ℚ) :
    bitAverage (fun χ : V → Bool => f (χ ∘ v)) = bitAverage f := by
  let : DecidablePred (fun a : V => a ∈ Set.range v) :=
    fun _ => Classical.propDecidable _
  let e : (V → Bool) ≃
      (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) :=
    (Equiv.piEquivPiSubtypeProd (fun a => a ∈ Set.range v) (fun _ => Bool)).trans
      (Equiv.prodCongr
        (Equiv.arrowCongr (Equiv.ofInjective v hv).symm (Equiv.refl Bool))
        (Equiv.refl _))
  have he (χ : V → Bool) : (e χ).1 = χ ∘ v := by
    rfl
  change finiteAverage (fun χ : V → Bool => f (χ ∘ v)) = finiteAverage f
  calc
    finiteAverage (fun χ : V → Bool => f (χ ∘ v)) =
        finiteAverage (fun χ : V → Bool => f (e χ).1) := by
      simp only [he]
    _ = finiteAverage (fun p :
        (I → Bool) × ({a : V // a ∉ Set.range v} → Bool) => f p.1) :=
      finiteAverage_equiv e (fun p => f p.1)
    _ = finiteAverage f := wProbabilityAverage_finiteAverage_prod_fst f

/-- An edge is noncrossing when its endpoints have the same Boolean color. -/
def sameColor (u v : V) (χ : V → Bool) : Prop := χ u = χ v

/-- The event allowing an opposite edge of a two-page book to be added. -/
def bookEvent (u v x y : V) (χ : V → Bool) : Prop :=
  χ x = χ y ∧ (χ u ≠ χ x ∨ χ v ≠ χ x)

instance (u v : V) : DecidablePred (sameColor u v) :=
  fun _ => inferInstanceAs (Decidable (_ = _))

instance (u v x y : V) : DecidablePred (bookEvent u v x y) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ (_ ∨ _)))

/-- Two distinct vertices agree in exactly half of all Boolean colorings. -/
theorem sameColor_average [Fintype V] [DecidableEq V] (u v : V) (huv : u ≠ v) :
    bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) = 1 / 2 := by
  have hi : Function.Injective (![u, v] : Fin 2 → V) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h := bitAverage_restrict (![u, v] : Fin 2 → V) hi
    (fun χ => if χ 0 = χ 1 then (1 : ℚ) else 0)
  have hsmall : bitAverage
      (fun χ : Fin 2 → Bool => if χ 0 = χ 1 then (1 : ℚ) else 0) = 1 / 2 := by
    decide +kernel
  calc
    bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) =
        bitAverage (fun χ : V → Bool =>
          if (χ ∘ (![u, v] : Fin 2 → V)) 0 =
              (χ ∘ (![u, v] : Fin 2 → V)) 1 then (1 : ℚ) else 0) := by
      congr 1
    _ = 1 / 2 := h.trans hsmall

end TuzaBound
end

section
-- Wang: Probability.Cut
/-!
The random-cut cover selects W, noncrossing old edges, and each uncovered
triangle's new edges. When each triangle has at least two old edges, every
added edge is noncrossing.
-/

namespace TuzaBound

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An unoriented edge is noncrossing when its two colors agree. -/
def noncrossingEdge (χ : V → Bool) (e : Sym2 V) : Prop :=
  (Sym2.map χ e).IsDiag

instance (χ : V → Bool) : DecidablePred (noncrossingEdge χ) :=
  fun e => inferInstanceAs (Decidable (Sym2.map χ e).IsDiag)

omit [Fintype V] [DecidableEq V] in
@[simp] theorem noncrossingEdge_pair (χ : V → Bool) (u v : V) :
    noncrossingEdge χ s(u, v) ↔ χ u = χ v := by
  simp [noncrossingEdge]

/-- The old edges selected before any uncovered triangles are considered. -/
def selectedOld (W O : Finset (Sym2 V)) (χ : V → Bool) : Finset (Sym2 V) :=
  W ∪ O.filter (noncrossingEdge χ)

/-- Add every non-old edge of every triangle that the selected old edges miss.
Using a union counts a repeated edge only once. -/
noncomputable def cutAddedEdges (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) :=
  (residual (trianglesOn A) (selectedOld W O χ)).biUnion (fun T => T \ O)

noncomputable def cutCover (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    Finset (Sym2 V) := selectedOld W O χ ∪ cutAddedEdges A W O χ

@[simp] theorem mem_cutAddedEdges {A W O : Finset (Sym2 V)} {χ : V → Bool}
    {e : Sym2 V} :
    e ∈ cutAddedEdges A W O χ ↔
      ∃ T ∈ residual (trianglesOn A) (selectedOld W O χ), e ∈ T \ O := by
  classical
  simp [cutAddedEdges]

omit [Fintype V] in
/-- Every triangle has a noncrossing edge under a Boolean vertex coloring. -/
theorem IsTriangle.exists_noncrossing {T : Finset (Sym2 V)} (hT : IsTriangle T)
    (χ : V → Bool) : ∃ e ∈ T, noncrossingEdge χ e := by
  obtain ⟨u, v, w, huv, huw, hvw, rfl⟩ := hT
  have h : χ u = χ v ∨ χ u = χ w ∨ χ v = χ w := by
    cases χ u <;> cases χ v <;> cases χ w <;> decide
  rcases h with h | h | h
  · exact ⟨s(u, v), by simp, (noncrossingEdge_pair χ u v).mpr h⟩
  · exact ⟨s(u, w), by simp, (noncrossingEdge_pair χ u w).mpr h⟩
  · exact ⟨s(v, w), by simp, (noncrossingEdge_pair χ v w).mpr h⟩

omit [Fintype V] in
theorem selectedOld_subset_old {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (χ : V → Bool) : selectedOld W O χ ⊆ O := by
  exact union_subset hW (filter_subset _ _)

/-- A noncrossing edge of an uncovered triangle cannot be old. -/
theorem residual_noncrossing_not_old {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ))
    {e : Sym2 V} (he : e ∈ T) (hNC : noncrossingEdge χ e) : e ∉ O := by
  intro heO
  exact disjoint_left.mp (mem_residual.mp hT).2 he
    (mem_union_right _ (mem_filter.mpr ⟨heO, hNC⟩))

theorem residual_new_edges_nonempty {A W O T : Finset (Sym2 V)} {χ : V → Bool}
    (hT : T ∈ residual (trianglesOn A) (selectedOld W O χ)) :
    (T \ O).Nonempty := by
  have htri := (mem_trianglesOn.mp (mem_residual.mp hT).1).1
  obtain ⟨e, he, hNC⟩ := htri.exists_noncrossing χ
  exact ⟨e, mem_sdiff.mpr ⟨he, residual_noncrossing_not_old hT he hNC⟩⟩

/-- The selected old edges and the uncovered triangles' new edges cover every triangle. -/
theorem cutCover_covers (A W O : Finset (Sym2 V)) (χ : V → Bool) :
    IsCover (trianglesOn A) (cutCover A W O χ) := by
  apply cover_union_residual
  intro T hT
  obtain ⟨e, he⟩ := residual_new_edges_nonempty hT
  exact ⟨e, mem_inter.mpr ⟨(mem_sdiff.mp he).1,
    mem_cutAddedEdges.mpr ⟨T, hT, he⟩⟩⟩

theorem cutAddedEdges_subset {A W O : Finset (Sym2 V)} (χ : V → Bool) :
    cutAddedEdges A W O χ ⊆ A \ O := by
  intro e he
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  obtain ⟨heT, heO⟩ := mem_sdiff.mp heT
  exact mem_sdiff.mpr
    ⟨(mem_trianglesOn.mp (mem_residual.mp hT).1).2 heT, heO⟩

theorem cutCover_subset {A W O : Finset (Sym2 V)}
    (hW : W ⊆ O) (hO : O ⊆ A) (χ : V → Bool) :
    cutCover A W O χ ⊆ A := by
  exact union_subset ((selectedOld_subset_old hW χ).trans hO)
    ((cutAddedEdges_subset χ).trans sdiff_subset)

/-- There is only one possible new edge in a triangle with at least two old
edges, so every added edge equals its noncrossing edge. -/
theorem cutAddedEdges_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card) (χ : V → Bool)
    {e : Sym2 V} (he : e ∈ cutAddedEdges A W O χ) : noncrossingEdge χ e := by
  obtain ⟨T, hT, heT⟩ := mem_cutAddedEdges.mp he
  have ht := (mem_residual.mp hT).1
  have htri := (mem_trianglesOn.mp ht).1
  obtain ⟨f, hf, hNC⟩ := htri.exists_noncrossing χ
  have hfnew : f ∈ T \ O :=
    mem_sdiff.mpr ⟨hf, residual_noncrossing_not_old hT hf hNC⟩
  have hcard : (T \ O).card ≤ 1 := by
    have hs := card_sdiff_add_card_inter T O
    have htcard := trianglesOn_card ht
    have ho := hOld T ht
    omega
  have hef : e = f := (card_le_one.mp hcard) e heT f hfnew
  exact hef ▸ hNC

theorem cutAddedEdges_inter_subset_noncrossing {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    cutAddedEdges A W O χ ∩ N ⊆ N.filter (noncrossingEdge χ) := by
  intro e he
  obtain ⟨heAdd, heN⟩ := mem_inter.mp he
  exact mem_filter.mpr ⟨heN, cutAddedEdges_noncrossing hOld χ heAdd⟩

/-- Every actual nonloop edge is noncrossing in exactly half of all cuts. -/
theorem noncrossingEdge_average (e : Sym2 V) (he : ¬ e.IsDiag) :
    bitAverage (fun χ => if noncrossingEdge χ e then (1 : ℚ) else 0) = 1 / 2 := by
  revert he
  refine Sym2.inductionOn e ?_
  intro u v he
  have huv : u ≠ v := fun h => he (Sym2.mk_isDiag_iff.mpr h)
  calc
    bitAverage (fun χ => if noncrossingEdge χ s(u, v) then (1 : ℚ) else 0) =
        bitAverage (fun χ => if sameColor u v χ then (1 : ℚ) else 0) := by
      congr 1
    _ = 1 / 2 := sameColor_average u v huv

/-- The expected number of noncrossing edges is half the number of edges. -/
theorem noncrossingEdges_average (E : Finset (Sym2 V))
    (hE : ∀ e ∈ E, ¬ e.IsDiag) :
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
      (E.card : ℚ) / 2 := by
  calc
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
        ∑ e ∈ E, bitAverage (fun χ => if noncrossingEdge χ e then (1 : ℚ) else 0) := by
      unfold bitAverage
      simp_rw [natCast_card_filter]
      exact finiteAverage_finset_sum E _
    _ = ∑ _e ∈ E, (1 / 2 : ℚ) := by
      apply sum_congr rfl
      intro e he
      exact noncrossingEdge_average e (hE e he)
    _ = (E.card : ℚ) / 2 := by simp [div_eq_mul_inv]

omit [Fintype V] in
theorem selectedOld_eq_union_sdiff (W O : Finset (Sym2 V)) (χ : V → Bool) :
    selectedOld W O χ = W ∪ (O \ W).filter (noncrossingEdge χ) := by
  ext e
  simp only [selectedOld, mem_union, mem_filter, mem_sdiff]
  tauto

omit [Fintype V] in
theorem selectedOld_card (W O : Finset (Sym2 V)) (χ : V → Bool) :
    (selectedOld W O χ).card = W.card + ((O \ W).filter (noncrossingEdge χ)).card := by
  rw [selectedOld_eq_union_sdiff, card_union_of_disjoint]
  apply disjoint_left.mpr
  intro e heW heF
  exact (mem_sdiff.mp (mem_filter.mp heF).1).2 heW

/-- The expected cost of the selected old edges. -/
theorem selectedOld_average {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (hO : ∀ e ∈ O, ¬ e.IsDiag) :
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) =
      (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 := by
  calc
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) =
        (W.card : ℚ) + bitAverage
          (fun χ => (((O \ W).filter (noncrossingEdge χ)).card : ℚ)) := by
      simp_rw [selectedOld_card, Nat.cast_add]
      exact (finiteAverage_add _ _).trans
        (by rw [finiteAverage_const]; rfl)
    _ = (W.card : ℚ) + ((O \ W).card : ℚ) / 2 := by
      rw [noncrossingEdges_average (O \ W)
        (fun e he => hO e (mem_sdiff.mp he).1)]
    _ = (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 := by
      rw [card_sdiff_of_subset hW, Nat.cast_sub (card_le_card hW)]

theorem selectedOld_average_le {W O : Finset (Sym2 V)} (hW : W ⊆ O)
    (hO : ∀ e ∈ O, ¬ e.IsDiag) :
    bitAverage (fun χ => ((selectedOld W O χ).card : ℚ)) ≤
      (W.card : ℚ) + ((O.card : ℚ) - W.card) / 2 :=
  (selectedOld_average hW hO).le

/-- The nonloop hypothesis is automatic for a set of actual simple-graph edges. -/
theorem noncrossingGraphEdges_average (G : SimpleGraph V) (E : Finset (Sym2 V))
    (hE : E ⊆ graphEdges G) :
    bitAverage (fun χ => ((E.filter (noncrossingEdge χ)).card : ℚ)) =
      (E.card : ℚ) / 2 :=
  noncrossingEdges_average E
    (fun _ he => G.not_isDiag_of_mem_edgeSet (mem_graphEdges.mp (hE he)))

/-- The pointwise cover cost, separating added edges inside and outside `N`. -/
theorem cutCover_card_le {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    (cutCover A W O χ).card ≤ W.card +
      ((O \ W).filter (noncrossingEdge χ)).card +
      (N.filter (noncrossingEdge χ)).card + (cutAddedEdges A W O χ \ N).card := by
  have hi := card_le_card (cutAddedEdges_inter_subset_noncrossing (W := W) hOld N χ)
  have hs := card_inter_add_card_sdiff (cutAddedEdges A W O χ) N
  have hu := card_union_le (selectedOld W O χ) (cutAddedEdges A W O χ)
  rw [selectedOld_card] at hu
  change (selectedOld W O χ ∪ cutAddedEdges A W O χ).card ≤ _
  omega

/-- The same pointwise inequality in the indicator form consumed by finite
average linearity. -/
theorem cutCover_charge_le {A W O : Finset (Sym2 V)}
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card)
    (N : Finset (Sym2 V)) (χ : V → Bool) :
    ((cutCover A W O χ).card : ℚ) ≤ (W.card : ℚ) +
      (∑ e ∈ O \ W, if noncrossingEdge χ e then (1 : ℚ) else 0) +
      (∑ e ∈ N, if noncrossingEdge χ e then (1 : ℚ) else 0) +
      ((cutAddedEdges A W O χ \ N).card : ℚ) := by
  simp only [sum_boole]
  exact_mod_cast cutCover_card_le hOld N χ

end TuzaBound
end

/-! ## Distinct opposites, simultaneous rotations, and cover bounds -/

section
open TuzaBound Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Maximum size of a family of graph triangles with pairwise disjoint edge sets. -/
noncomputable def tuzaNu (G : SimpleGraph V) : ℕ := packingNumber (graphTriangles G)

/-- Minimum number of edges hitting every graph triangle. -/
noncomputable def tuzaTau (G : SimpleGraph V) : ℕ := transversalNumber (graphTriangles G)

theorem le_tuzaNu_iff (G : SimpleGraph V) (n : ℕ) :
    n ≤ tuzaNu G ↔ ∃ P, IsPacking (graphTriangles G) P ∧ n ≤ P.card := le_nu_iff G n

/-- A packing witness expressed directly by adjacency of the three vertices
and pairwise disjointness of the resulting sets of three graph edges. -/
theorem le_tuzaNu_iff_adj (G : SimpleGraph V) (n : ℕ) :
    n ≤ tuzaNu G ↔ ∃ P : Finset (Finset (Sym2 V)), n ≤ P.card ∧
      (∀ T ∈ P, ∃ u v w, G.Adj u v ∧ G.Adj u w ∧ G.Adj v w ∧ T = triangleEdges u v w) ∧
      (P : Set (Finset (Sym2 V))).Pairwise Disjoint := by
  rw [le_tuzaNu_iff]
  constructor
  · rintro ⟨P,⟨hs,hd⟩,hn⟩
    exact ⟨P,hn,fun _ h => mem_graphTriangles_iff.mp (hs h),hd⟩
  · rintro ⟨P,hn,hs,hd⟩
    exact ⟨P,⟨fun T h => mem_graphTriangles_iff.mpr (hs T h),hd⟩,hn⟩

theorem tuzaTau_le_iff (G : SimpleGraph V) (n : ℕ) :
    tuzaTau G ≤ n ↔ ∃ C, C ⊆ graphEdges G ∧ C.card ≤ n ∧
      ∀ u v w, G.Adj u v → G.Adj u w → G.Adj v w →
        s(u,v) ∈ C ∨ s(u,w) ∈ C ∨ s(v,w) ∈ C := by
  rw [show tuzaTau G = tau G from rfl, tau_le_iff]
  constructor
  · rintro ⟨C, hC, h, hn⟩
    exact ⟨C, hC, hn, (graph_cover_iff_adj G C).mp h⟩
  · rintro ⟨C, hC, hn, h⟩
    exact ⟨C, hC, (graph_cover_iff_adj G C).mpr h, hn⟩

/-- The colored family contains *every* triangle with exactly one red edge. -/
noncomputable def coloredTau (G : SimpleGraph V) (R : Finset (Sym2 V)) : ℕ :=
  transversalNumber (oneRedTriangles (graphEdges G) R)

noncomputable def coloredNu (G : SimpleGraph V) (R : Finset (Sym2 V)) : ℕ :=
  packingNumber (oneRedTriangles (graphEdges G) R)
end

namespace TuzaBound
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In the uniform-cut cover one need only count the *distinct edges* of the
residual triangle family. No event about the colors of four vertices is needed. -/
theorem cut_cover_from_residual_support
    (F : Finset (Finset (Sym2 V))) (W : Finset (Sym2 V))
    (hF : ∀ T ∈ F, IsTriangle T) :
    2 * transversalNumber F ≤ 2 * W.card + (support (residual F W)).card := by
  classical
  let E := support (residual F W)
  have hn : ∀ e ∈ E, ¬ e.IsDiag := by
    intro e he
    obtain ⟨T, hT, heT⟩ := mem_support.mp he
    intro hd
    have hloop : s(e.diagElem hd, e.diagElem hd) ∈ T :=
      (congrArg (fun f : Sym2 V => f ∈ T) (Sym2.diag_diagElem hd)).mpr heT
    exact (hF T (mem_residual.mp hT).1).not_mem_diag _ hloop
  obtain ⟨χ, hχ⟩ := exists_le_finiteAverage
    (fun χ : V → Bool => ((E.filter (noncrossingEdge χ)).card : ℚ))
  change _ ≤ bitAverage _ at hχ
  rw [noncrossingEdges_average E hn] at hχ
  have hh : 2 * (E.filter (noncrossingEdge χ)).card ≤ E.card := by
    exact_mod_cast (show (2 : ℚ) * ((E.filter (noncrossingEdge χ)).card : ℚ) ≤ E.card by linarith)
  have hhit : IsCover (residual F W) (E.filter (noncrossingEdge χ)) := by
    intro T hT
    obtain ⟨e, he, hχe⟩ := (hF T (mem_residual.mp hT).1).exists_noncrossing χ
    exact ⟨e, mem_inter.mpr ⟨he, mem_filter.mpr ⟨mem_support.mpr ⟨_,hT,he⟩,hχe⟩⟩⟩
  have h := (cover_union_residual hhit).number_le
  have hc := card_union_le W (E.filter (noncrossingEdge χ))
  change 2 * transversalNumber F ≤ 2 * W.card + E.card
  omega

end TuzaBound

namespace TuzaBound
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Count a red edge once even when several uncovered triangles need it. -/
noncomputable def looseRed (A R W N : Finset (Sym2 V)) : Finset (Sym2 V) :=
  redEdges R (residual (oneRedTriangles A R) (W ∪ N))

/-- The uniform cut row before substituting packing counts. Outside the
fixed spokes and the blue edges, only packed red edges and distinct loose red
edges can remain in a triangle. -/
theorem distinct_red_cut_cover {A O W N : Finset (Sym2 V)}
    (hW : W ⊆ O) (hN : N ⊆ A \ O)
    (hOld : ∀ T ∈ trianglesOn A, 2 ≤ (T ∩ O).card) :
    2 * transversalNumber (trianglesOn A) ≤
      W.card + O.card + N.card + (looseRed A (A \ O) W N).card := by
  classical
  let L := looseRed A (A \ O) W N
  have sub : support (residual (trianglesOn A) W) ⊆ (O \ W) ∪ N ∪ L := by
    intro e he
    obtain ⟨T,hT,heT⟩ := mem_support.mp he
    obtain ⟨hTA,hd⟩ := mem_residual.mp hT
    by_cases heO : e ∈ O
    · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr
        ⟨heO, fun h => disjoint_left.mp hd heT h⟩))
    by_cases heN : e ∈ N
    · exact mem_union_left _ (mem_union_right _ heN)
    have ht := new_edge_forces_typeTwo hTA (hOld T hTA) (mem_sdiff.mpr ⟨heT,heO⟩)
    rw [typeTwo_eq_oneRed] at ht
    have heR : e ∈ A \ O := mem_sdiff.mpr ⟨(mem_trianglesOn.mp hTA).2 heT, heO⟩
    have hdN : Disjoint T N := by
      apply disjoint_left.mpr
      intro f hfT hfN
      have h := red_edges_eq (mem_oneRedTriangles.mp ht).2.2 hfT (hN hfN) heT heR
      exact heN (h ▸ hfN)
    exact mem_union_right _ (mem_redEdges.mpr ⟨mem_support.mpr
      ⟨T, mem_residual.mpr ⟨ht, Finset.disjoint_union_right.mpr ⟨hd,hdN⟩⟩, heT⟩, heR⟩)
  have hs := card_le_card sub
  have ha := card_union_le (O \ W) N
  have hb := card_union_le ((O \ W) ∪ N) L
  have hc := card_sdiff_add_card_eq_card hW
  have ht := cut_cover_from_residual_support (trianglesOn A) W
    (fun _ h => (mem_trianglesOn.mp h).1)
  change _ ≤ W.card + O.card + N.card + L.card
  omega
end TuzaBound

namespace TuzaBound
open Finset
variable {E : Type*} [DecidableEq E]

noncomputable def fixedSpokes (R : Finset E) (P Q : Finset (Finset E)) : Finset E :=
  blueEdges R (P \ Layered.pairedParents R P Q)

theorem fixedSpokes_card {R : Finset E} {F P Q : Finset (Finset E)}
    (hF : ColoredFamily F R) (hP : IsMaximumPacking F P)
    (hQ : IsPacking (residual F (blueEdges R P)) Q) :
    (fixedSpokes R P Q).card + 2 * Q.card = 2 * P.card := by
  have h₁ := (hP.1.subfamily (sdiff_subset : P \ Layered.pairedParents R P Q ⊆ P)).card_blueEdges hF
  have h₂ := card_sdiff_add_card_eq_card (Layered.pairedParents_subset R P Q)
  rw [Layered.pairedParents_card hF hP hQ] at h₂
  unfold fixedSpokes
  omega

namespace Construction
variable {V : Type*} [Fintype V] [DecidableEq V] {A : Finset (Sym2 V)}

noncomputable def looseOpposites (c : Construction A) (Q : Finset (Finset (Sym2 V))) :=
  let R := c.remainingEdges \ c.old
  looseRed c.remainingEdges R (fixedSpokes R c.typeTwo Q) c.newEdges

/-- Uniform-cut bound with the count of distinct uncovered red edges, rather
than a count of page pairs. The full graph is obtained by putting back the
first, type-one packing. -/
theorem uniform_cut (c : Construction A) {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) :
    2 * transversalNumber (trianglesOn A) + 2 * Q.card ≤
      3 * c.initial.card + 5 * c.first.card + 3 * c.typeTwo.card +
        (c.looseOpposites Q).card := by
  let R := c.remainingEdges \ c.old
  let W := fixedSpokes R c.typeTwo Q
  have hW : W ⊆ c.oldRemaining := by
    intro e he
    obtain ⟨hs,hn⟩ := mem_blueEdges.mp he
    have hp := support_mono (sdiff_subset.trans c.typeTwo_subset_rest) hs
    have hA := c.rest_support_subset hp
    apply mem_sdiff.mpr
    refine ⟨?_, (mem_sdiff.mp hA).2⟩
    by_contra h
    exact hn (mem_sdiff.mpr ⟨hA,h⟩)
  have hN : c.newEdges ⊆ c.remainingEdges \ c.oldRemaining := by
    rw [c.remaining_sdiff_oldRemaining,c.newEdges_eq_red_typeTwo]
    exact redEdges_subset_red _ _
  have h₂ := distinct_red_cut_cover hW hN (fun _ h => c.remaining_oldRemaining_ge_two h)
  rw [c.remaining_sdiff_oldRemaining] at h₂
  have hc : W.card + 2 * Q.card = 2 * c.typeTwo.card :=
    fixedSpokes_card (typeTwo_colored _ _) c.typeTwo_maximum
      (hQ.mono_family c.specialFamily_subset_typeTwo_residual)
  have ht := transversalNumber_le_add_residual (trianglesOn A) (support c.first)
    (fun _ h => trianglesOn_nonempty h)
  rw [← trianglesOn_sdiff] at ht
  change _ ≤ _ + transversalNumber (trianglesOn c.remainingEdges) at ht
  have ha := c.first_packing.card_support_uniform (fun T hT => trianglesOn_card (c.first_packing.1 hT))
  have ho := c.oldRemaining_card
  have hn := c.card_newEdges
  change 2 * transversalNumber (trianglesOn c.remainingEdges) ≤
    W.card + c.oldRemaining.card + c.newEdges.card + (c.looseOpposites Q).card at h₂
  omega

/-- The fifth row: charge the Wang private-edge saving before lifting the cover. -/
theorem private_residual_cover (c : Construction A) {Q : Finset (Finset (Sym2 V))}
    (hQ : IsMaximumPacking c.specialFamily Q) :
    3 * transversalNumber (trianglesOn A) + 3 * c.typeTwo.card +
      2 * (privateRedPages c.specialFamily c.newEdges Q).card ≤
      9 * c.initial.card + 8 * Q.card := by
  obtain ⟨D,hD⟩ := exists_maximumPacking (residual c.specialFamily (blueEdges c.newEdges Q))
  have hlocal := colored_bound hQ hD (Subset.refl _)
  have h₁ := transversalNumber_le_add_residual (trianglesOn A) (support c.first)
    (fun _ ht => trianglesOn_nonempty ht)
  rw [← trianglesOn_sdiff] at h₁
  change _ ≤ _ + transversalNumber (trianglesOn c.remainingEdges) at h₁
  have h₂ := transversalNumber_le_add_residual (trianglesOn c.remainingEdges)
    (support c.rest ∩ c.old) (fun _ ht => trianglesOn_nonempty ht)
  rw [← c.specialFamily_eq_residual] at h₂
  have ha := c.first_packing.card_support_uniform (fun T ht => trianglesOn_card (c.first_packing.1 ht))
  have hm := c.rest_packing.card_support_uniform (fun T ht => trianglesOn_card (c.rest_packing.1 ht))
  have hsplit := card_sdiff_add_card_inter (support c.rest) c.old
  change c.newEdges.card + _ = _ at hsplit
  rw [c.card_newEdges] at hsplit
  have hpack := c.first_rest_card_le
  unfold specialFamily at h₂ ⊢
  omega
end Construction
end TuzaBound

namespace TuzaBound
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A R : Finset (Sym2 V)} {P Q : Finset (Finset (Sym2 V))}

/-- The first colored row, with only the *distinct* loose red edges counted. -/
theorem distinct_colored_cover
    (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q) :
    transversalNumber (oneRedTriangles A R) + 2 * Q.card +
        (privateRedPages (oneRedTriangles A R) R P).card ≤
      3 * P.card + (looseRed A R (fixedSpokes R P Q) (redEdges R P)).card := by
  classical
  let F := oneRedTriangles A R
  let W := fixedSpokes R P Q
  let N := redEdges R P
  let L := looseRed A R W N
  let K := privateRedPages F R P
  let C := (W ∪ N) ∪ L
  have hF := oneRedTriangles_colored A R
  have hcov : IsCover F C := by
    apply cover_union_residual
    intro T hT
    have hp := (hF T (mem_residual.mp hT).1).2
    obtain ⟨e,he⟩ := card_pos.mp (show 0 < (T ∩ R).card by omega)
    exact ⟨e,mem_inter.mpr ⟨(mem_inter.mp he).1, mem_redEdges.mpr
      ⟨mem_support.mpr ⟨T,hT,(mem_inter.mp he).1⟩,(mem_inter.mp he).2⟩⟩⟩
  have hKP : K ⊆ P := privateRedPages_subset F R P
  have hs : K ⊆ P \ Layered.pairedParents R P Q := by
    intro T hT
    obtain ⟨hTP,hu⟩ := mem_privateRedPages.mp hT
    refine mem_sdiff.mpr ⟨hTP, ?_⟩
    intro h
    obtain ⟨_,q,hq,heq⟩ := Layered.mem_pairedParents.mp h
    exact Layered.residual_member_not_parent hF hQ hq
      ((hu q (mem_residual.mp (hQ.1 hq)).1 heq.symm).symm ▸ hTP)
  have hred : redEdges R K ⊆ C := by
    intro e he
    obtain ⟨hep,her⟩ := mem_redEdges.mp he
    exact mem_union_left _ (mem_union_right _ (mem_redEdges.mpr ⟨support_mono hKP hep,her⟩))
  have hblue : blueEdges R K ⊆ C := by
    intro e he
    obtain ⟨hep,her⟩ := mem_blueEdges.mp he
    exact mem_union_left _ (mem_union_left _ (mem_blueEdges.mpr ⟨support_mono hs hep,her⟩))
  have ht := (hcov.sdiff_privateRed hF hP.1 (Subset.refl K) hblue).number_le
  have hcut := card_sdiff_privateRed hF hP.1 (Subset.refl K) hred
  have hw := fixedSpokes_card hF hP hQ
  have hn := hP.1.card_redEdges hF
  have hc : C.card ≤ W.card + N.card + L.card := (card_union_le (W ∪ N) L).trans
    (Nat.add_le_add_right (card_union_le W N) L.card)
  change W.card + 2 * Q.card = 2 * P.card at hw
  change N.card = P.card at hn
  change transversalNumber F + 2*Q.card + K.card ≤ 3*P.card + L.card
  omega
end TuzaBound

namespace TuzaBound
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Coordinates with a distinguished parent, needed when a flip is to leave
or free a preselected spoke. -/
structure PairFace (V : Type*) where
  u : V
  v : V
  x : V
  y : V
  nodup : [u,v,x,y].Nodup

namespace PairFace
variable (g : PairFace V)
def first := triangleEdges g.u g.v g.x
def second := triangleEdges g.u g.v g.y
def alternate := triangleEdges g.u g.x g.y
def opposite := s(g.x,g.y)
def spine := s(g.u,g.v)
end PairFace

variable {A R : Finset (Sym2 V)} {P Q : Finset (Finset (Sym2 V))}
variable (hP : IsMaximumPacking (oneRedTriangles A R) P)
variable (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)

def RealizesPairs (g : {T // T ∈ Q} → PairFace V) : Prop :=
  ∀ q, (Layered.parent (oneRedTriangles_colored A R) hP hQ q).val = (g q).first ∧
    q.val = (g q).second ∧ (g q).spine ∈ R

theorem exists_pair_faces : ∃ g, RealizesPairs hP hQ g := by
  classical
  choose u v x y hp hq hs hn using paired_geometry hP hQ
  exact ⟨fun q => ⟨u q,v q,x q,y q,hn q⟩, fun q => ⟨hp q,hq q,hs q⟩⟩

/-- For every loose red edge, a pair having precisely that opposite is forced
by its witnessing uncovered triangle. This is the link between the cut's
distinct-edge count and the simultaneous rotations. -/
theorem loose_has_pair {g : {T // T ∈ Q} → PairFace V} (hg : RealizesPairs hP hQ g)
    {e : Sym2 V} (he : e ∈ looseRed A R (fixedSpokes R P Q) (redEdges R P)) :
    ∃ q, e = (g q).opposite := by
  classical
  let F := oneRedTriangles A R
  let hF := oneRedTriangles_colored A R
  obtain ⟨heS,heR⟩ := mem_redEdges.mp he
  obtain ⟨T,hTres,heT⟩ := mem_support.mp heS
  obtain ⟨hTF,havoid⟩ := mem_residual.mp hTres
  have havoidN := havoid.mono_right (subset_union_right :
    redEdges R P ⊆ fixedSpokes R P Q ∪ redEdges R P)
  have houtside : e ∉ redEdges R P := fun h => disjoint_left.mp havoidN heT h
  obtain ⟨p,hmeet⟩ := Books.exists_book_all_pages_meet_of_maximum
    (pages := Layered.twoLayerPages R P Q)
    (fun _ hS => hF.member_nonempty hS)
    (fun _ hf => Layered.choices_maximum hF hP hQ hf) hTF
  have hTp := hmeet p.val (Layered.mem_twoLayerPages.mpr (Or.inl rfl))
  have hpaired : p.val ∈ Layered.pairedParents R P Q := by
    by_contra h
    obtain ⟨f,hfT,hfp⟩ := not_disjoint_iff.mp hTp
    apply disjoint_left.mp havoid hfT
    by_cases hfR : f ∈ R
    · exact mem_union_right _ (mem_redEdges.mpr
        ⟨mem_support.mpr ⟨_, p.property, hfp⟩,hfR⟩)
    · exact mem_union_left _ (mem_blueEdges.mpr
        ⟨mem_support.mpr ⟨_, mem_sdiff.mpr ⟨p.property,h⟩,hfp⟩,hfR⟩)
  obtain ⟨_,U,hU,hred⟩ := Layered.mem_pairedParents.mp hpaired
  let q : {T // T ∈ Q} := ⟨U,hU⟩
  have hpar := Layered.parent_unique hF hP hQ q p hred
  obtain ⟨hfirst,hsecond,hsp⟩ := hg q
  have hp : p.val = (g q).first := (congrArg Subtype.val hpar).trans hfirst
  have hq : U = (g q).second := hsecond
  have hTU := hmeet U (Layered.mem_twoLayerPages.mpr (Or.inr ⟨hU,hred.symm⟩))
  have hspP : (g q).spine ∈ redEdges R P := mem_redEdges.mpr
    ⟨mem_support.mpr ⟨_,p.property,by rw [hp]; simp [PairFace.first,PairFace.spine]⟩,hsp⟩
  obtain ⟨f,hfT,hfp⟩ := not_disjoint_iff.mp hTp
  obtain ⟨j,hjT,hjU⟩ := not_disjoint_iff.mp hTU
  have hcases := two_page_triangle (mem_oneRedTriangles.mp hTF).1 (g q).nodup
    (fun h => disjoint_left.mp havoidN h hspP)
    ⟨f,mem_inter.mpr ⟨hfT,show f ∈ (g q).first from hp ▸ hfp⟩⟩ ⟨j,mem_inter.mpr ⟨hjT,show j ∈ (g q).second from hq ▸ hjU⟩⟩
  have hep : e ∉ (g q).first := fun h =>
    houtside (mem_redEdges.mpr ⟨mem_support.mpr ⟨_,p.property,hp.symm ▸ h⟩,heR⟩)
  have heq : e ∉ (g q).second := fun h =>
    houtside (residual_red_subset_parent_red hF hP (hQ.1 hU) (mem_inter.mpr ⟨hq.symm ▸ h,heR⟩))
  refine ⟨q,?_⟩
  rcases hcases with ht | ht <;> rw [ht] at heT <;>
    simp only [PairFace.first,PairFace.second,PairFace.opposite,mem_triangleEdges] at hep heq heT ⊢ <;> tauto

/-- A different representative is available for each distinct loose edge;
all representatives have a private red edge in the blue-deleted family. -/
theorem loose_representatives {g : {T // T ∈ Q} → PairFace V} (hg : RealizesPairs hP hQ g) :
    let L := looseRed A R (fixedSpokes R P Q) (redEdges R P)
    let K := privateRedPages (residual (oneRedTriangles A R) (blueEdges R P)) R Q
    ∃ f : {e // e ∈ L} → {T // T ∈ Q}, Function.Injective f ∧
      ∀ e, e.val = (g (f e)).opposite ∧ (f e).val ∈ K := by
  classical
  dsimp only
  choose f hf using fun e : {e // e ∈ looseRed A R (fixedSpokes R P Q) (redEdges R P)} =>
    loose_has_pair hP hQ hg e.property
  refine ⟨f, fun a b h => Subtype.ext ((hf a).trans ((congrArg (fun q => (g q).opposite) h).trans
    (hf b).symm)), ?_⟩
  intro e
  refine ⟨hf e, mem_privateRedPages.mpr ⟨(f e).property, ?_⟩⟩
  let q := f e
  let z := g q
  obtain ⟨hp,hy,hs⟩ := hg q
  have hparent : z.first ∈ P := hp ▸ (Layered.parent (oneRedTriangles_colored A R) hP hQ q).property
  have hpage : z.second ∈ residual (oneRedTriangles A R) (blueEdges R P) :=
    hy ▸ hQ.1 q.property
  obtain ⟨heSupp,heR⟩ := mem_redEdges.mp e.property
  obtain ⟨T,hTres,heT⟩ := mem_support.mp heSupp
  obtain ⟨ht,hd⟩ := mem_residual.mp hTres
  have heA := (mem_oneRedTriangles.mp ht).2.1 heT
  have hen : e.val ∉ redEdges R P := fun h => disjoint_left.mp hd heT (mem_union_right _ h)
  have heo : e.val = z.opposite := hf e
  unfold PairFace.opposite at heo
  have hu := unique_residual_triangle hP hparent hpage hs (heo ▸ heA) (heo ▸ heR) (heo ▸ hen)
  intro U hU hR
  have hsr : z.spine ∈ q.val ∩ R := mem_inter.mpr ⟨by rw [hy];simp [PairFace.spine,PairFace.second,z],hs⟩
  exact (hu U hU (mem_inter.mp (hR.symm ▸ hsr)).1).trans hy.symm

end TuzaBound

namespace TuzaBound
open Finset
variable {V : Type*} [DecidableEq V]

/-- Freeing a blue opposite by flipping a neighbouring two-page book introduces
no edge at either end of the original red spine. The books need only be
edge-disjoint, not vertex-disjoint. -/
theorem helper_flip_safe {u v x y p i t s' : V}
    (hu : [u,v,x,y].Nodup) (hp : [p,i,t,s'].Nodup)
    (hd : Disjoint (triangleEdges u v x ∪ triangleEdges u v y)
      (triangleEdges p i t ∪ triangleEdges p i s'))
    (hblue : s(x,y) ∈ triangleEdges p i t) (hn : s(x,y) ≠ s(p,i)) :
    s(x,y) ∉ triangleEdges p i s' ∧
      ∀ z, s(u,z) ∉ triangleEdges p i s' ∧ s(v,z) ∉ triangleEdges p i s' := by
  have spoke {a b : V} (ha : a = u ∨ a = v) (hb : b = x ∨ b = y) :
      s(a,b) ∈ triangleEdges u v x ∪ triangleEdges u v y := by
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp
  have hne {b a : V} (hb : b = x ∨ b = y) (ha : a = u ∨ a = v) :
      b ≠ a := by
    simp only [List.nodup_cons, List.mem_cons] at hu
    grind
  obtain ⟨b, hb, hbi⟩ : ∃ b : V, (b = x ∨ b = y) ∧ (b = p ∨ b = i) := by
    rcases mem_triangleEdges.mp hblue with h | h | h
    · exact (hn h).elim
    · rcases Sym2.eq_iff.mp h with h | h
      · exact ⟨x, Or.inl rfl, Or.inl h.1⟩
      · exact ⟨y, Or.inr rfl, Or.inl h.2⟩
    · rcases Sym2.eq_iff.mp h with h | h
      · exact ⟨x, Or.inl rfl, Or.inr h.1⟩
      · exact ⟨y, Or.inr rfl, Or.inr h.2⟩
  have away {a : V} (ha : a = u ∨ a = v) :
      a ≠ p ∧ a ≠ i ∧ a ≠ s' := by
    have hba := hne hb ha
    have hnot : s(a,b) ∉ triangleEdges p i s' := fun h =>
      disjoint_left.mp hd (spoke ha hb) (mem_union_right _ h)
    simp only [mem_triangleEdges, Sym2.eq_iff] at hnot
    grind
  constructor
  · intro h
    have h₁ := mem_triangleEdges.mp h
    have h₂ := mem_triangleEdges.mp hblue
    simp only [Sym2.eq_iff] at h₁ h₂ hn
    simp only [List.nodup_cons, List.mem_cons] at hp
    grind
  · intro z
    have h₁ := away (a := u) (Or.inl rfl)
    have h₂ := away (a := v) (Or.inr rfl)
    simp only [mem_triangleEdges, Sym2.eq_iff]
    grind

/-- Reorient a double book supported by a red matching in a complete
four-vertex graph. Both new pages have one red edge and share the blue spine. -/
theorem rotate_red_matching [Fintype V] {A R : Finset (Sym2 V)} {u v x y : V}
    (hn : [u,v,x,y].Nodup)
    (hp : triangleEdges u v x ∈ oneRedTriangles A R)
    (hq : triangleEdges u v y ∈ oneRedTriangles A R)
    (hs : s(u,v) ∈ R) (ha : s(x,y) ∈ A) (hr : s(x,y) ∈ R) :
    triangleEdges u x y ∈ oneRedTriangles A R ∧
    blueEdges R {triangleEdges u v x, triangleEdges u x y} = {s(u,x), s(v,x), s(u,y)} ∧
    support {triangleEdges u v x, triangleEdges u x y} ⊆
      insert s(x,y) (support {triangleEdges u v x, triangleEdges u v y}) := by
  classical
  obtain ⟨_, hAp, hpR⟩ := mem_oneRedTriangles.mp hp
  obtain ⟨_, hAq, hqR⟩ := mem_oneRedTriangles.mp hq
  have spoke {z : V} (hz : (triangleEdges u v z ∩ R).card = 1) (hu : u ≠ z) (hv : v ≠ z) :
      s(u,z) ∉ R ∧ s(v,z) ∉ R := by
    constructor
    · intro h
      have eq := red_edges_eq hz (e := s(u,z)) (f := s(u,v)) (by simp) h (by simp) hs
      exact hv (Sym2.congr_right.mp eq).symm
    · intro h
      have eq := red_edges_eq hz (e := s(v,z)) (f := s(u,v)) (by simp) h (by simp) hs
      simp only [Sym2.eq_iff] at eq
      grind
  have hn' : u ≠ v ∧ u ≠ x ∧ u ≠ y ∧ v ≠ x ∧ v ≠ y ∧ x ≠ y := by
    simpa [List.nodup_cons, and_assoc] using hn
  obtain ⟨_,hux,huy,hvx,hvy,hxy⟩ := hn'
  obtain ⟨huxB,hvxB⟩ := spoke hpR hux hvx
  obtain ⟨huyB,_⟩ := spoke hqR huy hvy
  refine ⟨mem_oneRedTriangles.mpr ⟨isTriangle_triangleEdges hux huy hxy, ?_, ?_⟩, ?_, ?_⟩
  · intro e he
    rcases mem_triangleEdges.mp he with rfl | rfl | rfl
    · exact hAp (by simp)
    · exact hAq (by simp)
    · exact ha
  · have h : triangleEdges u x y ∩ R = {s(x,y)} := by
      ext e
      simp only [mem_inter, mem_triangleEdges, mem_singleton]
      grind
    simp [h]
  · ext e
    simp only [mem_blueEdges, mem_support, mem_insert, mem_singleton,
      mem_triangleEdges, exists_eq_or_imp]
    aesop
  · intro e he
    simp only [mem_support, mem_insert, mem_singleton, mem_triangleEdges,
      exists_eq_or_imp] at he ⊢
    aesop

end TuzaBound

namespace TuzaBound
namespace Promotion

open Finset
variable {E I : Type*} [DecidableEq E] [Fintype I]

/-- The blue support after an arbitrary simultaneous choice of rotations. -/
def blueSupport (R : Finset E) (B : I → Finset (Finset E)) : Finset E :=
  univ.biUnion fun i => support (B i) \ R

theorem mem_blueSupport {R : Finset E} {B : I → Finset (Finset E)} {e : E} :
    e ∈ blueSupport R B ↔ ∃ i, e ∈ support (B i) ∧ e ∉ R := by
  classical
  simp [blueSupport]

/-- Every residual triangle has a unique owner. A single red edge meets
*every* page at that owner. This excludes in particular a rotated pair,
whose two red edges are different, even if it shares vertices with the
residual triangle. Distinct members of a residual packing get distinct owners. -/
theorem owner_injection
    {R : Finset E} {F D : Finset (Finset E)} {B : I → Finset (Finset E)}
    (hnum : ∀ T ∈ F, (T ∩ R).card ≤ 1)
    (hB : ∀ i, B i ⊆ F) (hne : ∀ i, (B i).Nonempty)
    (hd : Books.DisjointSupports B) (hchoice : Books.EveryChoiceMeets F B)
    (hD : IsPacking (residual F (blueSupport R B)) D) :
    ∃ f : {T // T ∈ D} → I, Function.Injective f ∧
      ∀ d, ∃ e ∈ d.val ∩ R, (∀ T ∈ B (f d), e ∈ T) ∧
        ∀ j T, T ∈ B j → ∀ x ∈ d.val, x ∈ T → x = e ∧ j = f d := by
  classical
  have info (d : {T // T ∈ D}) :
      ∃ i, ∃ e ∈ d.val ∩ R, (∀ T ∈ B i, e ∈ T) ∧
        ∀ j T, T ∈ B j → ∀ x ∈ d.val, x ∈ T → x = e ∧ j = i := by
    have hr := mem_residual.mp (hD.1 d.property)
    obtain ⟨i, hi⟩ := Books.exists_book_all_pages_meet hchoice hr.1
    obtain ⟨U, hU⟩ := hne i
    obtain ⟨e, hed, heU⟩ := not_disjoint_iff.mp (hi U hU)
    have red {j T x} (hT : T ∈ B j) (hxd : x ∈ d.val) (hxT : x ∈ T) : x ∈ R := by
      by_contra h
      exact disjoint_left.mp hr.2 hxd
        (mem_blueSupport.mpr ⟨j, mem_support.mpr ⟨T, hT, hxT⟩, h⟩)
    have heR := red hU hed heU
    have eqe {j T x} (hT : T ∈ B j) (hxd : x ∈ d.val) (hxT : x ∈ T) : x = e :=
      card_le_one.mp (hnum d.val hr.1) x (mem_inter.mpr ⟨hxd, red hT hxd hxT⟩)
        e (mem_inter.mpr ⟨hed, heR⟩)
    refine ⟨i, e, mem_inter.mpr ⟨hed, heR⟩, ?_, ?_⟩
    · intro T hT
      obtain ⟨x, hxd, hxT⟩ := not_disjoint_iff.mp (hi T hT)
      exact (eqe hT hxd hxT) ▸ hxT
    · intro j T hT x hxd hxT
      obtain rfl := eqe hT hxd hxT
      refine ⟨rfl, ?_⟩
      by_contra hij
      exact disjoint_left.mp (hd hij) (mem_support.mpr ⟨T, hT, hxT⟩)
        (mem_support.mpr ⟨U, hU, heU⟩)
  choose f e he hforce huniq using info
  refine ⟨f, ?_, fun d => ⟨e d, he d, hforce d, huniq d⟩⟩
  intro d d' h
  by_contra hne'
  have hv : d.val ≠ d'.val := fun hv => hne' (Subtype.ext hv)
  obtain ⟨T, hT⟩ := hne (f d)
  have hT' : T ∈ B (f d') := h ▸ hT
  have heq := card_le_one.mp (hnum T (hB _ hT))
    (e d) (mem_inter.mpr ⟨hforce d T hT, (mem_inter.mp (he d)).2⟩)
    (e d') (mem_inter.mpr ⟨hforce d' T hT', (mem_inter.mp (he d')).2⟩)
  exact disjoint_left.mp (hD.2 d.property d'.property hv)
    (mem_inter.mp (he d)).1 (heq.symm ▸ (mem_inter.mp (he d')).1)

end Promotion
end TuzaBound

namespace TuzaBound.Promotion
open Finset
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

/-- A maximum-size one-red selection is maximal in the target triangle family.
The target can also contain all-blue triangles. -/
def Saturates (A R : Finset (Sym2 V)) (F : Finset (Finset (Sym2 V))) (p : ℕ) : Prop :=
  ∀ S, IsPacking (oneRedTriangles A R) S → S.card = p → IsCover F (support S)

theorem choice_meets {A R : Finset (Sym2 V)} {F : Finset (Finset (Sym2 V))}
    {B : I → Finset (Finset (Sym2 V))}
    (hsat : Saturates A R F (Fintype.card I))
    (hB : ∀ i, B i ⊆ oneRedTriangles A R) (hd : Books.DisjointSupports B) :
    Books.EveryChoiceMeets F B := by
  intro f hf T hT
  have hp := Books.choice_isPacking hB hd hf
  have hc := Books.card_choice hd
    (fun i _ h => (oneRedTriangles_colored A R).member_nonempty (hB i h)) hf
  obtain ⟨e,he⟩ := hsat _ hp hc T hT
  obtain ⟨U,hU,heU⟩ := mem_support.mp (mem_inter.mp he).2
  obtain ⟨i,rfl⟩ := Books.mem_choice.mp hU
  exact ⟨i,fun h => disjoint_left.mp h (mem_inter.mp he).1 heU⟩

section
variable {E J : Type*} [DecidableEq E] [Fintype J]
noncomputable def fiber (f : J → I) (v : J → E) (i : I) : Finset E := by
  classical exact (univ.filter fun j => f j = i).image v

omit [Fintype I] in
theorem mem_fiber {f : J → I} {v : J → E} {i : I} {x : E} :
    x ∈ fiber f v i ↔ ∃ j, f j = i ∧ v j = x := by
  classical simp [fiber]

omit [Fintype I] in
theorem small_fiber {f : J → I} (hf : Function.Injective f) (v : J → E) (i : I) :
    (fiber f v i).card ≤ 1 := by
  apply card_le_one.mpr
  intro x hx y hy
  obtain ⟨a,ha,rfl⟩ := mem_fiber.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_fiber.mp hy
  exact congrArg v (hf (ha.trans hb.symm))

theorem sum_fiber (f : J → I) {v : J → E} (hv : Function.Injective v) :
    ∑ i, (fiber f v i).card = Fintype.card J := by
  classical
  have hd : ((univ : Finset I) : Set I).PairwiseDisjoint (fiber f v) := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,ha,rfl⟩ := mem_fiber.mp hx
    obtain ⟨b,hb,hv'⟩ := mem_fiber.mp hy
    exact hij (ha.symm.trans ((congrArg f (hv hv')).symm.trans hb))
  rw [← card_biUnion hd]
  have h : univ.biUnion (fiber f v) = univ.image v := by
    ext e
    simp only [mem_biUnion, mem_univ, true_and, mem_fiber, mem_image]
    grind
  rw [h,card_image_of_injective _ hv,card_univ]
end

/-- Promote one residual page at its forced owner. Only one extra page per
owner is possible; at a rotated owner no common red edge would be available. -/
theorem promote {A R : Finset (Sym2 V)} {F : Finset (Finset (Sym2 V))}
    {B : I → Finset (Finset (Sym2 V))}
    (hF : F ⊆ trianglesOn A) (hnum : ∀ T ∈ F, (T ∩ R).card ≤ 1)
    (hinc : oneRedTriangles A R ⊆ F)
    (hsat : Saturates A R F (Fintype.card I))
    (hB : ∀ i, B i ⊆ oneRedTriangles A R) (hne : ∀ i, (B i).Nonempty)
    (hd : Books.DisjointSupports B) (hsize : ∀ i, (B i).card ≤ 2)
    (hsp : ∀ i, ∃ e, ∀ T ∈ B i, e ∈ T) :
    ∃ k : ℕ,
      transversalNumber F + (∑ i, (B i).card) + k ≤ 4 * Fintype.card I ∧
      3 * transversalNumber F ≤ 3 * (blueSupport R B).card + 8*k := by
  classical
  let H := blueSupport R B
  let J := residual F H
  have hm := choice_meets hsat hB hd
  have hj : J = oneRedTriangles (A \ H) R := by
    rw [oneRedTriangles_sdiff]
    ext T
    constructor
    · intro hT
      obtain ⟨ht,hdis⟩ := mem_residual.mp hT
      obtain ⟨i,hi⟩ := Books.exists_book_all_pages_meet hm ht
      obtain ⟨U,hU⟩ := hne i
      obtain ⟨e,het,heu⟩ := not_disjoint_iff.mp (hi U hU)
      have heR : e ∈ R := by
        by_contra h
        exact disjoint_left.mp hdis het (mem_blueSupport.mpr
          ⟨i, mem_support.mpr ⟨_,hU,heu⟩,h⟩)
      have hpos := card_pos.mpr (show (T ∩ R).Nonempty from ⟨e, mem_inter.mpr ⟨het,heR⟩⟩)
      exact mem_residual.mpr ⟨mem_oneRedTriangles.mpr ⟨(mem_trianglesOn.mp (hF ht)).1,
        (mem_trianglesOn.mp (hF ht)).2, by have := hnum T ht; omega⟩,hdis⟩
    · intro h
      exact mem_residual.mpr ⟨hinc (mem_residual.mp h).1,(mem_residual.mp h).2⟩
  obtain ⟨D,hD⟩ := exists_maximumPacking J
  have hD' : IsMaximumPacking (oneRedTriangles (A \ H) R) D := hj ▸ hD
  have hbnd := colored_bound hD' (maximumPacking_spec _) (Subset.refl _)
  rw [← hj] at hbnd
  have hcost := transversalNumber_le_add_residual F H (fun _ h => trianglesOn_nonempty (hF h))
  change transversalNumber F ≤ H.card + transversalNumber J at hcost
  refine ⟨D.card,?_,by change 3 * transversalNumber F ≤ 3 * H.card + 8*D.card; omega⟩
  obtain ⟨f,hf,ho⟩ := owner_injection hnum (fun i => (hB i).trans hinc) hne hd hm hD.1
  let C := fiber f (fun d : {T // T ∈ D} => d.val)
  let B' := fun i => B i ∪ C i
  have hgood {d : {T // T ∈ D}} : d.val ∈ oneRedTriangles A R := by
    have h := hD'.1.1 d.property
    rw [oneRedTriangles_sdiff] at h
    exact (mem_residual.mp h).1
  have hjB (i : I) : B' i ⊆ oneRedTriangles A R := by
    intro T ht
    rcases mem_union.mp ht with h | h
    · exact hB i h
    · obtain ⟨d,_,rfl⟩ := mem_fiber.mp h
      exact hgood
  have hsep (i : I) : Disjoint (B i) (C i) := by
    apply disjoint_left.mpr
    intro T ht hc
    obtain ⟨d,hi,rfl⟩ := mem_fiber.mp hc
    have hcol := oneRedTriangles_colored A R _ (hB i ht)
    have hblue : (d.val \ R).Nonempty := by
      have h := card_sdiff_add_card_inter d.val R
      apply card_pos.mp
      omega
    obtain ⟨e,he⟩ := hblue
    exact disjoint_left.mp (mem_residual.mp (hD.1.1 d.property)).2 (mem_sdiff.mp he).1
      (mem_blueSupport.mpr ⟨i,mem_support.mpr ⟨_,ht,(mem_sdiff.mp he).1⟩,(mem_sdiff.mp he).2⟩)
  have hd' : Books.DisjointSupports B' := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨T,hT,hxT⟩ := mem_support.mp hxi
    obtain ⟨U,hU,hxU⟩ := mem_support.mp hxj
    rcases mem_union.mp hT with ht | ht <;> rcases mem_union.mp hU with hu | hu
    · exact disjoint_left.mp (hd hij) (mem_support.mpr ⟨_,ht,hxT⟩) (mem_support.mpr ⟨_,hu,hxU⟩)
    · obtain ⟨d,hj,rfl⟩ := mem_fiber.mp hu
      obtain ⟨e,_,_,hex⟩ := ho d
      exact hij ((hex i T ht x hxU hxT).2.trans hj)
    · obtain ⟨d,hi,rfl⟩ := mem_fiber.mp ht
      obtain ⟨e,_,_,hex⟩ := ho d
      exact hij (hi.symm.trans (hex j U hu x hxT hxU).2.symm)
    · obtain ⟨d,hi,rfl⟩ := mem_fiber.mp ht
      obtain ⟨d',hj,rfl⟩ := mem_fiber.mp hu
      apply disjoint_left.mp (hD.1.2 d.property d'.property ?_) hxT hxU
      intro heq
      exact hij (hi.symm.trans ((congrArg f (Subtype.ext heq)).trans hj))
  have hsp' (i : I) : ∃ e, ∀ T ∈ B' i, e ∈ T := by
    by_cases h : ∃ d, f d = i
    · obtain ⟨d,rfl⟩ := h
      obtain ⟨e,he,hh,_⟩ := ho d
      refine ⟨e,fun T ht => ?_⟩
      rcases mem_union.mp ht with h | h
      · exact hh T h
      · obtain ⟨d',ha,rfl⟩ := mem_fiber.mp h
        exact (hf ha).symm ▸ (mem_inter.mp he).1
    · obtain ⟨e,he⟩ := hsp i
      refine ⟨e,fun T ht => ?_⟩
      rcases mem_union.mp ht with ht | ht
      · exact he T ht
      · obtain ⟨d,hd,_⟩ := mem_fiber.mp ht
        exact (h ⟨d,hd⟩).elim
  have hc (i : I) : (B' i).card = (B i).card + (C i).card := card_union_of_disjoint (hsep i)
  obtain ⟨K,hK,hk⟩ := exists_cover_of_small_common_spine_books F B'
    (fun i => (hne i).mono subset_union_left)
    (fun i => by rw [hc]; have := hsize i; have := small_fiber hf Subtype.val i; change (C i).card ≤ 1 at this; omega)
    (fun i _ h => (mem_oneRedTriangles.mp (hjB i h)).1) hsp'
    (fun _ h => (mem_trianglesOn.mp (hF h)).1) (choice_meets hsat hjB hd')
  simp only [hc,sum_add_distrib] at hk
  have hsum : (∑ i, (C i).card) = D.card := by
    simpa [C] using sum_fiber f (v := Subtype.val) Subtype.val_injective
  have ht := hK.number_le
  omega
end TuzaBound.Promotion

namespace TuzaBound.Promotion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A A' R : Finset (Sym2 V)} {P Q F : Finset (Finset (Sym2 V))}

theorem layer_common {p : {T // T ∈ P}}
    (hp : p.val ∈ oneRedTriangles A R) :
    ∃ e, ∀ T ∈ Layered.twoLayerPages R P Q p, e ∈ T := by
  obtain ⟨e,he⟩ := card_pos.mp (show 0 < (p.val ∩ R).card by
    rw [(mem_oneRedTriangles.mp hp).2.2]; decide)
  refine ⟨e, fun T ht => ?_⟩
  rcases Layered.mem_twoLayerPages.mp ht with rfl | ⟨_,h⟩
  · exact (mem_inter.mp he).1
  · exact (mem_inter.mp (h.symm ▸ he)).1

theorem sum_layer_pages (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q) :
    (∑ p, (Layered.twoLayerPages R P Q p).card) = P.card + Q.card := by
  classical
  let hf := oneRedTriangles_colored A R
  let par := Layered.parent hf hP hQ
  have hc (p : {T // T ∈ P}) : Layered.children R Q p.val = fiber par Subtype.val p := by
    ext T
    constructor
    · intro h
      obtain ⟨ht,hr⟩ := Layered.mem_children.mp h
      exact mem_fiber.mpr ⟨⟨_,ht⟩,(Layered.parent_unique hf hP hQ _ p hr.symm).symm,rfl⟩
    · intro h
      obtain ⟨q,rfl,rfl⟩ := mem_fiber.mp h
      exact Layered.mem_children.mpr ⟨q.property,(Layered.parent_spec hf hP hQ q).symm⟩
  have hc' (p : {T // T ∈ P}) : (Layered.twoLayerPages R P Q p).card = (fiber par Subtype.val p).card + 1 := by
    rw [Layered.twoLayerPages,card_insert_of_notMem (Layered.parent_not_child hf hQ p),hc]
  simp_rw [hc']
  rw [sum_add_distrib,sum_fiber par Subtype.val_injective]
  simp [Nat.add_comm]

theorem blue_card_le_double {R : Finset (Sym2 V)} {X : Finset (Finset (Sym2 V))}
    (hx : X ⊆ oneRedTriangles A R) : (blueEdges R X).card ≤ 2*X.card := by
  classical
  have he : blueEdges R X = X.biUnion (fun T => T \ R) := by
    ext e
    simp only [mem_blueEdges,mem_support,mem_biUnion,mem_sdiff]
    grind
  rw [he]
  calc
    _ ≤ ∑ T ∈ X, (T \ R).card := card_biUnion_le
    _ = ∑ _T ∈ X, 2 := sum_congr rfl (fun _ ht => (oneRedTriangles_colored A R).member_blue_card (hx ht))
    _ = 2 * X.card := by simp [Nat.mul_comm]

/-- Simultaneously rotate one book per distinct loose red edge, then promote.
The outer one-red system on A locates opposite edges; all pages used for
selections live on A', allowing fixed all-blue singletons to be deleted. -/
theorem rotated_covers (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hp' : P ⊆ oneRedTriangles A' R) (hq' : Q ⊆ oneRedTriangles A' R)
    (hl' : looseRed A R (fixedSpokes R P Q) (redEdges R P) ⊆ A')
    (hF : F ⊆ trianglesOn A') (hnum : ∀ T ∈ F, (T ∩ R).card ≤ 1)
    (hinc : oneRedTriangles A' R ⊆ F) (hsat : Saturates A' R F P.card) :
    ∃ k : ℕ, transversalNumber F + Q.card + k ≤ 3*P.card ∧
      3*transversalNumber F + 3*(looseRed A R (fixedSpokes R P Q) (redEdges R P)).card ≤
        6*P.card + 6*Q.card + 8*k := by
  classical
  let L := looseRed A R (fixedSpokes R P Q) (redEdges R P)
  let hf := oneRedTriangles_colored A R
  let par := Layered.parent hf hP hQ
  let O := Layered.twoLayerPages R P Q
  obtain ⟨g,hg⟩ := exists_pair_faces hP hQ
  obtain ⟨rep,hirep,hrep⟩ := loose_representatives hP hQ hg
  let own := fun e : {x // x ∈ L} => par (rep e)
  have hinj : Function.Injective own := (Layered.parent_injective hf hP hQ).comp hirep
  let E := fiber own Subtype.val
  let Z := fun e : {x // x ∈ L} => g (rep e)
  let rot := fun e : {x // x ∈ L} => ({(Z e).first,(Z e).alternate} : Finset (Finset (Sym2 V)))
  let B := fun i : {T // T ∈ P} => if h : ∃ e, own e = i then rot h.choose else O i
  have hbrot (e : {x // x ∈ L}) : B (own e) = rot e := by
    dsimp only [B]
    have h : ∃ d, own d = own e := ⟨e,rfl⟩
    rw [dite_eq_left h]
    exact congrArg rot (hinj h.choose_spec)
  have horig (q : {T // T ∈ Q}) : O (par q) = {(g q).first, (g q).second} := by
    rw [show O (par q) = {(par q).val,q.val} from Layered.pages_eq_pair hf hQ _
      q.property (Layered.parent_spec hf hP hQ q).symm,(hg q).1,(hg q).2.1]
  have horigGood (i) : O i ⊆ oneRedTriangles A' R := by
    intro T ht
    rcases Layered.mem_twoLayerPages.mp ht with rfl | ⟨ht,_⟩
    · exact hp' i.property
    · exact hq' ht
  have hspec (e : {x // x ∈ L}) : rot e ⊆ oneRedTriangles A' R ∧
      (blueEdges R (rot e)).card ≤ 3 ∧
      support (rot e) ⊆ insert e.val (support (O (own e))) ∧
      (rot e).card = 2 ∧ (∃ s, ∀ T ∈ rot e, s ∈ T) := by
    let z := Z e
    have heo : e.val = s(z.x,z.y) := (hrep e).1
    have hpz : z.first ∈ oneRedTriangles A' R := (hg (rep e)).1 ▸ hp' (own e).property
    have hqz : z.second ∈ oneRedTriangles A' R := (hg (rep e)).2.1 ▸ hq' (rep e).property
    obtain ⟨hnew,hblue,hsub⟩ := rotate_red_matching z.nodup hpz hqz (hg (rep e)).2.2
      (heo ▸ hl' e.property) (heo ▸ (mem_redEdges.mp e.property).2)
    have hh : O (own e) = {z.first,z.second} := horig (rep e)
    have hne : z.first ≠ z.alternate := by
      intro heq
      have hv : s(z.u,z.v) ∈ triangleEdges z.u z.x z.y := show z.spine ∈ z.alternate from heq ▸ (show z.spine ∈ z.first by
        simp [PairFace.spine,PairFace.first])
      have hn := z.nodup
      simp only [List.nodup_cons,List.mem_cons] at hn
      simp only [mem_triangleEdges,Sym2.eq_iff] at hv
      grind
    change ({z.first,z.alternate} : Finset (Finset (Sym2 V))) ⊆ oneRedTriangles A' R ∧ (blueEdges R {z.first,z.alternate}).card ≤ 3 ∧
      support {z.first,z.alternate} ⊆ _ ∧ ({z.first,z.alternate} : Finset _).card = 2 ∧ (∃ s, ∀ T ∈ ({z.first,z.alternate} : Finset _), s ∈ T)
    refine ⟨by rw [insert_subset_iff,singleton_subset_iff]; exact ⟨hpz,hnew⟩, ?_,
      ?_,by simp [hne],?_⟩
    · change (blueEdges R {triangleEdges z.u z.v z.x,triangleEdges z.u z.x z.y}).card ≤ 3
      rw [hblue]; exact card_le_three
    · rw [heo,hh]; exact hsub
    · exact ⟨s(z.u,z.x), by
        intro T ht
        rcases mem_insert.mp ht with rfl | ht
        · simp [PairFace.first,z,Z]
        · rw [mem_singleton.mp ht]; simp [PairFace.alternate,z,Z]⟩
  have hfree {e : Sym2 V} (he : e ∈ L) (i) : e ∉ support (O i) := by
    obtain ⟨heS,hr⟩ := mem_redEdges.mp he
    obtain ⟨T,ht,heT⟩ := mem_support.mp heS
    have hN : e ∉ redEdges R P := fun h => disjoint_left.mp (mem_residual.mp ht).2 heT (mem_union_right _ h)
    intro hs
    obtain ⟨U,hu,heu⟩ := mem_support.mp hs
    rcases Layered.mem_twoLayerPages.mp hu with rfl | ⟨hu,_⟩
    · exact hN (mem_redEdges.mpr ⟨mem_support.mpr ⟨_,i.property,heu⟩,hr⟩)
    · exact hN (residual_red_subset_parent_red hf hP (hQ.1 hu) (mem_inter.mpr ⟨heu,hr⟩))
  have hOsize (i) : (O i).card ≤ 2 := by
    dsimp only [O,Layered.twoLayerPages]
    have := Layered.children_card_le_one hf hQ i.val
    rw [card_insert_of_notMem (Layered.parent_not_child hf hQ i)]; omega
  have hcases (i) : (B i ⊆ oneRedTriangles A' R) ∧ (B i).card = (O i).card ∧
      support (B i) ⊆ support (O i) ∪ E i ∧
      (blueEdges R (B i)).card + (E i).card ≤ 2 * (B i).card ∧
      ∃ s, ∀ T ∈ B i, s ∈ T := by
    by_cases h : ∃ e, own e = i
    · obtain ⟨e,rfl⟩ := h
      rw [hbrot]
      obtain ⟨h₁,h₂,h₃,h₄,h₅⟩ := hspec e
      have ho2 : (O (own e)).card = 2 := Layered.pages_card_paired hf hQ _ (Layered.mem_pairedParents.mpr
        ⟨(own e).property,_,(rep e).property,Layered.parent_spec hf hP hQ _⟩)
      refine ⟨h₁,h₄.trans ho2.symm,?_,?_,h₅⟩
      · intro x hx
        rcases mem_insert.mp (h₃ hx) with rfl | hx
        · exact mem_union_right _ (mem_fiber.mpr ⟨e,rfl,rfl⟩)
        · exact mem_union_left _ hx
      · have h := small_fiber hinj Subtype.val (own e)
        change (E (own e)).card ≤ 1 at h
        omega
    · rw [show B i = O i from dite_eq_right h]
      have hem : E i = ∅ := by
        apply not_nonempty_iff_eq_empty.mp
        rintro ⟨x,hx⟩
        obtain ⟨e,hi,_⟩ := mem_fiber.mp hx
        exact h ⟨e,hi⟩
      rw [hem]
      exact ⟨horigGood i,rfl,subset_union_left,by simpa using blue_card_le_double (horigGood i),
        layer_common (hp' i.property)⟩
  have hD : Books.DisjointSupports B := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hi hj
    rcases mem_union.mp ((hcases i).2.2.1 hi) with hi | hi <;>
      rcases mem_union.mp ((hcases j).2.2.1 hj) with hj | hj
    · exact disjoint_left.mp (Layered.supports_disjoint hf hP hQ hij) hi hj
    · obtain ⟨e,_,rfl⟩ := mem_fiber.mp hj
      exact hfree e.property i hi
    · obtain ⟨e,_,rfl⟩ := mem_fiber.mp hi
      exact hfree e.property j hj
    · obtain ⟨e,he,rfl⟩ := mem_fiber.mp hi
      obtain ⟨d,hd,hde⟩ := mem_fiber.mp hj
      exact hij (he.symm.trans ((congrArg own (Subtype.ext hde)).symm.trans hd))
  have hsum : (∑ i, (B i).card) = P.card + Q.card := by
    simp_rw [fun i => (hcases i).2.1]
    exact sum_layer_pages hP hQ
  have hblue : (blueSupport R B).card + L.card ≤ 2 * (P.card + Q.card) := by
    have h := sum_le_sum (s := (univ : Finset {T // T ∈ P})) (fun i _ => (hcases i).2.2.2.1)
    rw [sum_add_distrib,← mul_sum,hsum] at h
    have he : (∑ i, (E i).card) = L.card := by
      simpa [E] using sum_fiber own (v := Subtype.val) Subtype.val_injective
    have hu : (blueSupport R B).card ≤ ∑ i, (blueEdges R (B i)).card := card_biUnion_le
    omega
  have hne (i) : (B i).Nonempty := card_pos.mp (by
    rw [(hcases i).2.1]; exact card_pos.mpr (Layered.pages_nonempty R P Q i))
  obtain ⟨k,hr₁,hr₂⟩ := promote hF hnum hinc (by simpa using hsat) (fun i => (hcases i).1)
    hne hD (fun i => (hcases i).2.1.symm ▸ hOsize i) (fun i => (hcases i).2.2.2.2)
  rw [hsum,Fintype.card_coe] at hr₁
  change ∃ k, _ ∧ 3 * transversalNumber F + 3*L.card ≤ 6*P.card+6*Q.card+8*k
  exact ⟨k,by omega,by omega⟩
end TuzaBound.Promotion

namespace TuzaBound.Construction
open Finset Promotion
variable {V : Type*} [Fintype V] [DecidableEq V] {A : Finset (Sym2 V)} (c : Construction A)

def paint := c.remainingEdges \ c.old
noncomputable def blanks := c.rest \ c.typeTwo
noncomputable def cleared := c.remainingEdges \ support c.blanks

theorem blanks_old : support c.blanks ⊆ c.old := by
  intro x hx
  obtain ⟨T,ht,hex⟩ := mem_support.mp hx
  obtain ⟨hr,hn⟩ := mem_sdiff.mp ht
  by_contra h
  have hT := c.rest_packing.1 hr
  exact hn (mem_inter.mpr ⟨hr,new_edge_forces_typeTwo hT (c.remaining_old_ge_two hT)
    (mem_sdiff.mpr ⟨hex,h⟩)⟩)

theorem colored_parents : IsMaximumPacking (oneRedTriangles c.remainingEdges c.paint) c.typeTwo := by
  rw [paint,← typeTwo_eq_oneRed]
  exact c.typeTwo_maximum

theorem colored_children : c.specialFamily ⊆ residual (oneRedTriangles c.remainingEdges c.paint)
    (blueEdges c.paint c.typeTwo) := by
  unfold paint; rw [← typeTwo_eq_oneRed]; exact c.specialFamily_subset_typeTwo_residual

theorem parents_clear : c.typeTwo ⊆ oneRedTriangles c.cleared c.paint := by
  unfold cleared; rw [oneRedTriangles_sdiff]
  intro T ht
  refine mem_residual.mpr ⟨c.colored_parents.1.1 ht,disjoint_left.mpr ?_⟩
  intro x hx hx'
  obtain ⟨U,hu,hxU⟩ := mem_support.mp hx'
  obtain ⟨hur,hun⟩ := mem_sdiff.mp hu
  exact disjoint_left.mp (c.rest_packing.2 hur (c.typeTwo_subset_rest ht)
    (fun heq => hun (heq.symm ▸ ht))) hxU hx

theorem special_clear : c.specialFamily ⊆ oneRedTriangles c.cleared c.paint := by
  unfold cleared; rw [oneRedTriangles_sdiff]
  intro T ht
  have h := mem_residual.mp (c.specialFamily_eq_residual ▸ ht)
  exact mem_residual.mpr ⟨(mem_residual.mp (c.colored_children ht)).1,
    h.2.mono_right (fun _ he => mem_inter.mpr ⟨support_mono sdiff_subset he,c.blanks_old he⟩)⟩

theorem loose_clear {Q : Finset (Finset (Sym2 V))} :
    looseRed c.remainingEdges c.paint (fixedSpokes c.paint c.typeTwo Q)
      (redEdges c.paint c.typeTwo) ⊆ c.cleared := by
  intro e he
  obtain ⟨hA,hn⟩ := mem_sdiff.mp (mem_redEdges.mp he).2
  exact mem_sdiff.mpr ⟨hA,fun h => hn (c.blanks_old h)⟩

theorem clear_num {T : Finset (Sym2 V)} (h : T ∈ trianglesOn c.cleared) :
    (T ∩ c.paint).card ≤ 1 := by
  have ht : T ∈ trianglesOn c.remainingEdges :=
    mem_trianglesOn.mpr ⟨(mem_trianglesOn.mp h).1,(mem_trianglesOn.mp h).2.trans sdiff_subset⟩
  exact (card_le_card (show T ∩ c.paint ⊆ T \ c.old from fun e he => mem_sdiff.mpr
    ⟨(mem_inter.mp he).1,(mem_sdiff.mp (mem_inter.mp he).2).2⟩)).trans (c.remaining_new_le_one ht)

/-- Put the all-blue singletons back. Any size-b one-red selection avoiding
them now has the same two objective values as the lexicographic maximizer. -/
theorem clear_saturates : Saturates c.cleared c.paint (trianglesOn c.cleared) c.typeTwo.card := by
  intro S hs hcard
  let U := typeFamily c.remainingEdges c.old 2
  have hsU : S ⊆ U := by
    dsimp only [U]
    rw [typeTwo_eq_oneRed]
    intro T ht
    have h := hs.1 ht
    unfold cleared at h
    rw [oneRedTriangles_sdiff] at h
    exact (mem_residual.mp h).1
  have hbs := c.rest_packing.subfamily (sdiff_subset : c.blanks ⊆ c.rest)
  have hd : Disjoint (support S) (support c.blanks) := by
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨T,ht,het⟩ := mem_support.mp he
    exact (mem_sdiff.mp ((mem_oneRedTriangles.mp (hs.1 ht)).2.1 het)).2 he'
  have hs' : IsPacking (trianglesOn c.remainingEdges) S :=
    ⟨hsU.trans (typeFamily_subset _ _ _),hs.2⟩
  have hunion := hs'.union hbs hd
  have hint : (S ∪ c.blanks) ∩ U = S := by
    ext T
    constructor
    · intro ht
      obtain ⟨ht,hu⟩ := mem_inter.mp ht
      rcases mem_union.mp ht with ht | ht
      · exact ht
      · obtain ⟨hr,hn⟩ := mem_sdiff.mp ht
        exact (hn (mem_inter.mpr ⟨hr,hu⟩)).elim
    · intro ht
      exact mem_inter.mpr ⟨mem_union_left _ ht,hsU ht⟩
  have hsame₁ : ((S ∪ c.blanks) ∩ U).card = c.typeTwo.card := by rw [hint,hcard]
  have hsame₂ : (S ∪ c.blanks).card = c.rest.card := by
    rw [card_union_of_disjoint (disjoint_of_support_disjoint
      (fun _ ht => trianglesOn_nonempty (hs'.1 ht)) hd)]
    have h : c.blanks.card + c.typeTwo.card = c.rest.card := card_sdiff_add_card_eq_card c.typeTwo_subset_rest
    omega
  have hm := c.rest_lexMaximum.of_same_counts hunion hsame₁ hsame₂
  intro T hT
  have hT' : T ∈ residual (trianglesOn c.remainingEdges) (support c.blanks) := by
    rw [← trianglesOn_sdiff]; exact hT
  obtain ⟨e,he⟩ := hm.meets_support (mem_residual.mp hT').1 (trianglesOn_nonempty hT)
  obtain ⟨heT,heS⟩ := mem_inter.mp he
  obtain ⟨U,hU,heU⟩ := mem_support.mp heS
  rcases mem_union.mp hU with hU | hU
  · exact ⟨e,mem_inter.mpr ⟨heT,mem_support.mpr ⟨_,hU,heU⟩⟩⟩
  · exact (disjoint_left.mp (mem_residual.mp hT').2 heT (mem_support.mpr ⟨_,hU,heU⟩)).elim

theorem lift_clear : transversalNumber (trianglesOn A) + 3*c.typeTwo.card ≤
    3*c.initial.card + transversalNumber (trianglesOn c.cleared) := by
  have h₁ := transversalNumber_le_add_residual (trianglesOn A) (support c.first)
    (fun _ ht => trianglesOn_nonempty ht)
  rw [← trianglesOn_sdiff] at h₁
  change _ ≤ _ + transversalNumber (trianglesOn c.remainingEdges) at h₁
  have h₂ := transversalNumber_le_add_residual (trianglesOn c.remainingEdges) (support c.blanks)
    (fun _ ht => trianglesOn_nonempty ht)
  rw [← trianglesOn_sdiff] at h₂
  change _ ≤ _ + transversalNumber (trianglesOn c.cleared) at h₂
  have hs := c.first_packing.card_support_uniform (fun T ht => trianglesOn_card (c.first_packing.1 ht))
  have hb := c.rest_packing.subfamily (sdiff_subset : c.blanks ⊆ c.rest)
  have hb' : (support c.blanks).card = 3 * c.blanks.card :=
    hb.card_support_uniform (fun T ht => trianglesOn_card (hb.1 ht))
  have h : c.blanks.card + c.typeTwo.card = c.rest.card := card_sdiff_add_card_eq_card c.typeTwo_subset_rest
  have hn := c.first_rest_card_le
  omega

theorem rotation_rows {Q : Finset (Finset (Sym2 V))} (hQ : IsPacking c.specialFamily Q) :
    ∃ k, transversalNumber (trianglesOn A) + Q.card + k ≤ 3*c.initial.card ∧
      3*transversalNumber (trianglesOn A) + 3*c.typeTwo.card + 3*(c.looseOpposites Q).card ≤
        9*c.initial.card + 6*Q.card + 8*k := by
  obtain ⟨k,h₁,h₂⟩ := rotated_covers c.colored_parents (hQ.mono_family c.colored_children)
    c.parents_clear (hQ.1.trans c.special_clear) c.loose_clear (Subset.refl _) (fun _ h => c.clear_num h)
    oneRedTriangles_subset c.clear_saturates
  unfold looseOpposites
  rw [c.newEdges_eq_red_typeTwo]
  change ∃ k, _ ∧ 3*transversalNumber (trianglesOn A) + 3*c.typeTwo.card +
    3*(looseRed c.remainingEdges c.paint (fixedSpokes c.paint c.typeTwo Q)
      (redEdges c.paint c.typeTwo)).card ≤ _
  have := c.lift_clear
  exact ⟨k,by omega,by omega⟩
end TuzaBound.Construction

namespace TuzaBound.Promotion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A R A' : Finset (Sym2 V)} {P Q F : Finset (Finset (Sym2 V))}
variable (hP : IsMaximumPacking (oneRedTriangles A R) P)
variable (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
variable {g : {T // T ∈ Q} → PairFace V} (hg : RealizesPairs hP hQ g)

include hg in
theorem layer_support_pair (q : {T // T ∈ Q}) :
    support (Layered.twoLayerPages R P Q (Layered.parent (oneRedTriangles_colored A R) hP hQ q)) =
      (g q).first ∪ (g q).second := by
  rw [Layered.pages_eq_pair (oneRedTriangles_colored A R) hQ _ q.property
    (Layered.parent_spec (oneRedTriangles_colored A R) hP hQ q).symm,(hg q).1,(hg q).2.1]
  simp [support]

omit [Fintype V] in
theorem core_unpaired (i : {T // T ∈ P}) (hi : i.val ∉ Layered.pairedParents R P Q) :
    i.val ⊆ fixedSpokes R P Q ∪ redEdges R P := by
  intro e he
  by_cases hr : e ∈ R
  · exact mem_union_right _ (mem_redEdges.mpr ⟨mem_support.mpr ⟨_,i.property,he⟩,hr⟩)
  · exact mem_union_left _ (mem_blueEdges.mpr ⟨mem_support.mpr
      ⟨_,mem_sdiff.mpr ⟨i.property,hi⟩,he⟩,hr⟩)

include hg in
/-- With a potential third page at q, every other book has a page missing both
that third page W and the uncovered face T. Only a parent containing the
opposite of q might need switching. -/
theorem other_avoiding_pages (q : {T // T ∈ Q}) {T W : Finset (Sym2 V)}
    (ht : T ⊆ insert (g q).opposite ((g q).first ∪ (g q).second))
    (heo : (g q).opposite ∈ T)
    (hcore : Disjoint T (fixedSpokes R P Q ∪ redEdges R P))
    (hw : W ∈ residual (oneRedTriangles A R) (blueEdges R P))
    (hws : (g q).spine ∈ W)
    (j : {T // T ∈ P}) (hj : j ≠ Layered.parent (oneRedTriangles_colored A R) hP hQ q) :
    ∃ U ∈ Layered.twoLayerPages R P Q j, Disjoint T U ∧ Disjoint W U := by
  classical
  let hF := oneRedTriangles_colored A R
  let par := Layered.parent hF hP hQ
  let O := Layered.twoLayerPages R P Q
  let z := g q
  have hp := (hg q).1
  have hsp : z.spine ∈ (par q).val := by rw [hp]; simp [z,PairFace.spine,PairFace.first]
  have away : Disjoint (z.first ∪ z.second) (support (O j)) := by
    rw [← layer_support_pair hP hQ hg q]
    exact Layered.supports_disjoint hF hP hQ (Ne.symm hj)
  have avoid {U : Finset (Sym2 V)} (hu : U ∈ O j) (ho : z.opposite ∉ U) : Disjoint T U := by
    apply disjoint_left.mpr
    intro x hx hxu
    rcases mem_insert.mp (ht hx) with rfl | hx
    · exact ho hxu
    · exact disjoint_left.mp away hx (mem_support.mpr ⟨_,hu,hxu⟩)
  by_cases he : z.opposite ∈ j.val
  · have hpaired : j.val ∈ Layered.pairedParents R P Q := by
      by_contra h
      exact disjoint_left.mp hcore heo (core_unpaired j h he)
    obtain ⟨_,U,hU,hred⟩ := Layered.mem_pairedParents.mp hpaired
    let s : {T // T ∈ Q} := ⟨U,hU⟩
    have hjs : j = par s := Layered.parent_unique hF hP hQ s j hred
    let z' := g s
    have hp' : j.val = z'.first := (congrArg Subtype.val hjs).trans (hg s).1
    have hs' : U = z'.second := (hg s).2.1
    have hdis : Disjoint (z.first ∪ z.second) (z'.first ∪ z'.second) := by
      rw [← layer_support_pair hP hQ hg s]
      change Disjoint (z.first ∪ z.second) (support (O (par s)))
      rwa [← hjs]
    have hns : z.opposite ≠ z'.spine := by
      intro heq
      exact disjoint_left.mp hcore heo (mem_union_right _ (mem_redEdges.mpr ⟨mem_support.mpr
        ⟨_,j.property,he⟩,heq.symm ▸ (hg s).2.2⟩))
    have hf := helper_flip_safe z.nodup z'.nodup hdis (show z.opposite ∈ z'.first from hp' ▸ he) hns
    have hu : U ∈ O j := Layered.mem_twoLayerPages.mpr (Or.inr ⟨hU,hred.symm⟩)
    refine ⟨U,hu,avoid hu (by rw [hs']; exact hf.1),?_⟩
    obtain ⟨w,_,_,heq⟩ := (mem_oneRedTriangles.mp (mem_residual.mp hw).1).1.exists_third_of_mem hws
    rw [heq,hs']
    apply disjoint_left.mpr
    intro x hx hx'
    rcases mem_triangleEdges.mp hx with rfl | rfl | rfl
    · exact (hf.2 z.v).1 hx'
    · exact (hf.2 w).1 hx'
    · exact (hf.2 w).2 hx'
  · have hmem : j.val ∈ O j := Layered.mem_twoLayerPages.mpr (Or.inl rfl)
    refine ⟨j.val,hmem,avoid hmem he,disjoint_left.mpr ?_⟩
    intro x hx hx'
    have hr : x ∈ R := by
      by_contra hn
      exact disjoint_left.mp (mem_residual.mp hw).2 hx
        (mem_blueEdges.mpr ⟨mem_support.mpr ⟨_,j.property,hx'⟩,hn⟩)
    have heq := red_edges_eq (mem_oneRedTriangles.mp (mem_residual.mp hw).1).2.2 hx hr hws (hg q).2.2
    exact disjoint_left.mp (hP.1.2 j.property (par q).property (fun h => hj (Subtype.ext h))) hx'
      (heq.symm ▸ hsp)

/-- Contradiction from an avoiding selection with one exceptional page. -/
theorem no_escaping_choice {B : {T // T ∈ P} → Finset (Finset (Sym2 V))}
    (hd : Books.DisjointSupports B) (hB : ∀ i, B i ⊆ oneRedTriangles A' R)
    (hsat : Saturates A' R F P.card) {T W : Finset (Sym2 V)} (hT : T ∈ F)
    (hW : W ∈ oneRedTriangles A' R) (htW : Disjoint T W)
    (i : {T // T ∈ P})
    (hother : ∀ j, j ≠ i → ∃ U ∈ B j, Disjoint T U ∧ Disjoint W U) : False := by
  classical
  have H (j : {T // T ∈ P}) : ∃ U, U ∈ oneRedTriangles A' R ∧ Disjoint T U ∧
      (j = i → U = W) ∧ (j ≠ i → U ∈ B j ∧ Disjoint W U) := by
    by_cases he : j = i
    · exact ⟨W,hW,htW,fun _ => rfl,fun h => (h he).elim⟩
    · obtain ⟨U,hU,ht,hw⟩ := hother j he
      exact ⟨U,hB _ hU,ht,fun h => (he h).elim,fun _ => ⟨hU,hw⟩⟩
  choose f hgood hav hei hne using H
  let B' := fun j => ({f j} : Finset (Finset (Sym2 V)))
  have hd' : Books.DisjointSupports B' := by
    intro j k hjk
    change Disjoint (support {f j}) (support {f k})
    simp only [support,singleton_biUnion,id_eq]
    by_cases hj : j = i
    · rw [hei _ hj]
      exact (hne k (fun h => hjk (hj.trans h.symm))).2
    by_cases hk : k = i
    · rw [hei _ hk]; exact (hne j hj).2.symm
    exact (hd hjk).mono (Books.page_subset_support (hne j hj).1) (Books.page_subset_support (hne k hk).1)
  have hg' (j) : B' j ⊆ oneRedTriangles A' R := singleton_subset_iff.mpr (hgood j)
  obtain ⟨j,hj⟩ := choice_meets (by simpa using hsat) hg' hd' f (fun _ => mem_singleton_self _) T hT
  exact hj (hav j)
end TuzaBound.Promotion

namespace TuzaBound.Promotion
open Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A R A' : Finset (Sym2 V)} {P Q K F : Finset (Finset (Sym2 V))}

/-- A two-page book needs an extra cover edge only when no suitable third page
exists. K is the exceptional set (private pages in the construction). -/
theorem safe_cover (hP : IsMaximumPacking (oneRedTriangles A R) P)
    (hQ : IsPacking (residual (oneRedTriangles A R) (blueEdges R P)) Q)
    (hp' : P ⊆ oneRedTriangles A' R) (hq' : Q ⊆ oneRedTriangles A' R)
    (hF : F ⊆ trianglesOn A') (hsat : Saturates A' R F P.card)
    (hK : K ⊆ Q) (hthird : ∀ q ∈ Q, q ∉ K → ∀ e ∈ q ∩ R,
      ∃ W ∈ residual (oneRedTriangles A R) (blueEdges R P), W ∈ oneRedTriangles A' R ∧
        e ∈ W ∧ W ≠ q) :
    transversalNumber F + 2*Q.card ≤ 3*P.card + K.card := by
  classical
  let hcol := oneRedTriangles_colored A R
  let par := Layered.parent hcol hP hQ
  let B := Layered.twoLayerPages R P Q
  let N := redEdges R P
  let X := fixedSpokes R P Q
  obtain ⟨g,hg⟩ := exists_pair_faces hP hQ
  let extra := K.attach.image (fun q => (g ⟨q.val,hK q.property⟩).opposite)
  let C := (X ∪ N) ∪ extra
  have hd := Layered.supports_disjoint hcol hP hQ
  have hB (j) : B j ⊆ oneRedTriangles A' R := by
    intro T ht
    rcases Layered.mem_twoLayerPages.mp ht with rfl | ⟨ht,_⟩
    · exact hp' j.property
    · exact hq' ht
  have hcov : IsCover F C := by
    intro T hT
    by_contra hn
    have hdis : Disjoint T C := disjoint_left.mpr (fun x hx hx' => hn ⟨_,mem_inter.mpr ⟨hx,hx'⟩⟩)
    have hcore : Disjoint T (X ∪ N) := hdis.mono_right subset_union_left
    obtain ⟨j,hj⟩ := Books.exists_book_all_pages_meet (choice_meets (by simpa using hsat) hB hd) hT
    have hfirst := hj j.val (Layered.mem_twoLayerPages.mpr (Or.inl rfl))
    have hpair : j.val ∈ Layered.pairedParents R P Q := by
      by_contra h
      exact hfirst (hcore.mono_right (core_unpaired j h))
    obtain ⟨_,U,hu,hred⟩ := Layered.mem_pairedParents.mp hpair
    let q : {T // T ∈ Q} := ⟨U,hu⟩
    let z := g q
    have hjp : j = par q := Layered.parent_unique hcol hP hQ q j hred
    have hp : j.val = z.first := (congrArg Subtype.val hjp).trans (hg q).1
    have hq : U = z.second := (hg q).2.1
    have hsecond := hj U (Layered.mem_twoLayerPages.mpr (Or.inr ⟨hu,hred.symm⟩))
    have hsj : z.spine ∈ j.val := by rw [hp]; simp [PairFace.spine,PairFace.first]
    have hsu : z.spine ∈ U := by rw [hq]; simp [PairFace.spine,PairFace.second]
    have hspT : z.spine ∉ T := fun h => disjoint_left.mp hcore h (mem_union_right _
      (mem_redEdges.mpr ⟨mem_support.mpr ⟨_,j.property,hsj⟩,(hg q).2.2⟩))
    rw [hp] at hfirst
    rw [hq] at hsecond
    have meet {S : Finset (Sym2 V)} (h : ¬ Disjoint T S) : (T ∩ S).Nonempty := by
      obtain ⟨e,he,he'⟩ := not_disjoint_iff.mp h
      exact ⟨_,mem_inter.mpr ⟨he,he'⟩⟩
    have htri := (mem_trianglesOn.mp (hF hT)).1
    have shape := two_page_triangle htri z.nodup hspT (meet hfirst) (meet hsecond)
    have heo : z.opposite ∈ T := by rcases shape with ht | ht <;> rw [ht] <;> simp [PairFace.opposite]
    by_cases hk : U ∈ K
    · exact disjoint_left.mp hdis heo (mem_union_right _ (mem_image.mpr ⟨⟨U,hk⟩,mem_attach _ _,rfl⟩))
    obtain ⟨W,hw,hW',hws,hnW⟩ := hthird U hu hk z.spine (mem_inter.mpr ⟨hsu,(hg q).2.2⟩)
    obtain ⟨w,huw,hvw,heq⟩ := (mem_oneRedTriangles.mp (mem_residual.mp hw).1).1.exists_third_of_mem hws
    have hne : W ≠ j.val := by
      intro he
      have hblue := hcol.member_blue_card (hP.1.1 j.property)
      obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (j.val \ R).card by omega)
      exact disjoint_left.mp (mem_residual.mp hw).2 (he.symm ▸ (mem_sdiff.mp hx).1)
        (mem_blueEdges.mpr ⟨mem_support.mpr ⟨_,j.property,(mem_sdiff.mp hx).1⟩,(mem_sdiff.mp hx).2⟩)
    have hxw : z.x ≠ w := fun h => hne (by rw [heq,hp,← h]; rfl)
    have hyw : z.y ≠ w := fun h => hnW (by rw [heq,hq,← h]; rfl)
    have h5 : [z.u,z.v,z.x,z.y,w].Nodup := by
      have h := z.nodup
      simp_all [List.nodup_cons]
    have htW : Disjoint T W := by
      apply disjoint_left.mpr
      intro e he he'
      exact hspT (three_page_spine htri h5 (meet hfirst) (meet hsecond)
        ⟨_,mem_inter.mpr ⟨he,heq ▸ he'⟩⟩)
    have hsub : T ⊆ insert z.opposite (z.first ∪ z.second) := by
      intro e he
      rcases shape with h | h <;> rw [h] at he <;>
        rcases mem_triangleEdges.mp he with rfl | rfl | rfl <;>
        simp [PairFace.first,PairFace.second,PairFace.opposite]
    exact no_escaping_choice hd hB hsat hT hW' htW (par q)
      (other_avoiding_pages hP hQ hg q hsub heo hcore hw hws)
  have hc : C.card ≤ X.card + N.card + K.card := by
    have he : extra.card ≤ K.attach.card := card_image_le
    rw [card_attach] at he
    exact (card_union_le (X ∪ N) extra).trans (Nat.add_le_add (card_union_le X N) he)
  have hw : X.card + 2*Q.card = 2*P.card := fixedSpokes_card hcol hP hQ
  have hn : N.card = P.card := hP.1.card_redEdges hcol
  have ht := hcov.number_le
  omega
end TuzaBound.Promotion


/-- Clearing denominators in the six covers, with weights 15, 6, 4, 8, 6, 3. -/
theorem tuza_six_cover_arithmetic {t n a b c h l k : ℕ}
    (h₁ : t + a ≤ 3*n)
    (h₂ : 2*t + 2*c ≤ 3*n + 5*a + 3*b + l)
    (h₃ : t + 2*c ≤ 3*n + h)
    (h₄ : t + c + k ≤ 3*n)
    (h₅ : 3*t + 3*b + 2*h ≤ 9*n + 8*c)
    (h₆ : 3*t + 3*b + 3*l ≤ 9*n + 6*c + 8*k) :
    14*t ≤ 39*n := by omega

/-- The four colored covers use weights 7, 8, 3, 6. -/
theorem tuza_four_cover_arithmetic {t p q u l k : ℕ}
    (h₁ : t + 2*q + u ≤ 3*p + l)
    (h₂ : t + q + k + u ≤ 3*p)
    (h₃ : 3*t + 3*l ≤ 6*p + 6*q + 8*k)
    (h₄ : 3*t + 2*l ≤ 6*p + 8*q) :
    8*t + 5*u ≤ 21*p := by omega

namespace TuzaBound
open Finset Promotion
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Four covers, first without a private-edge term. -/
theorem colored_rotation_bound (A R : Finset (Sym2 V)) :
    8 * transversalNumber (oneRedTriangles A R) ≤ 21 * packingNumber (oneRedTriangles A R) := by
  classical
  let F := oneRedTriangles A R
  let P := maximumPacking F
  have hP : IsMaximumPacking F P := maximumPacking_spec _
  let S := residual F (blueEdges R P)
  let Q := maximumPacking S
  have hQ : IsMaximumPacking S Q := maximumPacking_spec _
  let L := looseRed A R (fixedSpokes R P Q) (redEdges R P)
  have hs : Saturates A R F P.card := fun K hK hk =>
    (hK.maximum_of_card_eq (hk.trans hP.card_eq)).support_covers
      (fun _ h => (oneRedTriangles_colored A R).member_nonempty h)
  have hL : L ⊆ A := by
    intro x hx
    obtain ⟨T,hT,hxT⟩ := mem_support.mp (mem_redEdges.mp hx).1
    exact (mem_oneRedTriangles.mp (mem_residual.mp hT).1).2.1 hxT
  obtain ⟨k,r₂,r₃⟩ := rotated_covers hP hQ.1 hP.1.1
    (fun T h => (mem_residual.mp (hQ.1.1 h)).1) hL oneRedTriangles_subset
    (fun T ht => le_of_eq (mem_oneRedTriangles.mp ht).2.2) (Subset.refl F) hs
  have r₁ := distinct_colored_cover hP hQ.1
  have hJ : oneRedTriangles (A \ blueEdges R P) R = S := oneRedTriangles_sdiff _ _ _
  have hQ' : IsMaximumPacking (oneRedTriangles (A \ blueEdges R P) R) Q := hJ.symm ▸ hQ
  have hlocal := colored_bound hQ' (maximumPacking_spec _) (Subset.refl _)
  rw [hJ] at hlocal
  have hdel := transversalNumber_le_add_residual F (blueEdges R P)
    (fun _ h => (oneRedTriangles_colored A R).member_nonempty h)
  change _ ≤ _ + transversalNumber S at hdel
  rw [hP.1.card_blueEdges (oneRedTriangles_colored A R)] at hdel
  have r₄ : 3 * transversalNumber F + 2*(privateRedPages S R Q).card ≤
      6*P.card + 8*Q.card := by omega
  obtain ⟨g,hg⟩ := exists_pair_faces hP hQ.1
  obtain ⟨f,hf,hf'⟩ := loose_representatives hP hQ.1 hg
  let K := privateRedPages S R Q
  let j : {x // x ∈ L} → {T // T ∈ K} := fun e => ⟨(f e).val,(hf' e).2⟩
  have hj : Function.Injective j := fun a b h => hf (Subtype.ext (congrArg (fun t : {T // T ∈ K} => t.val) h))
  have hl : L.card ≤ K.card := by simpa using Fintype.card_le_of_injective j hj
  change 3 * transversalNumber F + 2*K.card ≤ 6*P.card + 8*Q.card at r₄
  change transversalNumber F + 2*Q.card + _ ≤ 3*P.card + L.card at r₁
  change 3*transversalNumber F + 3*L.card ≤ 6*P.card + 6*Q.card + 8*k at r₃
  change 8 * transversalNumber F ≤ 21 * P.card
  simpa using tuza_four_cover_arithmetic (u := 0) (q := Q.card) (l := L.card) (k := k)
    (t := transversalNumber F) (p := P.card) (by omega) (by omega) r₃ (by omega)

/-- Deleting the two blue edges of each private packed page costs 2 per
page, and lowers the packing number by at least the number of pages:
no surviving triangle can now use *any* of their edges. -/
theorem colored_private_rotation_bound {A R : Finset (Sym2 V)} {P : Finset (Finset (Sym2 V))}
    (hP : IsMaximumPacking (oneRedTriangles A R) P) :
    8 * transversalNumber (oneRedTriangles A R) +
      5 * (privateRedPages (oneRedTriangles A R) R P).card ≤ 21 * P.card := by
  classical
  let F := oneRedTriangles A R
  let K := privateRedPages F R P
  let W := blueEdges R K
  let J := oneRedTriangles (A \ W) R
  let D := maximumPacking J
  have hD : IsMaximumPacking J D := maximumPacking_spec _
  have hj : J = residual F W := oneRedTriangles_sdiff A R W
  have hDr : IsPacking (residual F W) D := hj ▸ hD.1
  let hF := oneRedTriangles_colored A R
  have hK := hP.1.subfamily (privateRedPages_subset F R P)
  have hd : Disjoint (support D) (support K) := by
    apply disjoint_left.mpr
    intro e he he'
    obtain ⟨T,hT,het⟩ := mem_support.mp he
    obtain ⟨U,hU,heu⟩ := mem_support.mp he'
    obtain ⟨ht,hdis⟩ := mem_residual.mp (hDr.1 hT)
    by_cases hr : e ∈ R
    · have heq := (mem_privateRedPages.mp hU).2 T ht
        ((hF.red_eq_singleton ht het hr).trans (hF.red_eq_singleton (hK.1 hU) heu hr).symm)
      obtain rfl := heq
      have hblue := hF.member_blue_card ht
      obtain ⟨x,hx⟩ := card_pos.mp (show 0 < (T \ R).card by omega)
      exact disjoint_left.mp hdis (mem_sdiff.mp hx).1 (mem_blueEdges.mpr
        ⟨mem_support.mpr ⟨_,hU,(mem_sdiff.mp hx).1⟩,(mem_sdiff.mp hx).2⟩)
    · exact disjoint_left.mp hdis het (mem_blueEdges.mpr ⟨he',hr⟩)
  have hcap := hP.2 (D ∪ K) ((hDr.mono_family (filter_subset _ _)).union hK hd)
  rw [card_union_of_disjoint (disjoint_of_support_disjoint
    (fun _ h => hF.member_nonempty (mem_residual.mp (hDr.1 h)).1) hd)] at hcap
  have hcost := transversalNumber_le_add_residual F W (fun _ ht => hF.member_nonempty ht)
  rw [← hj] at hcost
  have hsize : W.card = 2*K.card := hK.card_blueEdges hF
  have hb : 8*transversalNumber J ≤ 21*D.card := colored_rotation_bound (A \ W) R
  change 8*transversalNumber F + 5*K.card ≤ 21*P.card
  omega
end TuzaBound

section
open TuzaBound
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- For any maximum one-red triangle packing P, each packed red edge occurring
in just one member of the whole one-red family improves the numerator by five. -/
theorem colored_tuza_bound_21_8 (G : SimpleGraph V) (R : Finset (Sym2 V))
    (P : Finset (Finset (Sym2 V)))
    (hP : IsMaximumPacking (oneRedTriangles (graphEdges G) R) P) :
    8 * coloredTau G R + 5 * (privateRedPages (oneRedTriangles (graphEdges G) R) R P).card ≤
      21 * coloredNu G R := by
  simpa only [coloredTau,coloredNu,← hP.card_eq] using colored_private_rotation_bound hP

theorem colored_tuza_bound_21_8_plain (G : SimpleGraph V) (R : Finset (Sym2 V)) :
    8 * coloredTau G R ≤ 21 * coloredNu G R := colored_rotation_bound (graphEdges G) R
end

namespace TuzaBound.Construction
open Finset Promotion
variable {V : Type*} [Fintype V] [DecidableEq V] {A : Finset (Sym2 V)}

/-- Charge an opposite only to the private red pages of the special family. -/
theorem safe_row (c : Construction A) {Q : Finset (Finset (Sym2 V))}
    (hQ : IsPacking c.specialFamily Q) :
    transversalNumber (trianglesOn A) + 2*Q.card ≤ 3*c.initial.card +
      (privateRedPages c.specialFamily c.newEdges Q).card := by
  classical
  have h := safe_cover c.colored_parents (hQ.mono_family c.colored_children)
    c.parents_clear (hQ.1.trans c.special_clear) (Subset.refl _) c.clear_saturates
    (privateRedPages_subset c.specialFamily c.newEdges Q) (by
      intro q hq hn e he
      have hn' : ¬ (∀ W ∈ c.specialFamily, W ∩ c.newEdges = q ∩ c.newEdges → W = q) :=
        fun h => hn (mem_privateRedPages.mpr ⟨hq,h⟩)
      push Not at hn'
      obtain ⟨W,hw,heq,hne⟩ := hn'
      have hsp := (mem_oneRedTriangles.mp (hQ.1 hq)).2.1 (mem_inter.mp he).1
      have her : e ∈ c.newEdges := by
        rcases mem_union.mp hsp with h | h
        · exact h
        · exact ((mem_sdiff.mp (mem_inter.mp he).2).2 (mem_sdiff.mp (mem_sdiff.mp h).1).1).elim
      have heW : e ∈ W ∩ c.newEdges := heq.symm ▸ mem_inter.mpr ⟨(mem_inter.mp he).1,her⟩
      exact ⟨W,c.colored_children hw,c.special_clear hw,(mem_inter.mp heW).1,hne⟩)
  have hl := c.lift_clear
  omega
end TuzaBound.Construction

section
open TuzaBound
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- In every finite simple graph, fourteen times the minimum triangle edge
cover size is at most thirty-nine times the maximum edge-disjoint packing size. -/
theorem tuza_bound_39_14 (G : SimpleGraph V) : 14 * tuzaTau G ≤ 39 * tuzaNu G := by
  obtain ⟨c⟩ := exists_construction (graphEdges G)
  obtain ⟨Q,hQ⟩ := exists_maximumPacking c.specialFamily
  obtain ⟨k,r₄,r₆⟩ := c.rotation_rows hQ.1
  have h := tuza_six_cover_arithmetic
    (FirstCover.transversalNumber_add_typeOne_packing_le c.initial_maximum c.first_maximum.1)
    (c.uniform_cut hQ.1) (c.safe_row hQ.1) r₄ (c.private_residual_cover hQ) r₆
  rw [c.initial_maximum.card_eq] at h
  exact h

theorem tuza_bound_39_14_standard (G : SimpleGraph V) : 14 * tau G ≤ 39 * nu G :=
  tuza_bound_39_14 G
end
