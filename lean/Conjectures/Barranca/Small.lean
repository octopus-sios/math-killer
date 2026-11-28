import Conjectures.Barranca.Basic
import Mathlib.Tactic.FinCases

/-! Coordinate descriptions of the five small induced embeddings. -/
namespace Barranca
open SimpleGraph Matrix
open scoped Classical
noncomputable section
set_option linter.unusedSimpArgs false

private def mkEmb {α β : Type} {H : SimpleGraph α} {G : SimpleGraph β}
    (f : α → β) (hi : Function.Injective f) (ha : ∀ i j, G.Adj (f i) (f j) ↔ H.Adj i j) :
    H ↪g G where
  toFun := f
  inj' := hi
  map_rel_iff' := ha _ _


theorem has_one (G : Graph) : Has (clq 1) G ↔ Nonempty G.V := by
  change Nonempty ((completeGraph (Fin 1)) ↪g G.gr) ↔ _
  constructor
  · rintro ⟨f⟩; exact ⟨f 0⟩
  · rintro ⟨v⟩
    refine ⟨{ toFun := fun _ => v, inj' := fun _ _ _ => Subsingleton.elim _ _, map_rel_iff' := ?_ }⟩
    intro x y
    have : x = y := Subsingleton.elim _ _
    subst y; simp

theorem has_edge (G : Graph) : Has (clq 2) G ↔ ∃ x y, G.gr.Adj x y := by
  change Nonempty ((completeGraph (Fin 2)) ↪g G.gr) ↔ _
  constructor
  · rintro ⟨f⟩
    exact ⟨_, _, f.map_rel_iff.mpr (by decide : (0 : Fin 2) ≠ 1)⟩
  · rintro ⟨x,y,h⟩
    refine ⟨mkEmb ((![x,y] : Fin 2 → G.V)) ?_ ?_⟩
    · intro i j; fin_cases i <;> fin_cases j <;> simp [h.ne, h.ne.symm]
    · intro i j; fin_cases i <;> fin_cases j <;> simp [clq,pack,h,h.symm]

theorem has_independent_pair (G : Graph) :
    Has (clq 1 ⊞ clq 1) G ↔ ∃ x y, x ≠ y ∧ ¬ G.gr.Adj x y := by
  change Nonempty ((completeGraph (Fin 1) ⊕g completeGraph (Fin 1)) ↪g G.gr) ↔ _
  constructor
  · rintro ⟨f⟩
    refine ⟨f (.inl 0), f (.inr 0), f.injective.ne Sum.inl_ne_inr, ?_⟩
    intro h
    have := f.map_rel_iff.mp h
    exact Bool.noConfusion this
  · rintro ⟨x,y,ne,ha⟩
    refine ⟨mkEmb (Sum.elim (fun _ => x) (fun _ => y)) ?_ ?_⟩
    · rintro (i|i) (j|j) h <;> simp_all [Subsingleton.elim i j, ne.symm]
    · have hb : ¬ G.gr.Adj y x := fun a => ha a.symm
      rintro (i|i) (j|j) <;> simp [plus,clq,pack,ha,hb,
        Subsingleton.elim i j]

theorem has_triangle (G : Graph) :
    Has (clq 3) G ↔ ∃ x y z, G.gr.Adj x y ∧ G.gr.Adj y z ∧ G.gr.Adj z x := by
  change Nonempty ((completeGraph (Fin 3)) ↪g G.gr) ↔ _
  constructor
  · rintro ⟨f⟩
    exact ⟨f 0, f 1, f 2, f.map_rel_iff.mpr (by decide : (0 : Fin 3) ≠ 1),
      f.map_rel_iff.mpr (by decide : (1 : Fin 3) ≠ 2), f.map_rel_iff.mpr (by decide : (2 : Fin 3) ≠ 0)⟩
  · rintro ⟨x,y,z,h,k,l⟩
    refine ⟨mkEmb ((![x,y,z] : Fin 3 → G.V)) ?_ ?_⟩
    · intro i j; fin_cases i <;> fin_cases j <;> simp [h.ne,k.ne,l.ne,h.ne.symm,k.ne.symm,l.ne.symm]
    · intro i j; fin_cases i <;> fin_cases j <;> simp [clq,pack,h,k,l,h.symm,k.symm,l.symm]

theorem has_path (G : Graph) :
    Has (bic 1 2) G ↔ ∃ x y z, G.gr.Adj x y ∧ G.gr.Adj y z ∧ x ≠ z ∧ ¬ G.gr.Adj x z := by
  change Nonempty ((completeBipartiteGraph (Fin 1) (Fin 2)) ↪g G.gr) ↔ _
  constructor
  · rintro ⟨f⟩
    refine ⟨f (.inr 0), f (.inl 0), f (.inr 1), f.map_rel_iff.mpr ?_, f.map_rel_iff.mpr ?_, f.injective.ne ?_, ?_⟩
    · simp [bic, pack, completeBipartiteGraph]
    · simp [bic, pack, completeBipartiteGraph]
    · exact fun h => (by decide : (0:Fin 2) ≠ 1) (Sum.inr.inj h)
    · intro h
      have := f.map_rel_iff.mp h
      simpa [bic,pack,completeBipartiteGraph] using this
  · rintro ⟨x,y,z,h,k,ne,hn⟩
    let f : Fin 1 ⊕ Fin 2 → G.V := Sum.elim (fun _ => y) ![x,z]
    refine ⟨mkEmb (f) ?_ ?_⟩
    · rintro (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;>
        simp [f,h.ne,h.ne.symm,k.ne,k.ne.symm,ne,ne.symm]
    · have hz : ¬ G.gr.Adj z x := fun a => hn a.symm
      rintro (i|i) (j|j) <;> fin_cases i <;> fin_cases j <;>
        simp [bic,pack,completeBipartiteGraph,f,h,h.symm,k,k.symm,hn,hz]
end
end Barranca
