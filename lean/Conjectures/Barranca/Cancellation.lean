import Conjectures.Barranca.Basic
import Mathlib.Tactic.Tauto

/-! Disjoint sums cancel for induced embeddings of finite graphs. -/
namespace Barranca

open SimpleGraph Matrix Polynomial Finset
open scoped Classical BigOperators
set_option linter.unusedSimpArgs false

noncomputable section

section Structure

variable {α β γ : Type} {F : SimpleGraph α} {A : SimpleGraph β} {B : SimpleGraph γ}

def pullEmbedding (f : F ↪g B) (g : A ↪g B)
    (h : ∀ x, ∃ y, g y = f x) : F ↪g A where
  toFun x := (h x).choose
  inj' := by
    intro x y he
    exact f.injective ((h x).choose_spec.symm.trans ((congrArg g he).trans (h y).choose_spec))
  map_rel_iff' := by
    intro x y
    change A.Adj (h x).choose (h y).choose ↔ _
    rw [← g.map_rel_iff, (h x).choose_spec, (h y).choose_spec, f.map_rel_iff]

theorem one_side (hc : F.Preconnected) (f : F ↪g A ⊕g B) :
    (∀ x, ∃ a, Sum.inl a = f x) ∨ (∀ x, ∃ b, Sum.inr b = f x) := by
  by_cases h : ∃ x a, Sum.inl a = f x
  · obtain ⟨x,a,hx⟩ := h
    left
    intro y
    cases hy : f y with
    | inl b => exact ⟨_, rfl⟩
    | inr b =>
      exfalso
      have hr : (A ⊕g B).Reachable (f x) (f y) := (hc x y).map f.toHom
      rw [← hx, hy] at hr
      exact SimpleGraph.not_reachable_sum_inl_inr a b hr
  · right
    intro x
    cases hx : f x with
    | inl a => exact (h ⟨x,a,hx.symm⟩).elim
    | inr b => exact ⟨_,rfl⟩

end Structure
/-- Disjoint cancellation for induced embeddings with a connected finite summand. -/
theorem cancel_connected (F G T : Graph) (hc : T.gr.Preconnected) :
    Has (F ⊞ T) (G ⊞ T) ↔ Has F G := by
  constructor
  · rintro ⟨f⟩
    let ft : T.gr ↪g G.gr ⊕g T.gr := f.comp SimpleGraph.Embedding.sumInr
    rcases one_side hc ft with leftSide|rightSide
    · let t : T.gr ↪g G.gr := pullEmbedding ft SimpleGraph.Embedding.sumInl leftSide
      have hit (v : T.V) : f (Sum.inr v) = Sum.inl (t v) := (leftSide v).choose_spec.symm
      let f' : F.V → G.V := fun x => Sum.elim id t (f (Sum.inl x))

      have ffr (u v : F.V ⊕ T.V) : (G.gr ⊕g T.gr).Adj (f u) (f v) ↔ (F.gr ⊕g T.gr).Adj u v :=
        f.map_rel_iff
      refine ⟨{ toFun := f', inj' := ?_, map_rel_iff' := ?_ }⟩
      · intro x y he
        change Sum.elim id t (f (.inl x)) = Sum.elim id t (f (.inl y)) at he
        cases hx : f (.inl x) with
        | inl a =>
          cases hy : f (.inl y) with
          | inl b =>
            have h : a=b := by simpa [hx,hy] using he
            exact Sum.inl.inj (f.injective (hx.trans ((congrArg Sum.inl h).trans hy.symm)))
          | inr b =>
            have h : a=t b := by simpa [hx,hy] using he
            exact (Sum.inl_ne_inr (f.injective (hx.trans ((congrArg Sum.inl h).trans (hit b).symm)))).elim
        | inr a =>
          cases hy : f (.inl y) with
          | inl b =>
            have h : t a=b := by simpa [hx,hy] using he
            exact (Sum.inr_ne_inl (f.injective ((hit a).trans ((congrArg Sum.inl h).trans hy.symm)))).elim
          | inr b =>
            have h : a=b := t.injective (by simpa [hx,hy] using he)
            exact Sum.inl.inj (f.injective (hx.trans ((congrArg Sum.inr h).trans hy.symm)))
      · intro x y
        change G.gr.Adj (Sum.elim id t (f (.inl x))) (Sum.elim id t (f (.inl y))) ↔ _
        have hxy := ffr (.inl x) (.inl y)
        cases hx : f (.inl x) with
        | inl a =>
          cases hy : f (.inl y) with
          | inl b => simpa [hx,hy] using hxy
          | inr b =>
            have hz := ffr (.inl x) (.inr b)
            simp [hx,hy,hit] at hz hxy ⊢
            tauto
        | inr a =>
          cases hy : f (.inl y) with
          | inl b =>
            have hz := ffr (.inr a) (.inl y)
            simp [hx,hy,hit] at hz hxy ⊢
            tauto
          | inr b => simpa [hx,hy,t.map_rel_iff] using hxy
    · let t : T.gr ↪g T.gr := pullEmbedding ft SimpleGraph.Embedding.sumInr rightSide
      have ht := Finite.surjective_of_injective t.injective
      let fl : F.gr ↪g G.gr ⊕g T.gr := f.comp SimpleGraph.Embedding.sumInl
      refine ⟨pullEmbedding fl SimpleGraph.Embedding.sumInl (fun x => ?_)⟩
      cases hx : fl x with
      | inl a => exact ⟨_,rfl⟩
      | inr b =>
        obtain ⟨v,hv⟩ := ht b
        have hh : f (Sum.inr v) = Sum.inr (t v) := (rightSide v).choose_spec.symm
        have hx' : f (Sum.inl x) = Sum.inr b := hx
        rw [hv] at hh
        exact (Sum.inl_ne_inr (f.injective (hx'.trans hh.symm))).elim
  · rintro ⟨f⟩
    exact ⟨SimpleGraph.Embedding.sum f SimpleGraph.Embedding.refl⟩

/-- Split off the vertices reachable from one endpoint of an unreachable pair. -/
theorem split_graph (G : Graph) (h : ¬ G.gr.Preconnected) :
    ∃ A B : Graph, Fintype.card A.V < Fintype.card G.V ∧
      Fintype.card B.V < Fintype.card G.V ∧ Nonempty ((A ⊞ B).gr ≃g G.gr) := by
  change ¬ ∀ x y, G.gr.Reachable x y at h
  push Not at h
  obtain ⟨x,y,hxy⟩ := h
  let s : Set G.V := G.gr.Reachable x
  let A := pack s (G.gr.induce s)
  let B := pack (sᶜ : Set G.V) (G.gr.induce (sᶜ : Set G.V))
  have hn : Nonempty s := ⟨x,SimpleGraph.Reachable.refl x⟩
  have hm : Nonempty (sᶜ : Set G.V) := ⟨y,hxy⟩
  let i : (G.gr.induce s ⊕g G.gr.induce (sᶜ : Set G.V)) ≃g G.gr := {
    toEquiv := Equiv.Set.sumCompl s
    map_rel_iff' := by
      rintro (u|u) (v|v)
      · rfl
      · simp only [SimpleGraph.sum_adj, Bool.false_eq_true, iff_false]
        exact (fun ha => v.property (u.property.trans ha.reachable))
      · simp only [SimpleGraph.sum_adj, Bool.false_eq_true, iff_false]
        exact (fun ha => u.property (v.property.trans ha.symm.reachable))
      · rfl }
  have he := Fintype.card_congr i.toEquiv
  change Fintype.card (A.V ⊕ B.V) = Fintype.card G.V at he
  rw [Fintype.card_sum] at he
  have h1 : 0 < Fintype.card A.V := Fintype.card_pos_iff.mpr hn
  have h2 : 0 < Fintype.card B.V := Fintype.card_pos_iff.mpr hm
  exact ⟨A,B,by omega,by omega,⟨i⟩⟩

theorem graph_induction (P : Graph → Prop)
    (one : ∀ G, G.gr.Preconnected → P G)
    (step : ∀ A B, P A → P B → P (A ⊞ B))
    (iso : ∀ {A B : Graph}, A.gr ≃g B.gr → P A → P B) (G : Graph) : P G := by
  by_cases h : G.gr.Preconnected
  · exact one G h
  · obtain ⟨A,B,ha,hb,⟨i⟩⟩ := split_graph G h
    apply iso i (step A B ?_ ?_)
    · exact graph_induction P one step iso A
    · exact graph_induction P one step iso B
termination_by Fintype.card G.V

theorem disjoint_cancellation (T F G : Graph) : Has (F ⊞ T) (G ⊞ T) ↔ Has F G := by
  revert F G
  apply graph_induction (fun T => ∀ F G, Has (F ⊞ T) (G ⊞ T) ↔ Has F G)
  · intro T hc F G
    exact cancel_connected F G T hc
  · intro A B hA hB F G
    exact (has_congr SimpleGraph.Iso.sumAssoc.symm SimpleGraph.Iso.sumAssoc.symm).trans
      ((hB (F ⊞ A) (G ⊞ A)).trans (hA F G))
  · intro A B e hA F G
    exact (has_congr (SimpleGraph.Iso.sumCongr (SimpleGraph.Iso.refl : F.gr ≃g F.gr) e.symm)
      (SimpleGraph.Iso.sumCongr (SimpleGraph.Iso.refl : G.gr ≃g G.gr) e.symm)).trans (hA F G)

theorem summand_rs (F T : Graph) (hr : RS (F ⊞ T)) : RS F := by
  intro A B h
  have hcp : cp (A ⊞ T) = cp (B ⊞ T) := by simp [cp_plus,h]
  exact (disjoint_cancellation T F A).symm.trans ((hr _ _ hcp).trans (disjoint_cancellation T F B))


end
end Barranca
