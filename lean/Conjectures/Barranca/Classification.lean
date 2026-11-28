import Conjectures.Barranca.Connected
import Conjectures.Barranca.Seeds

/-! Assembly of the necessary condition up to graph isomorphism. -/
namespace Barranca

open SimpleGraph Matrix Polynomial Finset
open scoped Classical BigOperators
set_option linter.unusedSimpArgs false

noncomputable section

inductive Tag | null | pt | independentPair | edge | triangle | path

def model : Tag → Graph
  | .null => clq 0
  | .pt => clq 1
  | .independentPair => clq 1 ⊞ clq 1
  | .edge => clq 2
  | .triangle => clq 3
  | .path => bic 1 2

def Listed (H : Graph) := ∃ t, Nonempty (H.gr ≃g (model t).gr)

def completeIso (H : Graph) (h : ∀ x y, x ≠ y → H.gr.Adj x y) :
    H.gr ≃g (clq (Fintype.card H.V)).gr where
  toEquiv := Fintype.equivFin _
  map_rel_iff' := by
    intro x y
    change Fintype.equivFin H.V x ≠ Fintype.equivFin H.V y ↔ H.gr.Adj x y
    rw [(Fintype.equivFin H.V).injective.ne_iff]
    exact ⟨h x y, SimpleGraph.Adj.ne⟩

theorem list_clique (n : ℕ) (h : RS (clq n)) : Listed (clq n) := by
  obtain hn|hn := le_or_gt n 3
  · interval_cases n
    · exact ⟨.null,⟨SimpleGraph.Iso.refl⟩⟩
    · exact ⟨.pt,⟨SimpleGraph.Iso.refl⟩⟩
    · exact ⟨.edge,⟨SimpleGraph.Iso.refl⟩⟩
    · exact ⟨.triangle,⟨SimpleGraph.Iso.refl⟩⟩
  · exact (large_clique_not_rs (n-4) (by simpa [Nat.sub_add_cancel (by omega : 4≤n)] using h)).elim

theorem listed_via {G H : Graph} (e : G.gr ≃g H.gr) (h : Listed H) : Listed G := by
  obtain ⟨t,⟨i⟩⟩ := h
  exact ⟨t,⟨e.trans i⟩⟩

def starIso (H : Graph) (c : H.V) (hh : H.gr = starGraph c) :
    (bic 1 (Fintype.card {x : H.V // x ≠ c})).gr ≃g H.gr := by
  let e := (Fintype.equivFin {x : H.V // x ≠ c}).symm
  let v : Fin 1 ⊕ Fin (Fintype.card {x : H.V // x ≠ c}) → H.V :=
    Sum.elim (fun _ => c) (fun x => (e x).1)
  have hv : Function.Bijective v := by
    constructor
    · rintro (a|a) (b|b) h
      · exact congrArg Sum.inl (Subsingleton.elim _ _)
      · exact ((e b).property h.symm).elim
      · exact ((e a).property h).elim
      · exact congrArg Sum.inr (e.injective (Subtype.ext h))
    · intro x
      by_cases hx : x=c
      · exact ⟨.inl 0,hx.symm⟩
      · exact ⟨.inr (e.symm ⟨x,hx⟩),by simp [v]⟩
  refine ⟨Equiv.ofBijective v hv,?_⟩
  intro a b
  change H.gr.Adj (v a) (v b) ↔ (completeBipartiteGraph _ _).Adj a b
  cases a <;> cases b <;>
    simp [v, hh, bic,pack, completeBipartiteGraph, starGraph_adj, (e _).property,
      Ne.symm (e _).property]

theorem list_bic (m : ℕ) (h : RS (bic 1 m)) : Listed (bic 1 m) := by
  by_cases hm : 3≤m
  · exact (large_star_not_rs m hm h).elim
  have hle : m≤2 := by omega
  interval_cases m
  · have i := completeIso (bic 1 0) (by
      change ∀ x y : Fin 1 ⊕ Fin 0, x ≠ y → (completeBipartiteGraph _ _).Adj x y
      rintro (x|x) (y|y) <;> fin_cases x <;> fin_cases y <;> simp [completeBipartiteGraph])
    exact listed_via i (list_clique _ ((rs_congr i).mp h))
  · have i := completeIso (bic 1 1) (by
      change ∀ x y : Fin 1 ⊕ Fin 1, x ≠ y → (completeBipartiteGraph _ _).Adj x y
      rintro (x|x) (y|y) <;> fin_cases x <;> fin_cases y <;> simp [completeBipartiteGraph])
    exact listed_via i (list_clique _ ((rs_congr i).mp h))
  · exact ⟨.path,⟨SimpleGraph.Iso.refl⟩⟩

theorem list_preconnected (H : Graph) (hc : H.gr.Preconnected) (hr : RS H) : Listed H := by
  obtain ⟨B,hB,h⟩ := rs_embeds_in_pieces H hr
  obtain ⟨n,hn⟩ := connected_in_pieces H B hc hB h
  rcases hn with hcl | hbi
  · obtain ⟨f⟩ := hcl
    let i := completeIso H (fun x y hn => f.map_rel_iff.mp (f.injective.ne hn))
    exact listed_via i (list_clique _ ((rs_congr i).mp hr))
  · change Nonempty (H.gr ↪g completeBipartiteGraph (Fin 1) (Fin n)) at hbi
    obtain ⟨f⟩ := hbi
    by_cases hcenter : ∃ c z, f c = Sum.inl z
    · obtain ⟨c,u,hu⟩ := hcenter
      have left (x) : (f x).isLeft = true ↔ x=c := by
        constructor
        · intro hl
          cases hx : f x with
          | inl a => exact f.injective (hx.trans ((congrArg Sum.inl (Subsingleton.elim a u)).trans hu.symm))
          | inr b => simp [hx] at hl
        · rintro rfl; simp [hu]
      have right (x) : (f x).isRight = true ↔ x ≠ c := by
        have := left x
        cases hx : f x <;> simp_all
      have hh : H.gr = starGraph c := by
        ext x y
        have hh' : (completeBipartiteGraph _ _).Adj (f x) (f y) ↔ H.gr.Adj x y := f.map_rel_iff
        change ((f x).isLeft = true ∧ (f y).isRight = true ∨
          (f x).isRight = true ∧ (f y).isLeft = true) ↔ H.gr.Adj x y at hh'
        simp only [left, right] at hh'
        rw [← hh',starGraph_adj]
        grind
      let i := starIso H c hh
      exact listed_via i.symm (list_bic _ ((rs_congr i).mpr hr))
    · have he (x y : H.V) : ¬ H.gr.Adj x y := by
        intro a
        have ha := f.map_rel_iff.mpr a
        cases hx : f x with
        | inl u => exact hcenter ⟨_,_,hx⟩
        | inr u =>
          cases hy : f y with
          | inl v => exact hcenter ⟨_,_,hy⟩
          | inr v => rw [hx,hy] at ha; simp [completeBipartiteGraph] at ha
      have ss (x y : H.V) : x=y := by
        obtain ⟨w⟩ := hc x y
        cases w with
        | nil => rfl
        | cons h _ => exact (he _ _ h).elim
      let i := completeIso H (fun x y hn => (hn (ss x y)).elim)
      exact listed_via i (list_clique _ ((rs_congr i).mp hr))

def dropNull (H : Graph) : ((clq 0) ⊞ H).gr ≃g H.gr where
  toFun := Sum.elim Fin.elim0 id
  invFun := Sum.inr
  left_inv := by rintro (a|a); exact a.elim0; rfl
  right_inv := fun _ => rfl
  map_rel_iff' := by rintro (a|a) (b|b) <;> first | exact a.elim0 | exact b.elim0 | rfl

theorem summed_models (t u : Tag) (hr : RS (model t ⊞ model u)) : Listed (model t ⊞ model u) := by
  let I := clq 1
  have flip {A B : Graph} (h : RS (A ⊞ B)) : RS (B ⊞ A) :=
    (rs_congr SimpleGraph.Iso.sumComm).mp h
  have trim (X : Graph) (h : RS ((I ⊞ I) ⊞ X)) : RS (I ⊞ X) :=
    summand_rs (I ⊞ X) I (flip ((rs_congr SimpleGraph.Iso.sumAssoc).mp h))
  cases t <;> cases u
  · exact ⟨.null,⟨dropNull _⟩⟩
  · exact ⟨.pt,⟨dropNull _⟩⟩
  · exact ⟨.independentPair,⟨dropNull _⟩⟩
  · exact ⟨.edge,⟨dropNull _⟩⟩
  · exact ⟨.triangle,⟨dropNull _⟩⟩
  · exact ⟨.path,⟨dropNull _⟩⟩
  · exact ⟨.pt,⟨SimpleGraph.Iso.sumComm.trans (dropNull _)⟩⟩
  · exact ⟨.independentPair,⟨SimpleGraph.Iso.refl⟩⟩
  · exact (seed_iii (flip hr)).elim
  · exact (seed_ei (flip hr)).elim
  · exact (seed_it hr).elim
  · exact (seed_ip hr).elim
  · exact ⟨.independentPair,⟨SimpleGraph.Iso.sumComm.trans (dropNull _)⟩⟩
  · exact (seed_iii hr).elim
  · exact (seed_iii (flip (trim _ hr))).elim
  · exact (seed_ei (flip (trim _ hr))).elim
  · exact (seed_it (trim _ hr)).elim
  · exact (seed_ip (trim _ hr)).elim
  · exact ⟨.edge,⟨SimpleGraph.Iso.sumComm.trans (dropNull _)⟩⟩
  · exact (seed_ei hr).elim
  · exact (seed_ei (flip (trim _ (flip hr)))).elim
  · exact (seed_ee hr).elim
  · exact (seed_et hr).elim
  · exact (seed_ep hr).elim
  · exact ⟨.triangle,⟨SimpleGraph.Iso.sumComm.trans (dropNull _)⟩⟩
  · exact (seed_it (flip hr)).elim
  · exact (seed_it (trim _ (flip hr))).elim
  · exact (seed_et (flip hr)).elim
  · exact (seed_tt hr).elim
  · exact (seed_pt (flip hr)).elim
  · exact ⟨.path,⟨SimpleGraph.Iso.sumComm.trans (dropNull _)⟩⟩
  · exact (seed_ip (flip hr)).elim
  · exact (seed_ip (trim _ (flip hr))).elim
  · exact (seed_ep (flip hr)).elim
  · exact (seed_pt hr).elim
  · exact (seed_pp hr).elim

/-- Necessity in Barranca's classification, including the harmless null pattern. -/
theorem only_listed (H : Graph) : RS H → Listed H := by
  apply graph_induction (fun G => RS G → Listed G)
  · exact list_preconnected
  · intro A B hA hB hr
    obtain ⟨t,⟨a⟩⟩ := hA (summand_rs A B hr)
    obtain ⟨u,⟨b⟩⟩ := hB (summand_rs B A ((rs_congr SimpleGraph.Iso.sumComm).mp hr))
    let i : (A ⊞ B).gr ≃g (model t ⊞ model u).gr := SimpleGraph.Iso.sumCongr a b
    exact listed_via i (summed_models t u ((rs_congr i).mp hr))
  · intro A B i hA hB
    exact listed_via i.symm (hA ((rs_congr i).mpr hB))

end
end Barranca
