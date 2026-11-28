import Conjectures.Barranca.Trade
import Conjectures.Barranca.Cancellation
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Tactic.IntervalCases

/-! Connected patterns and explicit witnesses for large cliques and stars. -/
namespace Barranca

open SimpleGraph Matrix Polynomial Finset
open scoped Classical BigOperators
set_option linter.unusedSimpArgs false

noncomputable section

def leaves (n : ℕ) : (zeroG n).gr ↪g (bic 1 n).gr where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := by intro i j; change (completeBipartiteGraph (Fin 1) (Fin n)).Adj (.inr i) (.inr j) ↔ False; exact ⟨fun h => (h.elim (fun a => Bool.noConfusion a.1) (fun a => Bool.noConfusion a.2)), False.elim⟩

theorem connected_in_pieces (H B : Graph) (hc : H.gr.Preconnected) (hB : Pieces B) :
    Has H B → ∃ n, Has H (clq n) ∨ Has H (bic 1 n) := by
  induction hB with
  | isolated n => rintro ⟨f⟩; exact ⟨n,Or.inr ⟨(leaves n).comp f⟩⟩
  | clique n => intro h; exact ⟨n,Or.inl h⟩
  | star n => intro h; exact ⟨n,Or.inr h⟩
  | @sum A B _ _ ih jh =>
    rintro ⟨f⟩
    rcases one_side hc (A := A.gr) (B := B.gr) f with hl|hr
    · exact ih ⟨pullEmbedding f SimpleGraph.Embedding.sumInl hl⟩
    · exact jh ⟨pullEmbedding f SimpleGraph.Embedding.sumInr hr⟩

theorem connected_rs_atom (H : Graph) (hc : H.gr.Connected) (hr : RS H) :
    ∃ n, Has H (clq n) ∨ Has H (bic 1 n) := by
  obtain ⟨B,hB,h⟩ := rs_embeds_in_pieces H hr
  exact connected_in_pieces H B hc.preconnected hB h

def bookPart (t : ℕ) : Fin 2 ⊕ Fin t → Fin 3 := Sum.elim Fin.castSucc (fun _ => 2)

def book (t : ℕ) : Graph := pack _ ((completeGraph (Fin 3)).comap (bookPart t))

theorem cp_book (t : ℕ) (ht : 0 < t) :
    cp (book t) = X^(t-1) * ((X+1)*(X^2-X-2*C (t:ℤ))) := by
  let c := bookPart t
  let U : Matrix (Fin 2 ⊕ Fin t) (Fin 3) ℤ := fun x j => if c x = j then 1 else 0
  let V : Matrix (Fin 3) (Fin 2 ⊕ Fin t) ℤ := fun j x => if c x = j then 0 else 1
  have hUV : ((completeGraph (Fin 3)).comap (bookPart t)).adjMatrix ℤ = U*V := by
    ext x y
    rw [Matrix.mul_apply, Finset.sum_eq_single (c x)]
    · by_cases e : c x = c y <;> simp_all [SimpleGraph.adjMatrix_apply, SimpleGraph.comap, c, U,V, eq_comm]
    · intro b _ hb; simp [U, Ne.symm hb]
    · simp
  have hVU : V*U = !![0,1,(t:ℤ);1,0,(t:ℤ);1,1,0] := by
    ext i j; rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;>
      simp [U,V,c,bookPart,Fintype.sum_sum_type,Fin.sum_univ_two]
  unfold book
  rw [cp_pack,hUV,Matrix.charpoly_mul_comm_of_le, hVU]
  · simp only [Fintype.card_sum,Fintype.card_fin]
    rw [show 2+t-3 = t-1 by omega]
    congr 1
    simp [Matrix.charpoly,Matrix.charmatrix,Matrix.det_fin_three,Matrix.one_apply]
    ring
  · simp; omega

theorem cp_clique_witness (k : ℕ) :
    let d := k+3
    let t := d*(d-1)/2
    cp ((clq (d+1) ⊞ bic (d-1) (d-1)) ⊞ zeroG (t-1)) =
      cp ((clq d ⊞ book t) ⊞ zeroG ((d-1)+(d-1)-2)) := by
  intro d t
  have hd : 0 < d-1 := by dsimp [d]; omega
  have ht0 : 2 ∣ d*(d-1) := by
    rw [Nat.dvd_iff_mod_eq_zero,Nat.mul_mod]
    have : d%2 = 0 ∨ (d-1)%2 = 0 := by omega
    rcases this with h|h <;> simp [h]
  have ht : 0 < t := by
    have h3 : 3 ≤ d := by dsimp [d]; omega
    have h2 : 2 ≤ d-1 := by omega
    dsimp [t]
    have := Nat.mul_le_mul h3 h2
    omega
  have ht2 : t*2 = d*(d-1) := Nat.div_mul_cancel ht0
  have hc : (2:ℤ)*(t:ℤ) = (d:ℤ)*((d:ℤ)-1) := by
    have := congrArg (fun z : ℕ => (z:ℤ)) ht2
    push_cast [Nat.one_le_iff_ne_zero.mpr (by omega : d ≠ 0)] at this
    linarith
  simp only [cp_plus, cp_zeroG,cp_clq,cp_bic _ _ hd hd,cp_book t ht]
  conv_rhs => rw [show clq d = clq ((d-1)+1) by congr 1 <;> omega, cp_clq]
  rw [show (X+1 : ℤ[X])^d = (X+1)^(d-1) * (X+1) by
    conv_lhs => rw [show d = (d-1)+1 by omega, pow_succ]]
  have hh : (2:ℤ[X])*C (t:ℤ) = C (d:ℤ)*(C (d:ℤ)-1) := by
    simpa using congrArg (C : ℤ → ℤ[X]) hc
  push_cast [Nat.one_le_iff_ne_zero.mpr (by omega : d ≠ 0)]
  rw [hh]
  simp only [map_mul, map_sub, map_one, map_pow]
  ring

def bicEmb {a b c d : ℕ} (f : Fin a ↪ Fin c) (g : Fin b ↪ Fin d) :
    (bic a b).gr ↪g (bic c d).gr where
  toFun := Sum.map f g
  inj' := (f.sumMap g).injective
  map_rel_iff' := by rintro (x|x) (y|y) <;> rfl

theorem star_pre (m : ℕ) : (bic 1 m).gr.Preconnected := by
  have h (x : (bic 1 m).V) : (bic 1 m).gr.Reachable (.inl 0) x := by
    rcases x with a|b
    · have : a=0 := Subsingleton.elim _ _; subst a
      exact SimpleGraph.Reachable.refl _
    · apply SimpleGraph.Adj.reachable
      simp [bic,pack,completeBipartiteGraph]
  intro x y; exact (h x).symm.trans (h y)

theorem star_into_bic {m a b : ℕ} (f : (bic 1 m).gr ↪g (bic a b).gr) :
    m ≤ a ∨ m ≤ b := by
  have h (u : Fin m) : (bic a b).gr.Adj (f (Sum.inl 0)) (f (Sum.inr u)) :=
    f.map_rel_iff.mpr (by simp [bic,pack,completeBipartiteGraph])
  cases hx : f (Sum.inl 0) with
  | inl i =>
    right
    have br (u : Fin m) : ∃ j, f (Sum.inr u) = Sum.inr j := by
      cases hy : f (Sum.inr u) with
      | inr j => exact ⟨_,rfl⟩
      | inl j => have := h u; rw [hx,hy] at this; simp [bic,pack,completeBipartiteGraph] at this
    have hi : Function.Injective (fun u => (br u).choose) := by
      intro u v he
      have hh := f.injective ((br u).choose_spec.trans ((congrArg Sum.inr he).trans (br v).choose_spec.symm))
      exact Sum.inr.inj hh
    simpa using Fintype.card_le_of_injective _ hi
  | inr j =>
    left
    have bl (u : Fin m) : ∃ i, f (Sum.inr u) = Sum.inl i := by
      cases hy : f (Sum.inr u) with
      | inl i => exact ⟨_,rfl⟩
      | inr i => have := h u; rw [hx,hy] at this; simp [bic,pack,completeBipartiteGraph] at this
    have hi : Function.Injective (fun u => (bl u).choose) := by
      intro u v he
      exact Sum.inr.inj (f.injective ((bl u).choose_spec.trans ((congrArg Sum.inl he).trans (bl v).choose_spec.symm)))
    simpa using Fintype.card_le_of_injective _ hi

theorem large_star_not_rs (m : ℕ) (hm : 3 ≤ m) : ¬ RS (bic 1 m) := by
  let a := m-1
  have ha : 0<a := by dsimp [a]; omega
  let A := bic 1 (2*a) ⊞ zeroG (2+a-2)
  let B := bic 2 a ⊞ zeroG (1+2*a-2)
  have hcp : cp A = cp B := by
    simp only [A,B,cp_plus, cp_zeroG, cp_bic 1 _ (by decide) (by positivity : 0<2*a),
      cp_bic 2 _ (by decide) ha]
    push_cast
    ring
  intro hr
  have g := bicEmb (Function.Embedding.refl (Fin 1)) (Fin.castLEEmb (show m ≤ 2*a by dsimp [a]; omega))
  have good : Has (bic 1 m) A := ⟨(SimpleGraph.Embedding.sumInl).comp g⟩
  obtain ⟨f⟩ := (hr _ _ hcp).mp good
  rcases one_side (star_pre m) (A := (bic 2 a).gr) (B := (zeroG _).gr) f with hl|hz
  · have hh := star_into_bic (pullEmbedding f SimpleGraph.Embedding.sumInl hl)
    dsimp [a] at hh; omega
  · let z := pullEmbedding f SimpleGraph.Embedding.sumInr hz
    have h : (bic 1 m).gr.Adj (Sum.inl 0) (Sum.inr ⟨0,by omega⟩) := by simp [bic,pack,completeBipartiteGraph]
    exact z.map_rel_iff.mpr h

theorem clique_color_bound {n k : ℕ} {H : Graph}
    (h : Has (clq n) H) (color : H.gr →g completeGraph (Fin k)) : n ≤ k := by
  obtain ⟨f⟩ := h
  let c := color.comp f.toHom
  have hc : Function.Injective c := by
    intro x y he; by_contra hn
    have had : (clq n).gr.Adj x y := hn
    exact (c.map_rel had).ne he
  let fn : Fin n → Fin k := c
  have hc' : Function.Injective fn := hc
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective fn hc'

def paintSum {F G : Graph} {β : Type} {T : SimpleGraph β} (f : F.gr →g T) (g : G.gr →g T) :
    (F ⊞ G).gr →g T where
  toFun := Sum.elim f g
  map_rel' := by
    rintro (x|x) (y|y) h
    · exact f.map_rel h
    · exact Bool.noConfusion h
    · exact Bool.noConfusion h
    · exact g.map_rel h

theorem large_clique_not_rs (k : ℕ) : ¬ RS (clq (k+4)) := by
  let d := k+3
  let t := d*(d-1)/2
  let A := (clq (d+1) ⊞ bic (d-1) (d-1)) ⊞ zeroG (t-1)
  let B := (clq d ⊞ book t) ⊞ zeroG ((d-1)+(d-1)-2)
  have hcp : cp A = cp B := cp_clique_witness k
  have color1 : (book t).gr →g completeGraph (Fin d) := {
    toFun := fun x => Fin.castLE (show 3 ≤ d by dsimp [d]; omega) (bookPart t x)
    map_rel' := by
      intro x y h
      change bookPart t x ≠ bookPart t y at h
      exact fun e => h (Fin.ext (congrArg (Fin.val : Fin d → ℕ) e)) }
  let colZ : (zeroG ((d-1)+(d-1)-2)).gr →g completeGraph (Fin d) :=
    ⟨fun _ => ⟨0, by dsimp [d]; omega⟩, fun h => h.elim⟩
  let c : B.gr →g completeGraph (Fin d) :=
    paintSum (paintSum (SimpleGraph.Hom.id : (clq d).gr →g (clq d).gr) color1) colZ
  intro h
  have hp : Has (clq (k+4)) A := ⟨SimpleGraph.Embedding.sumInl.comp SimpleGraph.Embedding.sumInl⟩
  have hh := clique_color_bound ((h _ _ hcp).mp hp) c
  dsimp [d] at hh; omega


end
end Barranca
