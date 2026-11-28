import Conjectures.Barranca.Spectrum
import Conjectures.Barranca.Small
import Mathlib.Algebra.Order.Star.Real

/-! Recognition of all five patterns. The quantities in the first four tests
are invariant under relabeling and make sense for empty hosts as well. -/
namespace Barranca
open Matrix Finset SimpleGraph
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSimpArgs false

private def count {ι : Type} [Fintype ι] (P : ι → Prop) : ℝ :=
  ∑ i, if P i then 1 else 0

private theorem count_pos {ι : Type} [Fintype ι] (P : ι → Prop) :
    0 < count P ↔ ∃ i, P i := by
  simp [count, Finset.card_pos, Finset.Nonempty]

private def edges (G : Graph) := count (fun p : G.V × G.V => G.gr.Adj p.1 p.2)
private def gaps (G : Graph) := count (fun p : G.V × G.V => p.1 ≠ p.2 ∧ ¬ G.gr.Adj p.1 p.2)
private def triangles (G : Graph) := count fun p : G.V × G.V × G.V =>
  G.gr.Adj p.1 p.2.1 ∧ G.gr.Adj p.2.1 p.2.2 ∧ G.gr.Adj p.2.2 p.1

theorem trace_two (G : Graph) : ((adj G)^2).trace = edges G := by
  simp only [edges, count, Matrix.trace, Matrix.diag_apply, pow_two, Matrix.mul_apply,
    Fintype.sum_prod_type, adj, SimpleGraph.adjMatrix_apply]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  by_cases h : G.gr.Adj i j
  · simp [h,h.symm]
  · simp [h]

theorem trace_three (G : Graph) : ((adj G)^3).trace = triangles G := by
  simp only [triangles, count, Matrix.trace, Matrix.diag_apply, pow_succ', pow_zero, mul_one,
    Matrix.mul_apply, Finset.mul_sum, Fintype.sum_prod_type, adj, SimpleGraph.adjMatrix_apply]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro j _
  apply sum_congr rfl; intro k _
  split_ifs <;> simp_all

private theorem account (G : Graph) :
    edges G + gaps G + (Fintype.card G.V : ℝ) = (Fintype.card G.V : ℝ)^2 := by
  have diag : count (fun p : G.V × G.V => p.1 = p.2) = Fintype.card G.V := by
    unfold count
    rw [Fintype.sum_prod_type]
    simp
  have total : (∑ _ : G.V × G.V, (1:ℝ)) = (Fintype.card G.V : ℝ)^2 := by simp [pow_two]
  rw [← total, ← diag]
  unfold edges gaps count
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl; rintro ⟨i,j⟩ _
  by_cases h : i=j
  · subst j; simp
  · by_cases a : G.gr.Adj i j <;> simp [h,a]

theorem rs_point : RS (clq 1) := by
  intro G H h
  rw [has_one, has_one, ← Fintype.card_pos_iff, ← Fintype.card_pos_iff, card_eq h]

theorem rs_edge : RS (clq 2) := by
  have key (G : Graph) : Has (clq 2) G ↔ 0 < ((adj G)^2).trace := by
    simp [has_edge, trace_two, edges, count_pos]
  intro G H h
  rw [key, key, moment_eq h]

theorem rs_independent_pair : RS (clq 1 ⊞ clq 1) := by
  have key (G : Graph) : Has (clq 1 ⊞ clq 1) G ↔ 0 < gaps G := by
    simp [has_independent_pair, gaps, count_pos]
  intro G H h
  have a := account G
  have b := account H
  rw [← trace_two, moment_eq h, card_eq h, trace_two] at a
  rw [key, key, show gaps G = gaps H by linarith]

theorem rs_triangle : RS (clq 3) := by
  have key (G : Graph) : Has (clq 3) G ↔ 0 < ((adj G)^3).trace := by
    simp [has_triangle, trace_three, triangles, count_pos]
  intro G H h
  rw [key, key, moment_eq h]

/-- In a path-free graph, equality or adjacency is an equivalence relation.
The shifted matrix is the submatrix of the identity pulled back from the
quotient by that relation. Conversely, the three path vertices support a
vector of strictly negative quadratic form. -/
theorem path_free_iff_psd (G : Graph) : ¬ Has (bic 1 2) G ↔ (shifted G).PosSemidef := by
  rw [has_path]
  constructor
  · intro no
    let s : Setoid G.V := {
      r := fun x y => x = y ∨ G.gr.Adj x y
      iseqv := {
        refl := fun _ => Or.inl rfl
        symm := fun h => h.elim (fun e => Or.inl e.symm) (fun a => Or.inr a.symm)
        trans := by
          intro x y z a b
          rcases a with rfl | h
          · exact b
          rcases b with rfl | k
          · exact Or.inr h
          by_contra! q
          exact no ⟨x,y,z,h,k,q.1,q.2⟩ } }
    let f := @Quotient.mk _ s
    have mat : shifted G = (1 : Matrix (Quotient s) (Quotient s) ℝ).submatrix f f := by
      ext x y
      have eqc : f x = f y ↔ x = y ∨ G.gr.Adj x y := Quotient.eq
      by_cases h : x=y
      · subst y; simp [shifted, adj, Matrix.one_apply]
      · by_cases a : G.gr.Adj x y <;> simp [shifted, adj, Matrix.one_apply, eqc, h, a]
    rw [mat]
    exact Matrix.PosSemidef.one.submatrix f
  · rintro ps ⟨x,y,z,h,k,ne,no⟩
    let f : Fin 3 → G.V := ![x,y,z]
    have hn : ¬ G.gr.Adj z x := fun a => no a.symm
    have mat : (shifted G).submatrix f f = !![(1:ℝ),1,0;1,1,1;0,1,1] := by
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [shifted, adj, f, Matrix.one_apply, h,k,h.symm,k.symm,h.ne,k.ne,h.ne.symm,k.ne.symm,
          no,hn,ne,ne.symm]
    have ps' := ps.submatrix f
    rw [mat] at ps'
    have bad := ps'.dotProduct_mulVec_nonneg ![(1:ℝ),-2,1]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at bad

theorem rs_path : RS (bic 1 2) := by
  intro G H h
  apply not_iff_not.mp
  rw [path_free_iff_psd, path_free_iff_psd]
  exact shifted_psd_congr h

end
end Barranca
