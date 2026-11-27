import Conjectures.NabergallChordalDiagrams.Counting
import Conjectures.NabergallChordalDiagrams.Series

/-! # Enumeration of the actual connected chordal matchings -/

namespace NabergallChordalDiagrams
namespace Counting
noncomputable section
open scoped Classical

private theorem scalar_count (m : Rule) (n k : ℕ) :
    Fintype.card (Target m n k) =
      ∑ ab ∈ Finset.antidiagonal n, ∑ i ∈ Finset.range ab.1, ∑ j ∈ Finset.range ab.2,
        I_count ab.1 (i+1) * H_count ab.2 (j+1) * Fintype.card (Choice m (i+1) (j+1) k) := by
  rw [Fintype.card_congr (decomposition m n k)]
  simp only [Terms, Fintype.card_sigma, Fintype.card_prod, I_count, H_count, Nat.mul_assoc]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro ab _
  conv_rhs => rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  conv_rhs => rw [← Fin.sum_univ_eq_sum_range]

private theorem free_choices (i j k : ℕ) : Fintype.card (Choice .sequence i j k) =
    (Finsupp.single (i+j) 1 : Series.WeightRow) k := by
  by_cases h : i+j=k
  · let z : Choice .sequence i j k := ⟨⟨0,by omega⟩,rfl,by simpa using h⟩
    haveI : Unique (Choice .sequence i j k) :=
      ⟨⟨z⟩,fun x => Subtype.ext (Fin.ext (x.property.1 : x.val.val=0))⟩
    simp [Finsupp.single_apply,h]
  · haveI : IsEmpty (Choice .sequence i j k) := ⟨fun x =>
      let hz : x.val.val=0 := x.property.1
      h (by simpa [hz] using x.property.2)⟩
    simp [Finsupp.single_apply,h]

private def relabelLinks (i j k : ℕ) : Choice .linked i (j+1) k ≃
    {u : Fin (min i j) // i+j-1-2*u.val=k} where
  toFun x := by
    obtain ⟨t,⟨ht,ltj⟩,w⟩ := x
    have := t.isLt
    exact ⟨⟨t.val-1,by omega⟩,by dsimp; omega⟩
  invFun x := by
    obtain ⟨u,w⟩ := x
    have := u.isLt
    exact ⟨⟨u.val+1,by omega⟩,⟨by dsimp; omega,by dsimp; omega⟩,by dsimp; omega⟩
  left_inv x := by
    apply Subtype.ext; apply Fin.ext
    change x.val.val-1+1=x.val.val
    have := x.property.1.1; omega
  right_inv x := by
    apply Subtype.ext; apply Fin.ext; change x.val.val+1-1=x.val.val; omega

private theorem linked_choices (i j k : ℕ) : Fintype.card (Choice .linked i (j+1) k) =
    Series.links i j k := by
  rw [Fintype.card_congr (relabelLinks i j k),Series.links_apply,← Fin.sum_univ_eq_sum_range]
  simp only [Finset.sum_boole]
  let S := (Finset.univ : Finset (Fin (min i j))).filter (fun u => i+j-1-2*u.val=k)
  let e : {u : Fin (min i j) // i+j-1-2*u.val=k} ≃ ↥S :=
    Equiv.subtypeEquivRight (fun _ => by simp [S])
  exact (Fintype.card_congr e).trans (Fintype.card_coe S)

private theorem seq_count (n k : ℕ) : H_count n k =
    I_count n k + Series.splitCounts I_count H_count (fun i j => Finsupp.single (i+j) 1) n k := by
  let e : ValidFragment n k ≃ IrreducibleFragment n k ⊕ Target .sequence n k :=
    (Equiv.sumCompl (fun F : ValidFragment n k => F.val.Irreducible)).symm
  have sum : H_count n k = I_count n k + Fintype.card (Target .sequence n k) := by
    simpa only [I_count, H_count, ← Nat.card_eq_fintype_card] using
      (Fintype.card_congr e).trans Fintype.card_sum
  rw [sum,scalar_count,Series.splitCounts_apply]
  simp only [free_choices]

private def oneFragment : Fragment 1 := ⟨id,fun _ => rfl⟩

private theorem irreducible_one : I_count 1 1 = 1 := by
  have wf : oneFragment.weight=1 := by
    rw [Fragment.weight_eq_one_iff]
    exact ⟨0,fun x => ⟨fun _ => Subsingleton.elim _ _,fun _ => rfl⟩⟩
  haveI : Nonempty oneFragment.Chord := ⟨⟨0,le_rfl⟩⟩
  have ch : Chordal oneFragment.graph := by
    intro k hk f inj _
    let u : Fin k := ⟨0,by omega⟩
    let v : Fin k := ⟨1,by omega⟩
    have e := congrArg Fin.val (inj (Subsingleton.elim (f u) (f v)))
    exact Nat.zero_ne_one e
  let x : IrreducibleFragment 1 1 :=
    ⟨⟨oneFragment,⟨SimpleGraph.Connected.of_subsingleton,ch⟩,wf,Nat.zero_lt_one⟩,
      fun g hp hq => (by omega : False).elim⟩
  haveI : Unique (IrreducibleFragment 1 1) := ⟨⟨x⟩,fun _ => Subsingleton.elim _ _⟩
  exact Fintype.card_unique

private theorem seed_count (n k : ℕ) :
    I_count n k = Series.seed n k + Fintype.card (Target .linked n k) := by
  by_cases hn : 2≤n
  · let e : IrreducibleFragment n k ≃ Target .linked n k :=
      Equiv.subtypeEquivRight (fun _ => ⟨fun h => ⟨h,hn⟩,And.left⟩)
    simpa [I_count,Series.seed,show n≠1 by omega, ← Nat.card_eq_fintype_card] using Fintype.card_congr e
  · haveI : IsEmpty (Target .linked n k) := ⟨fun x => hn x.property.2⟩
    simp only [Fintype.card_of_isEmpty, Nat.add_zero]
    rcases (show n=0 ∨ n=1 by omega) with rfl|rfl
    · cases k with
      | zero => simpa [Series.seed] using I_count_zero 0
      | succ k => simpa [Series.seed] using I_count_support 0 (k+1) (by omega)
    · by_cases hk : k=0
      · subst k; simpa [Series.seed] using I_count_zero 1
      by_cases hk' : k=1
      · subst k; simpa [Series.seed] using irreducible_one
      · simpa [Series.seed,Finsupp.single_apply,Ne.symm hk'] using I_count_support 1 k (by omega)

private theorem linked_count (n k : ℕ) : I_count n k =
    Series.seed n k + Series.splitCounts I_count H_count (fun i j => Series.links i (j-1)) n k := by
  rw [seed_count n k, scalar_count, Series.splitCounts_apply]
  simp only [linked_choices, Nat.add_sub_cancel]

end
end Counting

/-- The earliest-cut and sequence recurrences for cardinalities of the
actual finite sets of fragments (not for an independently generated table). -/
theorem fragment_recurrences : Series.Recurrences I_count H_count :=
  Series.Recurrences.of_pointwise I_count_zero H_count_zero I_count_support H_count_support
    Counting.seq_count Counting.linked_count

/-- Nabergall, Conjecture 8.5 (published index). The root is position zero;
the matchings are not taken up to dihedral symmetry. -/
theorem connectedChordalDiagram_card (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (ConnectedChordalDiagram n) = catalan (n-1)^2 :=
  (card_eq_weight_one n hn).trans (Series.count_weight_one_shift I_count H_count fragment_recurrences hn)

/-- Size `n+1` form, with no positivity hypothesis. -/
theorem connectedChordalDiagram_card_succ (n : ℕ) :
    Fintype.card (ConnectedChordalDiagram (n+1)) = catalan n ^ 2 := by
  simpa using connectedChordalDiagram_card (n+1) (Nat.le_add_left 1 n)

end NabergallChordalDiagrams
