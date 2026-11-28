import Conjectures.Barranca.Classification
import Conjectures.Barranca.Positive

/-! Barranca, Conjecture 2.1.2. Hosts are arbitrary finite simple graphs,
and containment is by an adjacency-reflecting injection. -/
namespace Barranca
open SimpleGraph

theorem rs_null : RS (clq 0) := by
  have occurs (A : Graph) : Has (clq 0) A := by
    refine ⟨{ toFun := Fin.elim0, inj' := fun x => Fin.elim0 x, map_rel_iff' := ?_ }⟩
    intro x; exact Fin.elim0 x
  intro A B _
  exact iff_of_true (occurs A) (occurs B)

theorem rs_iff_listed (H : Graph) : RS H ↔ Listed H := by
  refine ⟨only_listed H, ?_⟩
  rintro ⟨t, ⟨i⟩⟩
  apply (rs_congr i).mpr
  cases t
  · exact rs_null
  · exact rs_point
  · exact rs_independent_pair
  · exact rs_edge
  · exact rs_triangle
  · exact rs_path

/-- The five isomorphism types in Barranca's conjecture for nonempty patterns. -/
theorem recognizable_iff (H : Graph) (hne : Nonempty H.V) :
    RS H ↔
      Nonempty (H.gr ≃g (clq 1).gr) ∨
      Nonempty (H.gr ≃g (clq 1 ⊞ clq 1).gr) ∨
      Nonempty (H.gr ≃g (clq 2).gr) ∨
      Nonempty (H.gr ≃g (clq 3).gr) ∨
      Nonempty (H.gr ≃g (bic 1 2).gr) := by
  rw [rs_iff_listed]
  constructor
  · rintro ⟨t, ⟨i⟩⟩
    cases t with
    | null => exact Fin.elim0 (i (Classical.choice hne))
    | pt => exact Or.inl ⟨i⟩
    | independentPair => exact Or.inr <| Or.inl ⟨i⟩
    | edge => exact Or.inr <| Or.inr <| Or.inl ⟨i⟩
    | triangle => exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨i⟩
    | path => exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨i⟩
  · rintro (h|h|h|h|h)
    · exact ⟨.pt,h⟩
    · exact ⟨.independentPair,h⟩
    · exact ⟨.edge,h⟩
    · exact ⟨.triangle,h⟩
    · exact ⟨.path,h⟩

end Barranca
