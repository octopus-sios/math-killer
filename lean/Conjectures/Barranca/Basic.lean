import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-! Finite simple graphs, recognizability by the integer adjacency characteristic polynomial, and disjoint sums. -/
namespace Barranca

open SimpleGraph Matrix Polynomial Finset
open scoped Classical BigOperators
set_option linter.unusedSimpArgs false

noncomputable section

structure Graph where
  V : Type
  ft : Fintype V
  gr : SimpleGraph V

attribute [instance] Graph.ft

def pack (V : Type) [Fintype V] (G : SimpleGraph V) : Graph := ⟨V, inferInstance, G⟩

def cp (G : Graph) : ℤ[X] := (G.gr.adjMatrix ℤ).charpoly

theorem cp_pack (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] : cp (pack V G) = (G.adjMatrix ℤ).charpoly := by
  unfold cp pack
  congr!

def plus (G H : Graph) : Graph := pack _ (G.gr ⊕g H.gr)
infixr:62 " ⊞ " => plus

def Has (H G : Graph) : Prop := Nonempty (H.gr ↪g G.gr)

/-- Recognizability for the ordinary adjacency spectrum, via its characteristic polynomial. -/
def RS (H : Graph) : Prop := ∀ A B : Graph, cp A = cp B → (Has H A ↔ Has H B)

def zeroG (n : ℕ) : Graph := pack (Fin n) ⊥
def clq (n : ℕ) : Graph := pack (Fin n) (completeGraph _)
def bic (a b : ℕ) : Graph := pack _ (completeBipartiteGraph (Fin a) (Fin b))

theorem cp_plus (G H : Graph) : cp (G ⊞ H) = cp G * cp H := by
  have he : (G.gr ⊕g H.gr).adjMatrix ℤ =
      fromBlocks (G.gr.adjMatrix ℤ) 0 0 (H.gr.adjMatrix ℤ) := by
    ext (i|i) (j|j) <;> simp [SimpleGraph.adjMatrix_apply, Matrix.fromBlocks]
  unfold plus
  rw [cp_pack]
  rw [he, Matrix.charpoly_fromBlocks_zero₁₂]
  unfold cp
  congr!

theorem has_congr {F F' G G' : Graph} (i : F.gr ≃g F'.gr) (j : G.gr ≃g G'.gr) :
    Has F G ↔ Has F' G' := by
  constructor
  · rintro ⟨f⟩; exact ⟨(j.toEmbedding.comp f).comp i.symm.toEmbedding⟩
  · rintro ⟨f⟩; exact ⟨(j.symm.toEmbedding.comp f).comp i.toEmbedding⟩

theorem rs_congr {F F' : Graph} (i : F.gr ≃g F'.gr) : RS F ↔ RS F' := by
  have h (G : Graph) : Has F G ↔ Has F' G :=
    ⟨fun ⟨f⟩ => ⟨f.comp i.symm.toEmbedding⟩, fun ⟨f⟩ => ⟨f.comp i.toEmbedding⟩⟩
  constructor <;> intro hr A B hc
  · exact (h A).symm.trans ((hr A B hc).trans (h B))
  · exact (h A).trans ((hr A B hc).trans (h B).symm)

end
end Barranca
