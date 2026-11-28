import Conjectures.Barranca.Basic
import Mathlib.Analysis.Matrix.PosDef

/-! Two spectral invariants used to recognize small induced patterns:
closed-walk counts, and positive semidefiniteness after shifting by one. -/
namespace Barranca

open SimpleGraph Matrix Polynomial Finset
open scoped Classical BigOperators
noncomputable section

def adj (G : Graph) := G.gr.adjMatrix ℝ

theorem herm (G : Graph) : (adj G).IsHermitian := by
  apply Matrix.ext
  intro i j
  simp [adj, Matrix.conjTranspose_apply, SimpleGraph.adj_comm]

theorem real_charpoly (G : Graph) : (adj G).charpoly = (cp G).map (Int.castRingHom ℝ) := by
  unfold cp
  rw [← Matrix.charpoly_map]
  congr 1
  ext i j
  by_cases h : G.gr.Adj i j <;> simp [adj, h]

theorem card_eq {G H : Graph} (h : cp G = cp H) : Fintype.card G.V = Fintype.card H.V := by
  simpa [cp] using congrArg Polynomial.natDegree h

/-- The trace of a power is the corresponding power sum over the roots, including repeats. -/
theorem moment_roots (G : Graph) (k : ℕ) :
    ((adj G)^k).trace = ((adj G).charpoly.roots.map (· ^ k)).sum := by
  have h := herm G
  conv_lhs => rw [h.spectral_theorem, ← map_pow, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_pow,
    Matrix.trace_diagonal]
  rw [h.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  rfl

theorem moment_eq {G H : Graph} (h : cp G = cp H) (k : ℕ) :
    ((adj G)^k).trace = ((adj H)^k).trace := by
  rw [moment_roots, moment_roots, real_charpoly, real_charpoly, h]

def shifted (G : Graph) : Matrix G.V G.V ℝ := adj G + 1

theorem shifted_charpoly (G : Graph) :
    (shifted G).charpoly = (adj G).charpoly.comp (X + C (-1)) := by
  rw [← Matrix.charpoly_sub_scalar]
  congr 1
  ext i j
  by_cases h : i=j <;> simp [shifted, Matrix.one_apply, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem psd_iff_roots (G : Graph) :
    (shifted G).PosSemidef ↔ ∀ x ∈ (shifted G).charpoly.roots, 0 ≤ x := by
  have h : (shifted G).IsHermitian := (herm G).add Matrix.isHermitian_one
  rw [h.posSemidef_iff_eigenvalues_nonneg, h.roots_charpoly_eq_eigenvalues]
  simp [Pi.le_def]

theorem shifted_psd_congr {G H : Graph} (h : cp G = cp H) :
    (shifted G).PosSemidef ↔ (shifted H).PosSemidef := by
  rw [psd_iff_roots, psd_iff_roots, shifted_charpoly, shifted_charpoly,
    real_charpoly, real_charpoly, h]
end
end Barranca
