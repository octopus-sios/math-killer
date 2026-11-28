import Conjectures.MarcusDeOliveira.Matching
import Conjectures.MarcusDeOliveira.Arrowhead
import Conjectures.MarcusDeOliveira.MinorBridge
import Conjectures.MarcusDeOliveira.AllCompounds
import Conjectures.MarcusDeOliveira.Collision
import Conjectures.MarcusDeOliveira.Displacement
import Conjectures.MarcusDeOliveira.Stationary
import Conjectures.MarcusDeOliveira.Cut
import Conjectures.MarcusDeOliveira.Projective
import Conjectures.MarcusDeOliveira.Hadamard
import Conjectures.MarcusDeOliveira.Facet
import Conjectures.MarcusDeOliveira.TaoForbidden

/-! Verified Lean 4.35.0 formalization suite for the Marcus–de Oliveira Conjecture campaign.

Covers:
* `Matching`, `Arrowhead`, `MinorBridge`, `AllCompounds`: exact 14-noncrossing-permutation
  probability law reproducing all 70 squared minors and all complex determinant pencils for
  every 4×4 interlacing Hermitian arrowhead eigenbasis.
* `Collision`: full 4×4 Cross-Spectral Collision Theorem (for arbitrary complex spectra with
  a_i + b_j = 0 and arbitrary U ∈ U(4)).
* `Displacement`, `Stationary`, `Cut`: matrix-level displacement and algebraic cut recovery
  for the Separate-Circle One-Outlier Theorem.
* `Projective`: arbitrary-order PGL₂(ℂ) invariance of MOC.
* `Hadamard`: Klein-four protection placing every 4×4 complex Hadamard matrix inside Π₄.
* `Facet`: exact rational SO(4) breach witness (−316/2401) and nonnegativity over all 24 permutations.
* `TaoForbidden`: exact 45-zero 2×2 minor obstruction for Tao's 6×6 complex Hadamard matrix.
-/
