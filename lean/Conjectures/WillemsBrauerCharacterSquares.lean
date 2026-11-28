import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Tensor-quotient degree bound for the defining-characteristic step

A nonzero equivariant map from S ⊗ V, with S irreducible, gives the lower
bound dim W ≥ dim S / dim V even in positive characteristic. This is the
representation-theoretic estimate used with S the Steinberg module, not a
formalization of the classification or of the entire character inequality.
-/

namespace WillemsBrauerCharacterSquares

open scoped TensorProduct
open Representation

variable {k G S V W : Type*} [Field k] [Group G]
    [AddCommGroup S] [Module k S]
    [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The modular tensor-quotient bound; only a nonzero intertwiner, not a
semisimple tensor product, is needed. -/
theorem tensor_quotient_degree (ρ : Representation k G S) (σ : Representation k G V)
    (τ : Representation k G W) [ρ.IsIrreducible]
    (q : (ρ.tprod σ).IntertwiningMap τ) (hq : q ≠ 0) :
    Module.finrank k S ≤ Module.finrank k V * Module.finrank k W := by
  let F : ρ.IntertwiningMap (σ.linHom τ) :=
    { toLinearMap := TensorProduct.curry q.toLinearMap
      isIntertwining' := fun g => by
        apply LinearMap.ext
        intro x
        apply LinearMap.ext
        intro y
        change q ((ρ g x) ⊗ₜ[k] y) = τ g (q (x ⊗ₜ[k] σ g⁻¹ y))
        have h : σ g (σ g⁻¹ y) = y := by
          change ((σ g) * (σ g⁻¹)) y = y
          rw [← map_mul, mul_inv_cancel, map_one]
          rfl
        simpa only [Representation.tprod_apply, TensorProduct.map_tmul, h] using
          Representation.IntertwiningMap.isIntertwining (ρ.tprod σ) τ q g (x ⊗ₜ[k] σ g⁻¹ y) }
  have hn : F ≠ 0 := by
    intro h
    apply hq
    apply Representation.IntertwiningMap.ext
    apply TensorProduct.ext'
    intro x y
    exact congrArg (fun f : ρ.IntertwiningMap (σ.linHom τ) => f x y) h
  have hi := (Representation.IsIrreducible.injective_or_eq_zero F).resolve_right hn
  have hd := LinearMap.finrank_le_finrank_of_injective (f := F.toLinearMap) hi
  simpa only [Module.finrank_linearMap] using hd

end WillemsBrauerCharacterSquares
