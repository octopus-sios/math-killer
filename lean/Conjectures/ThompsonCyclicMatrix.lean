import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Rank-one perturbation lemmas for the two-cycle proof of the rank-one
stratum of Thompson's permutation-cyclicity problem. Apply these to the
linear map `T = P - z • id` and the functional `ℓ = vᵀ P`.
The field arithmetic and the selection of the cycles are in the written proof. -/

namespace ThompsonCyclicMatrix

open LinearMap

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- An update direction outside the range cannot cancel a nonzero range vector. -/
theorem ker_update_of_notMem_range (T : V →ₗ[F] V) (u : V) (ℓ : V →ₗ[F] F)
    (hu : u ∉ LinearMap.range T) :
    LinearMap.ker (T + ℓ.smulRight u) = LinearMap.ker T ⊓ LinearMap.ker ℓ := by
  ext x
  change T x + ℓ x • u = 0 ↔ T x = 0 ∧ ℓ x = 0
  constructor
  · intro h
    have hx : ℓ x = 0 := by
      by_contra hn
      apply hu
      refine ⟨(-(ℓ x)⁻¹) • x, ?_⟩
      have ht : T x = -(ℓ x • u) := eq_neg_of_add_eq_zero_left h
      simp [map_smul, ht, smul_smul, hn]
    exact ⟨by simpa [hx] using h, hx⟩
  · rintro ⟨ht, hx⟩
    simp [ht, hx]

/-- At an old eigenvalue with two Jordan blocks the two-sided test
cuts geometric multiplicity to at most one. -/
theorem finrank_ker_update_of_two [FiniteDimensional F V]
    (T : V →ₗ[F] V) (u : V) (ℓ : V →ₗ[F] F)
    (hu : u ∉ LinearMap.range T) (hdim : Module.finrank F (LinearMap.ker T) = 2)
    (hv : ∃ x, T x = 0 ∧ ℓ x ≠ 0) :
    Module.finrank F (LinearMap.ker (T + ℓ.smulRight u)) ≤ 1 := by
  rw [ker_update_of_notMem_range _ _ _ hu]
  obtain ⟨x, hx, hl⟩ := hv
  have hlt : LinearMap.ker T ⊓ LinearMap.ker ℓ < LinearMap.ker T := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    have hmem : x ∈ LinearMap.ker T ⊓ LinearMap.ker ℓ := by
      rw [heq]
      exact hx
    exact hl hmem.2
  have h := Submodule.finrank_lt_finrank_of_lt hlt
  rw [hdim] at h
  exact Nat.le_of_lt_succ h

/-- Away from the old spectrum the update has nullity at most one. -/
theorem finrank_ker_update_of_injective [FiniteDimensional F V]
    (T : V →ₗ[F] V) (u : V) (ℓ : V →ₗ[F] F) (hinj : Function.Injective T) :
    Module.finrank F (LinearMap.ker (T + ℓ.smulRight u)) ≤ 1 := by
  let K := LinearMap.ker (T + ℓ.smulRight u)
  let f : K →ₗ[F] F := ℓ.comp K.subtype
  have hf : Function.Injective f := by
    intro x y h
    change ℓ (x : V) = ℓ (y : V) at h
    apply Subtype.ext
    apply hinj
    have hx : T (x : V) + ℓ (x : V) • u = 0 := x.property
    have hy : T (y : V) + ℓ (y : V) • u = 0 := y.property
    rw [h] at hx
    exact add_right_cancel (hx.trans hy.symm)
  simpa only [Module.finrank_self] using LinearMap.finrank_le_finrank_of_injective hf

end ThompsonCyclicMatrix
