import Mathlib

/-!
# The slice-cover test for odd-coloring extensions

The finite six-color certificate uses signatures: at each interface vertex a
signature stores the parity vector contributed by the interior. An exterior
tuple obstructs extension precisely if every signature agrees with it at
some coordinate. This module proves the cover recursion for any signature
family, and proves the parity gluing criterion directly for finite graphs.
It does not certify the finite table for four-trees.
-/

namespace KashimaOzekiKtreeOddColoring

/-- There is a permitted tuple that hits every signature, using only
coordinates in `I`. -/
def Covered {ι M : Type*} (allowed : M → Prop) (I : Set ι) (S : Set (ι → M)) : Prop :=
  ∃ b : ι → M, (∀ i, allowed (b i)) ∧ ∀ s ∈ S, ∃ i ∈ I, s i = b i

/-- Duality between a slice cover and simultaneous avoidance. -/
theorem not_covered_iff {ι M : Type*} (allowed : M → Prop) (I : Set ι)
    (S : Set (ι → M)) :
    ¬ Covered allowed I S ↔
      ∀ b : ι → M, (∀ i, allowed (b i)) → ∃ s ∈ S, ∀ i ∈ I, s i ≠ b i := by
  classical
  constructor
  · intro hn b hb
    by_contra h
    push Not at h
    exact hn ⟨b, hb, h⟩
  · rintro h ⟨b, hb, hc⟩
    obtain ⟨s, hs, ha⟩ := h b hb
    obtain ⟨i, hi, he⟩ := hc s hs
    exact ha i hi he

/-- At a chosen uncovered signature, it suffices to branch on its allowed
entries; the matching slice and the selected coordinate can both be removed. -/
theorem covered_iff_step {ι M : Type*} (allowed : M → Prop)
    (I : Set ι) (S : Set (ι → M)) {s : ι → M} (hs : s ∈ S) :
    Covered allowed I S ↔ ∃ i ∈ I, allowed (s i) ∧
      Covered allowed (I \ {i}) {t | t ∈ S ∧ t i ≠ s i} := by
  classical
  constructor
  · rintro ⟨b, hb, hc⟩
    obtain ⟨i, hi, he⟩ := hc s hs
    refine ⟨i, hi, he ▸ hb i, b, hb, ?_⟩
    rintro t ⟨ht, hd⟩
    obtain ⟨j, hj, hjb⟩ := hc t ht
    refine ⟨j, ⟨hj, ?_⟩, hjb⟩
    rintro rfl
    exact hd (hjb.trans he.symm)
  · rintro ⟨i, hi, ha, b, hb, hc⟩
    let b' : ι → M := fun j => if j = i then s i else b j
    refine ⟨b', ?_, ?_⟩
    · intro j
      by_cases h : j = i <;> simp [b', h, ha, hb]
    · intro t ht
      by_cases he : t i = s i
      · exact ⟨i, hi, by simpa [b'] using he⟩
      · obtain ⟨j, hj, hjb⟩ := hc t ⟨ht, he⟩
        have hji : j ≠ i := hj.2
        exact ⟨j, hj.1, by simpa [b', hji] using hjb⟩

section Graph

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Multiplicity of color `a` among the neighbors of `v` in `D`. -/
def multiplicity (c : V → C) (D : Finset V) (v : V) (a : C) : ℕ :=
  (D.filter fun w => G.Adj v w ∧ c w = a).card

/-- The local odd condition on the whole graph. -/
def OddAt (c : V → C) (v : V) : Prop :=
  ∃ a, multiplicity G c Finset.univ v a % 2 = 1

/-- On an interface vertex, the exterior mask must be different from the
interior mask. Here the masks are represented by their color coordinates. -/
theorem oddAt_iff_masks_differ (c : V → C) (D : Finset V) (v : V) :
    OddAt G c v ↔ ∃ a,
      multiplicity G c D v a % 2 ≠ multiplicity G c Dᶜ v a % 2 := by
  classical
  have hsum (a : C) : multiplicity G c D v a + multiplicity G c Dᶜ v a =
      multiplicity G c Finset.univ v a := by
    unfold multiplicity
    rw [← Finset.card_union_of_disjoint]
    · rw [← Finset.filter_union, Finset.union_compl]
    · exact Finset.disjoint_filter_filter <| disjoint_compl_right
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by have := hsum a; omega⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by have := hsum a; omega⟩

end Graph
end KashimaOzekiKtreeOddColoring
