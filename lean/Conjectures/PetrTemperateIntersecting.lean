import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.NormNum

/-! The lightning lower bound for every even dimension, and the sharp unrestricted
upper bound in dimension four. These results do not assert the conjectural upper
bound in arbitrary dimension. -/

namespace PetrTemperateIntersecting

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

def Intersecting (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, ∀ B ∈ F, ¬ Disjoint A B

def Temperate (F : Finset (Finset α)) : Prop :=
  ∀ A ∈ F, (F.filter (· ⊆ A)).card ≤ 1 + A.card

def lightning (p : α) (k : ℕ) : Finset (Finset α) :=
  ((univ.powersetCard k).filter (p ∈ ·) ∪ univ.powersetCard (k+1)) ∪
    ((univ.powersetCard (k+2)).filter (p ∉ ·))

private theorem mem_lightning {A : Finset α} {p : α} {k : ℕ} :
    A ∈ lightning p k ↔
      (A.card = k ∧ p ∈ A) ∨ A.card = k + 1 ∨ (A.card = k + 2 ∧ p ∉ A) := by
  simp [lightning, Finset.mem_powersetCard]

theorem lightning_intersecting (p : α) (k : ℕ) (hn : Fintype.card α = 2*k) :
    Intersecting (lightning p k) := by
  intro A hA B hB hd
  have hle := Finset.card_le_univ (A ∪ B)
  rw [Finset.card_union_of_disjoint hd, hn] at hle
  rcases mem_lightning.mp hA with hA | hA | hA <;>
    rcases mem_lightning.mp hB with hB | hB | hB
  all_goals first | exact Finset.disjoint_left.mp hd hA.2 hB.2 | omega

theorem lightning_temperate (p : α) {k : ℕ} (hk : 2 ≤ k) :
    Temperate (lightning p k) := by
  intro A hA
  have hpos : 1 ≤ A.card := by
    rcases mem_lightning.mp hA with h | h | h <;> omega
  have hs : (lightning p k).filter (· ⊆ A) ⊆ insert A (A.powersetCard (A.card - 1)) := by
    intro B hB
    obtain ⟨hm, hBA⟩ := Finset.mem_filter.mp hB
    by_cases heq : B = A
    · simp [heq]
    · have hlt : B.card < A.card := Finset.card_lt_card (lt_of_le_of_ne hBA heq)
      apply Finset.mem_insert_of_mem
      apply Finset.mem_powersetCard.mpr
      refine ⟨hBA, ?_⟩
      rcases mem_lightning.mp hA with ha | ha | ha <;>
        rcases mem_lightning.mp hm with hb | hb | hb
      all_goals first | exact False.elim (ha.2 (hBA hb.2)) | omega
  calc
    _ ≤ (insert A (A.powersetCard (A.card - 1))).card := Finset.card_le_card hs
    _ ≤ (A.powersetCard (A.card - 1)).card + 1 := Finset.card_insert_le _ _
    _ = 1 + A.card := by rw [Finset.card_powersetCard, Nat.choose_symm hpos, Nat.choose_one_right]; omega

private theorem avoid_card (p : α) (r : ℕ) :
    ((univ.powersetCard r).filter (p ∉ ·)).card = (Fintype.card α - 1).choose r := by
  have heq : (univ.powersetCard r).filter (p ∉ ·) = (univ.erase p).powersetCard r := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    constructor
    · rintro ⟨hc, hp⟩
      exact ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hp (h ▸ hx), Finset.mem_univ _⟩, hc⟩
    · rintro ⟨h, hc⟩
      exact ⟨hc, fun hp => (Finset.mem_erase.mp (h hp)).1 rfl⟩
  rw [heq, Finset.card_powersetCard, Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ]

theorem lightning_card (p : α) {k : ℕ} (hk : 2 ≤ k) (hn : Fintype.card α = 2*k) :
    (lightning p k).card =
      (2*k).choose k / 2 + (2*k).choose (k+1) + (2*k-1).choose (k+2) := by
  let L := (univ.powersetCard k).filter (p ∈ ·)
  let M := (univ : Finset α).powersetCard (k+1)
  let H := ((univ : Finset α).powersetCard (k+2)).filter (p ∉ ·)
  have hsplit := Finset.card_filter_add_card_filter_not (s := (univ : Finset α).powersetCard k) (fun a => p ∈ a)
  rw [avoid_card, Finset.card_powersetCard, Finset.card_univ, hn] at hsplit
  have hsame : (2*k-1).choose (k-1) = (2*k-1).choose k := by
    have h := Nat.choose_symm (show k ≤ 2*k-1 by omega)
    rwa [show 2*k-1-k = k-1 by omega] at h
  have hpas : (2*k).choose k = (2*k-1).choose (k-1) + (2*k-1).choose k := by
    have h := Nat.choose_succ_succ (2*k-1) (k-1)
    simpa only [Nat.succ_eq_add_one, show 2*k-1+1 = 2*k by omega,
      show k-1+1 = k by omega] using h
  have hL : L.card = (2*k).choose k / 2 := by dsimp [L]; omega
  have dLM : Disjoint L M := Finset.disjoint_left.mpr (by
    intro a ha hb
    have h1 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp ha).1).2
    have h2 := (Finset.mem_powersetCard.mp hb).2
    omega)
  have dLH : Disjoint (L ∪ M) H := Finset.disjoint_left.mpr (by
    intro a ha hb
    have h3 := (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hb).1).2
    rcases Finset.mem_union.mp ha with ha | ha
    · exact (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp ha).2
    · have h2 := (Finset.mem_powersetCard.mp ha).2
      omega)
  change ((L ∪ M) ∪ H).card = _
  rw [Finset.card_union_of_disjoint dLH, Finset.card_union_of_disjoint dLM, hL]
  simp [M, H, avoid_card, hn]

theorem lightning_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ F : Finset (Finset (Fin (2*k))), Intersecting F ∧ Temperate F ∧
      F.card = (2*k).choose k / 2 + (2*k).choose (k+1) + (2*k-1).choose (k+2) := by
  let p : Fin (2*k) := ⟨0, by omega⟩
  exact ⟨lightning p k, lightning_intersecting p k (by simp), lightning_temperate p hk,
    lightning_card p hk (by simp)⟩

theorem upper_four (F : Finset (Finset (Fin 4))) (hi : Intersecting F) (ht : Temperate F) :
    F.card ≤ 7 := by
  classical
  by_cases h : univ ∈ F
  · have hh := ht _ h
    simp at hh
    omega
  · have empty_out : (∅ : Finset (Fin 4)) ∉ F := fun H => hi _ H _ H (by simp)
    let G := F.image (fun a => aᶜ)
    have hcard : G.card = F.card := Finset.card_image_of_injective _ compl_injective
    have hd : Disjoint F G := Finset.disjoint_left.mpr (by
      rintro a ha hG
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hG
      exact hi _ hb _ ha disjoint_compl_right)
    have h0 : (∅ : Finset (Fin 4)) ∉ F ∪ G := by
      simp [G, empty_out, h]
    have hle := Finset.card_le_univ (insert (∅ : Finset (Fin 4)) (F ∪ G))
    rw [Finset.card_insert_of_notMem h0, Finset.card_union_of_disjoint hd, hcard] at hle
    norm_num at hle
    omega

end PetrTemperateIntersecting
