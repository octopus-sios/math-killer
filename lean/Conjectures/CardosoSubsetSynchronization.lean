import Mathlib

/-! The additive counting step in the weakly oriented circular case of Cardoso's
subset conjecture. A placement is counted at length `l` when its end is higher
than its start in the periodic prefix sum of the indegree discrepancy. -/

namespace CardosoSubsetSynchronization

open Finset
open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def rises (F : G → ℤ) (l : G) : ℕ :=
  (univ.filter fun x => F x < F (x + l)).card

def overlap (D : Finset G) (l : G) : ℕ :=
  (D.filter fun x => x + l ∈ D).card

omit [Fintype G] in
/-- Each ordered pair of distinct points pays for at most one shift. -/
theorem overlap_budget (D J : Finset G) (h0 : 0 ∉ J) :
    ∑ l ∈ J, overlap D l ≤ D.card * (D.card - 1) := by
  classical
  calc
    _ = ∑ x ∈ D, (J.filter fun l => x + l ∈ D).card := by
      simp only [overlap, card_filter]
      exact sum_comm
    _ ≤ ∑ _x ∈ D, (D.card - 1) := by
      apply sum_le_sum
      intro x hx
      rw [← card_erase_of_mem hx]
      apply card_le_card_of_injOn (x + ·) _ (add_right_injective x).injOn
      intro l hl
      obtain ⟨hlJ, hxl⟩ := mem_filter.mp hl
      refine mem_erase.mpr ⟨?_, hxl⟩
      intro he
      apply h0
      have : l = 0 := by simpa using he
      simpa [this] using hlJ
    _ = _ := by simp

/-- A cut can be used in either orientation: a translation sends as many
points across it in one direction as in the other. -/
theorem cut_step (F : G → ℤ) (D : Finset G) (l : G)
    (hcut : (∀ x ∈ D, ∀ y ∉ D, F x < F y) ∨
      (∀ x ∈ D, ∀ y ∉ D, F y < F x)) :
    D.card ≤ rises F l + overlap D l := by
  classical
  have hp := card_filter_add_card_filter_not (s := D) (fun x => x + l ∈ D)
  rcases hcut with lower | upper
  · have h : (D.filter fun x => x + l ∉ D).card ≤ rises F l := by
      apply card_le_card
      intro x hx
      obtain ⟨hx, hn⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_univ _, lower _ hx _ hn⟩
    unfold overlap
    omega
  · have hin : (D.filter fun y => y - l ∈ D).card = overlap D l := by
      apply card_bij (fun y _ => y-l)
      · intro y hy
        obtain ⟨hy, hd⟩ := mem_filter.mp hy
        exact mem_filter.mpr ⟨hd, by simpa using hy⟩
      · intro y hy z hz e
        exact sub_left_injective e
      · intro x hx
        obtain ⟨hx, hd⟩ := mem_filter.mp hx
        exact ⟨x+l, mem_filter.mpr ⟨hd, by simpa using hx⟩, by simp⟩
    have hn : (D.filter fun y => y - l ∉ D).card ≤ rises F l := by
      apply card_le_card_of_injOn (· - l) _ (sub_left_injective (b := l)).injOn
      intro y hy
      obtain ⟨hy, hd⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨mem_univ _, by simpa using upper y hy _ hd⟩
    have hp' := card_filter_add_card_filter_not (s := D) (fun y => y - l ∈ D)
    omega

/-- Aggregate growth estimate, uniform over all choices of stage shifts.
The boundary case `D.card = J.card` uses the additional short-gap argument
in the accompanying proof. -/
theorem aggregate_cut_rises (F : G → ℤ) (D J : Finset G)
    (h0 : 0 ∉ J) (hk : 2 ≤ D.card) (hd : D.card + 1 ≤ J.card)
    (hcut : (∀ x ∈ D, ∀ y ∉ D, F x < F y) ∨
      (∀ x ∈ D, ∀ y ∉ D, F y < F x)) :
    2 * J.card ≤ (∑ l ∈ J, rises F l) + 2 := by
  have H := sum_le_sum (s := J) (fun l _ => cut_step F D l hcut)
  rw [sum_add_distrib] at H
  simp only [sum_const, nsmul_eq_mul] at H
  have C := overlap_budget D J h0
  have h1 : D.card - 1 + 1 = D.card := by omega
  have h2 : D.card - 2 + 2 = D.card := by omega
  have h3 : J.card - (D.card + 1) + (D.card + 1) = J.card := by omega
  nlinarith [Nat.zero_le ((D.card - 2) * (J.card - (D.card + 1))),
    congrArg (D.card * ·) h1, congrArg (· * J.card) h2,
    congrArg ((D.card - 2) * ·) h3, congrArg (· * D.card) h2]

private theorem extrema_rises (F : G → ℤ) (J : Finset G) (h0 : 0 ∉ J)
    (u v : G) (hu : ∀ x, x ≠ u → F u < F x)
    (hv : ∀ x, x ≠ v → F x < F v) :
    2 * J.card ≤ (∑ l ∈ J, rises F l) + 1 := by
  classical
  have hsum := sum_le_sum (s := J)
    (g := fun l => rises F l + (if l = v-u then 1 else 0))
    (f := fun _ => 2) (by
      intro l hl
      have hn : l ≠ 0 := fun e => h0 (e ▸ hl)
      have hu' : u ∈ univ.filter (fun x => F x < F (x+l)) :=
        mem_filter.mpr ⟨mem_univ _, hu _ (by simpa using hn)⟩
      by_cases h : l = v-u
      · simp only [h, ite_true]
        have H := card_pos.mpr ⟨u,h ▸ hu'⟩
        unfold rises
        omega
      · simp [h]
        apply one_lt_card.mpr
        refine ⟨u, hu', v-l, mem_filter.mpr ⟨mem_univ _, ?_⟩, ?_⟩
        · simpa using hv (v-l) (by simpa using hn)
        · intro e
          apply h
          rw [eq_sub_iff_add_eq]
          rw [e]
          abel)
  simp [sum_add_distrib] at hsum
  split_ifs at hsum <;> omega

private def lower (F : G → ℤ) (t : ℤ) := univ.filter fun x => F x < t
private def upper (F : G → ℤ) (t : ℤ) := univ.filter fun x => t ≤ F x

omit [AddCommGroup G] [DecidableEq G] in
private theorem ordered_drops (F : G → ℤ) (x y a b : G)
    (hxy : x ≠ y) (hab : a ≠ b) (hx : F a < F x) (hy : F b < F y)
    (h : F x ≤ F y)
    (hn : ¬∃ t, 2 ≤ (lower F t).card ∧ 2 ≤ (upper F t).card) :
    ∃ u v, (∀ i, i ≠ u → F u < F i) ∧ (∀ i, i ≠ v → F i < F v) := by
  refine ⟨a, y, ?_, ?_⟩
  · intro i hi
    by_contra! hf
    apply hn
    refine ⟨F x, one_lt_card.mpr ⟨i, ?_, a, ?_, hi⟩,
      one_lt_card.mpr ⟨x, ?_, y, ?_, hxy⟩⟩ <;>
      simp_all [lower, upper, lt_of_le_of_lt hf hx]
  · intro i hi
    by_contra! hf
    apply hn
    refine ⟨F y, one_lt_card.mpr ⟨a, ?_, b, ?_, hab⟩,
      one_lt_card.mpr ⟨i, ?_, y, ?_, hi⟩⟩ <;>
      simp_all [lower, upper, lt_of_lt_of_le hx h]

/-- Two distinct descents of the same shift force aggregate growth.
No cut, symmetry of the height function, or per-shift lower bound is assumed. -/
theorem aggregate_rises_of_descents (F : G → ℤ) (s : G) (J : Finset G)
    (h0 : 0 ∉ J) (hd : Fintype.card G / 2 + 1 ≤ J.card)
    (hdesc : 2 ≤ (univ.filter fun x => F (x+s) < F x).card) :
    2 * J.card ≤ (∑ l ∈ J, rises F l) + 2 := by
  classical
  by_cases hb : ∃ t, 2 ≤ (lower F t).card ∧ 2 ≤ (upper F t).card
  · obtain ⟨t,hlo,hhi⟩ := hb
    have htot : (lower F t).card + (upper F t).card = Fintype.card G := by
      simpa [lower, upper, not_lt] using
        (card_filter_add_card_filter_not (s := (univ : Finset G)) (fun x => F x < t))
    by_cases hsmall : (lower F t).card ≤ Fintype.card G / 2
    · apply aggregate_cut_rises F (lower F t) J h0 hlo (by omega)
      left
      intro x hx y hy
      simp [lower] at hx hy
      omega
    · apply aggregate_cut_rises F (upper F t) J h0 hhi (by omega)
      right
      intro x hx y hy
      simp [upper] at hx hy
      omega
  · obtain ⟨x, hx, y, hy, hxy⟩ := one_lt_card.mp hdesc
    have hx' := (mem_filter.mp hx).2
    have hy' := (mem_filter.mp hy).2
    have he : x+s ≠ y+s := fun e => hxy (add_right_cancel e)
    have hm : ∃ u v, (∀ i, i ≠ u → F u < F i) ∧ (∀ i, i ≠ v → F i < F v) := by
      rcases le_total (F x) (F y) with h | h
      · exact ordered_drops _ _ _ _ _ hxy he hx' hy' h hb
      · exact ordered_drops _ _ _ _ _ hxy.symm he.symm hy' hx' h hb
    obtain ⟨u,v,hu,hv⟩ := hm
    have H := extrema_rises F J h0 u v hu hv
    omega

/-- Integral form of the conjectured bound for nonempty subsets. -/
def bound (n m : ℕ) : ℤ :=
  let g : ℤ := ((n-1)/m : ℕ)
  ((n:ℤ)-1)^2 - g*(2*n-m*(g+1)-1)

/-- The credits from the aggregate estimate buy Cardoso's exact ceilings,
with at least `m-3` letters left over. -/
theorem closing_budget (n m : ℕ) (hm : 3 ≤ m) (hmn : m ≤ n) :
    let g : ℤ := ((n-1)/m : ℕ)
    2 + ((n:ℤ)-1)*(n-g-2) + m*g + ((m:ℤ)-3) ≤ bound n m := by
  dsimp [bound]
  let g := (n-1)/m
  let e := (n-1)%m+1
  have hm0 : 0 < m := by omega
  have he : e ≤ m := by
    dsimp [e]
    have := Nat.mod_lt (n-1) hm0
    omega
  have hdecomp : n = m*g+e := by
    dsimp [g,e]
    have := Nat.mod_add_div (n-1) m
    omega
  have heq : (n:ℤ) = (m:ℤ)*g+e := by exact_mod_cast hdecomp
  change 2 + ((n:ℤ)-1)*(n-(g:ℤ)-2) + m*g + ((m:ℤ)-3) ≤
    ((n:ℤ)-1)^2 - (g:ℤ)*(2*n-m*(g+1)-1)
  have he' : (e:ℤ) ≤ m := by exact_mod_cast he
  by_cases hg : g = 0
  · have hne : n = e := by simpa [hg] using hdecomp
    have hem : e = m := by omega
    have hnm : n = m := by omega
    rw [hg, hnm]
    push_cast
    nlinarith
  · have hgn : 1 ≤ g := Nat.pos_of_ne_zero hg
    have hg' : 1 ≤ (g:ℤ) := by exact_mod_cast hgn
    rw [heq]
    nlinarith [mul_nonneg (sub_nonneg.mpr hg') (sub_nonneg.mpr he')]

/-- Starting from a set of possible positions saves one step for each
additional initial position. This only needs transitivity of the forward orbit. -/
theorem steer {X : Type*} [Fintype X] [DecidableEq X] (f : X → X)
    (ht : ∀ x y, ∃ t : ℕ, f^[t] x = y) (A B : Finset X)
    (ha : A.Nonempty) (hb : B.Nonempty) :
    ∃ x ∈ A, ∃ t ≤ Fintype.card X + 1 - (A.card + B.card), f^[t] x ∈ B := by
  classical
  let R (t : ℕ) := univ.filter (fun y => ∃ x ∈ A, ∃ j ≤ t, f^[j] x = y)
  have memR (t : ℕ) (y : X) :
      y ∈ R t ↔ ∃ x ∈ A, ∃ j ≤ t, f^[j] x = y := by simp [R]
  have inc (t) : R t ⊆ R (t+1) := by
    intro y hy
    obtain ⟨x,hx,j,hj,e⟩ := (memR ..).mp hy
    exact (memR ..).mpr ⟨x,hx,j,by omega,e⟩
  have hin (t) : A ⊆ R t := by
    intro y hy
    exact (memR ..).mpr ⟨y,hy,0,Nat.zero_le _,rfl⟩
  have grows (t) (hne : R t ≠ univ) : (R t).card < (R (t+1)).card := by
    apply card_lt_card
    refine ssubset_of_subset_of_ne (inc t) ?_
    intro e
    obtain ⟨x,hx⟩ := ha
    apply hne
    apply eq_univ_of_forall
    intro y
    obtain ⟨j,rfl⟩ := ht x y
    induction j with
    | zero => exact hin t hx
    | succ j ih =>
      obtain ⟨s,hs,k,hk,hiter⟩ := (memR ..).mp ih
      rw [e]
      apply (memR ..).mpr
      refine ⟨s,hs,k+1,by omega,?_⟩
      simp [Function.iterate_succ_apply', hiter]
  have amount (t : ℕ) : min (Fintype.card X) (A.card+t) ≤ (R t).card := by
    induction t with
    | zero => simpa using (min_le_right _ _).trans (card_le_card (hin 0))
    | succ t ih =>
      by_cases h : R t = univ
      · have h' : R (t+1) = univ := by
          apply eq_univ_of_forall
          intro x
          exact inc t (by simp [h])
        simp [h']
      · have hg := grows t h
        omega
  let t := Fintype.card X + 1 - (A.card+B.card)
  have hnon : ((R t) ∩ B).Nonempty := by
    by_contra! h
    have hdis : Disjoint (R t) B := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      simpa [Finset.not_nonempty_iff_eq_empty] using h
    have H := (Finset.card_le_univ ((R t) ∪ B))
    rw [card_union_of_disjoint hdis] at H
    have hB := Finset.card_pos.mpr hb
    have hR := amount t
    dsimp [t] at *
    omega
  obtain ⟨y,hy⟩ := hnon
  obtain ⟨hr,htarget⟩ := mem_inter.mp hy
  obtain ⟨x,ha',j,hj,he⟩ := (memR ..).mp hr
  exact ⟨x,ha',j,hj,he.symm ▸ htarget⟩

end CardosoSubsetSynchronization
