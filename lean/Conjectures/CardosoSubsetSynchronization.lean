import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-! Words are read from left to right. The cyclic order on the states is the
standard order modulo `n`; the distinguished circular letter is not required
to be the successor in that order. -/

namespace CardosoSubsetSynchronization

open Finset

/-- An arbitrary alphabet and one total transition for each letter. -/
structure Automaton (n : ℕ) (α : Type*) where
  δ : α → ZMod n → ZMod n

variable {n : ℕ} {α : Type*}

namespace Automaton

def act (A : Automaton n α) : List α → ZMod n → ZMod n
  | [], p => p
  | a :: w, p => A.act w (A.δ a p)

@[simp] theorem act_nil (A : Automaton n α) (p : ZMod n) : A.act [] p = p := rfl

@[simp] theorem act_cons (A : Automaton n α) (a : α) (w : List α) (p : ZMod n) :
    A.act (a :: w) p = A.act w (A.δ a p) := rfl

theorem act_append (A : Automaton n α) (u v : List α) (p : ZMod n) :
    A.act (u ++ v) p = A.act v (A.act u p) := by
  induction u generalizing p with
  | nil => rfl
  | cons x u ih => exact ih _

theorem act_replicate (A : Automaton n α) (a : α) (k : ℕ) (p : ZMod n) :
    A.act (List.replicate k a) p = (A.δ a)^[k] p := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih => simpa [List.replicate_succ, Function.iterate_succ_apply] using ih (A.δ a p)

def Synchronizes (A : Automaton n α) (w : List α) (S : Finset (ZMod n)) : Prop :=
  ∃ q, ∀ p ∈ S, A.act w p = q

def Synchronizing (A : Automaton n α) : Prop :=
  ∃ w q, ∀ p, A.act w p = q

/-- Transitivity of the powers of a permutation. This includes a one-state
cycle and does not prescribe the jump in the standard cyclic order. -/
def Circular (A : Automaton n α) : Prop :=
  ∃ a : α, ∃ π : Equiv.Perm (ZMod n), A.δ a = π ∧
    ∀ p q, ∃ k : ℕ, (π : ZMod n → ZMod n)^[k] p = q

end Automaton

/-- The `l` consecutive points beginning at `i`. -/
def interval (i : ZMod n) (l : ℕ) : Finset (ZMod n) :=
  (range l).image fun (k : ℕ) => i + (k : ZMod n)

@[simp] theorem mem_interval {i p : ZMod n} {l : ℕ} :
    p ∈ interval i l ↔ ∃ k < l, i + (k : ZMod n) = p := by simp [interval]

@[simp] theorem interval_one (i : ZMod n) : interval i 1 = {i} := by
  ext p
  simp [interval]

theorem interval_mono (i : ZMod n) {k l : ℕ} (h : k ≤ l) :
    interval i k ⊆ interval i l := by
  intro p hp
  obtain ⟨j,hj,rfl⟩ := mem_interval.mp hp
  exact mem_interval.mpr ⟨j,by omega,rfl⟩

theorem natCast_inj_lt [NeZero n] {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : (a : ZMod n) = (b : ZMod n)) : a = b := by
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using congrArg ZMod.val h

theorem interval_card [NeZero n] (i : ZMod n) {l : ℕ} (hl : l ≤ n) :
    (interval i l).card = l := by
  rw [interval, card_image_of_injOn, card_range]
  intro a ha b hb e
  exact natCast_inj_lt (lt_of_lt_of_le (mem_range.mp ha) hl)
    (lt_of_lt_of_le (mem_range.mp hb) hl) (add_left_cancel e)

@[simp] theorem interval_full [NeZero n] (i : ZMod n) : interval i n = univ := by
  apply eq_univ_of_card
  simpa [ZMod.card] using interval_card i (le_refl n)

def pre [NeZero n] (f : ZMod n → ZMod n) (T : Finset (ZMod n)) : Finset (ZMod n) :=
  univ.filter fun x => f x ∈ T

@[simp] theorem mem_pre [NeZero n] {p : ZMod n} {f : ZMod n → ZMod n} {T} :
    p ∈ pre f T ↔ f p ∈ T := by simp [pre]

def Automaton.WeaklyOriented [NeZero n] (A : Automaton n α) : Prop :=
  ∀ a i l, l ≤ n → ∃ j k, k ≤ n ∧ pre (A.δ a) (interval i l) = interval j k

/-- For a nonempty subset, the quotient in this formula is
`ceil(n / m) - 1` (equivalently, `floor((n-1)/m)`). -/
def B (n m : ℕ) : ℕ :=
  let g := (n - 1) / m
  (n - 1)^2 - g * (2*n - m*(g+1) - 1)

theorem ceiling_eq {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (n + m - 1) / m = (n-1)/m + 1 := by
  rw [show n+m-1 = (n-1)+m by omega, Nat.add_div_right _ hm]

theorem ceiling_product_le {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    m * ((n-1)/m+1) + 1 ≤ 2*n := by
  have H := Nat.div_mul_le_self (n-1) m
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm m]
  omega

@[simp] theorem B_singleton {n : ℕ} (hn : 0 < n) : B n 1 = 0 := by
  simp only [B, Nat.div_one, Nat.one_mul]
  rw [show 2*n - (n-1+1) - 1 = n-1 by omega, pow_two, Nat.sub_self]

@[simp] theorem B_full {n : ℕ} (hn : 0 < n) : B n n = (n-1)^2 := by
  simp [B, Nat.div_eq_of_lt (show n-1 < n by omega)]

theorem B_two {n : ℕ} (hn : 2 ≤ n) : B n 2 = n.choose 2 := by
  rw [Nat.choose_two_right]
  suffices h : 2 * B n 2 = n * (n-1) by omega
  obtain ⟨k,h | h⟩ : ∃ k, n = 2*k+1 ∨ n = 2*k+2 := by
    exact ⟨(n-1)/2, by omega⟩
  · rw [h]
    simp only [B, show 2*k+1-1 = 2*k by omega, show 2*k/2 = k by omega,
      show 2*(2*k+1)-2*(k+1)-1 = 2*k-1 by omega]
    have hk : 1 ≤ k := by omega
    have hs : 2*k-1+1 = 2*k := by omega
    have hh : k*(2*k-1) ≤ (2*k)^2 := by nlinarith [Nat.mul_le_mul_left k (Nat.sub_le (2*k) 1)]
    nlinarith [Nat.sub_add_cancel hh, congrArg (k * ·) hs]
  · rw [h]
    simp only [B, show 2*k+2-1 = 2*k+1 by omega, show (2*k+1)/2 = k by omega,
      show 2*(2*k+2)-2*(k+1)-1 = 2*k+1 by omega]
    have hh : k*(2*k+1) ≤ (2*k+1)^2 := by nlinarith
    nlinarith [Nat.sub_add_cancel hh]

namespace Automaton

theorem Synchronizes.mono {A : Automaton n α} {w : List α} {S T : Finset (ZMod n)}
    (hw : A.Synchronizes w T) (h : S ⊆ T) : A.Synchronizes w S := by
  obtain ⟨q,hq⟩ := hw
  exact ⟨q,fun _ hp => hq _ (h hp)⟩

theorem emptyWord_of_card_one (A : Automaton n α) (S : Finset (ZMod n)) (hS : S.card = 1) :
    A.Synchronizes [] S := by
  obtain ⟨p,rfl⟩ := card_eq_one.mp hS
  exact ⟨p,by simp⟩

/-- This two-state-subset case does not need a circular letter or an order:
the uncollapsed images form a path among unordered pairs. -/
theorem pair_bound [NeZero n] (A : Automaton n α) (hs : A.Synchronizing)
    (S : Finset (ZMod n)) (hS : S.card = 2) :
    ∃ w, w.length ≤ B n 2 ∧ A.Synchronizes w S := by
  classical
  let pairs := (univ : Finset (ZMod n)).powersetCard 2
  have memPairs (T : Finset (ZMod n)) : T ∈ pairs ↔ T.card = 2 := by simp [pairs]
  let R (t : ℕ) := pairs.filter fun T => ∃ w : List α, w.length ≤ t ∧ A.Synchronizes w T
  have memR (T : Finset (ZMod n)) (t : ℕ) : T ∈ R t ↔
      T.card = 2 ∧ ∃ w : List α, w.length ≤ t ∧ A.Synchronizes w T := by simp [R,memPairs]
  have inc (t : ℕ) : R t ⊆ R (t+1) := by
    intro T hT
    obtain ⟨h2,w,hw,hsw⟩ := (memR ..).mp hT
    exact (memR ..).mpr ⟨h2,w,by omega,hsw⟩
  have sat (t : ℕ) (eq : R t = R (t+1)) : R t = pairs := by
    apply Subset.antisymm (filter_subset _ _)
    intro T hT
    have h2 := (memPairs T).mp hT
    obtain ⟨v,q,hq⟩ := hs
    have hv : A.Synchronizes v T := ⟨q,fun p _ => hq p⟩
    clear hT hq
    induction v generalizing T with
    | nil => exact (memR ..).mpr ⟨h2,[],by simp,hv⟩
    | cons a v ih =>
      let U := T.image (A.δ a)
      have hu : U.card ≤ 2 := (card_image_le).trans h2.le
      have hpos : 0 < U.card := card_pos.mpr
        ((card_pos.mp (show 0 < T.card by omega)).image _)
      have hshort : ∃ w : List α, w.length ≤ t ∧ A.Synchronizes w U := by
        by_cases hu2 : U.card = 2
        · apply ((memR U t).mp (ih (T := U) hu2 ?_)).2
          obtain ⟨z,hz⟩ := hv
          refine ⟨z,?_⟩
          intro p hp
          obtain ⟨s,hs',rfl⟩ := mem_image.mp hp
          exact hz _ hs'
        · exact ⟨[],by simp,A.emptyWord_of_card_one U (by omega)⟩
      obtain ⟨w,hw,z,hz⟩ := hshort
      change T ∈ R t
      rw [eq]
      refine (memR ..).mpr ⟨h2,a::w,by simp only [List.length_cons]; omega,z,?_⟩
      intro p hp
      exact hz _ (mem_image_of_mem _ hp)
  have low (t : ℕ) : min pairs.card t ≤ (R t).card := by
    induction t with
    | zero => simp
    | succ t ih =>
      by_cases h : R t = R (t+1)
      · have eq := sat t h
        rw [← h, eq]
        exact min_le_left _ _
      · have := card_lt_card (ssubset_of_subset_of_ne (inc t) h)
        omega
  have hfull : R pairs.card = pairs := eq_of_subset_of_card_le (filter_subset _ _)
    (by simpa using low pairs.card)
  obtain ⟨_,w,hw,hsw⟩ := (memR S _).mp (hfull ▸ (memPairs S).mpr hS)
  have h2n := card_le_univ S
  rw [hS, ZMod.card] at h2n
  exact ⟨w,by simpa [pairs, ZMod.card, B_two h2n] using hw,hsw⟩

end Automaton

end CardosoSubsetSynchronization

namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n] {α : Type*}

@[simp] theorem interval_two (i : ZMod n) : interval i 2 = {i, i+1} := by
  ext p
  simp [interval, show 2 = 1+1 by decide, range_add_one, or_comm]

theorem starts_card (q : ZMod n) {l : ℕ} (hl : l ≤ n) :
    (univ.filter (fun i => q ∈ interval i l)).card = l := by
  have eq : univ.filter (fun i => q ∈ interval i l) =
      (range l).image (fun (k : ℕ) => q - (k : ZMod n)) := by
    ext i
    simp only [mem_filter, mem_univ, true_and, mem_interval, mem_image, mem_range]
    constructor
    · rintro ⟨k,hk,e⟩
      exact ⟨k,hk,by rw [← e]; abel⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨k,hk,by abel⟩
  rw [eq, card_image_of_injOn, card_range]
  intro a ha b hb h
  apply natCast_inj_lt (lt_of_lt_of_le (mem_range.mp ha) hl)
    (lt_of_lt_of_le (mem_range.mp hb) hl)
  exact sub_right_injective h

theorem pre_perm (π : Equiv.Perm (ZMod n)) (T : Finset (ZMod n)) :
    pre π T = T.image π.symm := by
  ext x
  simp only [mem_pre, mem_image]
  constructor
  · intro h
    exact ⟨π x,h,π.symm_apply_apply x⟩
  · rintro ⟨q,hq,rfl⟩
    simpa using hq

theorem pre_total (f : ZMod n → ZMod n) {l : ℕ} (hl : l ≤ n) :
    ∑ i : ZMod n, (pre f (interval i l)).card = n*l := by
  calc
    _ = ∑ p : ZMod n, (univ.filter (fun i => f p ∈ interval i l)).card := by
      simp only [pre, card_filter]
      exact sum_comm
    _ = ∑ _p : ZMod n, l := sum_congr rfl (fun p _ => starts_card (f p) hl)
    _ = n*l := by simp [ZMod.card]

namespace Automaton

/-- If no letter increased an interval at this length, the average shows
that every one of their preimages would have the same length. This property
propagates backwards through an entire word, contradicting a reset. -/
theorem exists_growing (A : Automaton n α) (ho : A.WeaklyOriented) (hs : A.Synchronizing)
    {l : ℕ} (hpos : 0 < l) (hlt : l < n) :
    ∃ a i, l < (pre (A.δ a) (interval i l)).card := by
  classical
  by_contra! h
  have heq (a : α) (i : ZMod n) : (pre (A.δ a) (interval i l)).card = l := by
    have hle := h a i
    by_contra hn
    have hlt' : (∑ j : ZMod n, (pre (A.δ a) (interval j l)).card) <
        ∑ _j : ZMod n, l := sum_lt_sum (fun j _ => h a j) ⟨i,mem_univ _,by omega⟩
    simpa [pre_total _ hlt.le, ZMod.card] using hlt'
  have step (a : α) (i : ZMod n) : ∃ j, pre (A.δ a) (interval i l) = interval j l := by
    obtain ⟨j,k,hk,e⟩ := ho a i l hlt.le
    have hp := heq a i
    rw [e, interval_card j hk] at hp
    exact ⟨j,hp ▸ e⟩
  have word (w : List α) (i : ZMod n) : ∃ j, pre (A.act w) (interval i l) = interval j l := by
    induction w generalizing i with
    | nil => exact ⟨i,by ext p; simp⟩
    | cons a w ih =>
      obtain ⟨k,hk⟩ := ih i
      obtain ⟨j,hj⟩ := step a k
      refine ⟨j,?_⟩
      rw [← hj]
      ext p
      simp only [mem_pre,act_cons]
      rw [← hk, mem_pre]
  obtain ⟨w,q,hq⟩ := hs
  have hmem : q ∈ interval q l := mem_interval.mpr ⟨0,hpos,by simp⟩
  have hw : pre (A.act w) (interval q l) = univ := eq_univ_of_forall (fun p =>
    mem_pre.mpr (by simpa [hq] using hmem))
  obtain ⟨j,hj⟩ := word w q
  rw [hw] at hj
  have H := congrArg Finset.card hj
  rw [interval_card j hlt.le, card_univ, ZMod.card] at H
  omega

/-- A transitive permutation respecting the interval order is a rotation.
For three or more states, successive steps of its inverse must have the
same sign, and an affine reflection has no orbit of size three. -/
theorem circular_rotation (A : Automaton n α) (hc : A.Circular) (ho : A.WeaklyOriented)
    (hn : 3 ≤ n) :
    ∃ a j, (∀ x, A.δ a x = x+j) ∧
      ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y := by
  obtain ⟨a,π,ha,ht⟩ := hc
  have one_ne : (1 : ZMod n) ≠ 0 := by
    intro e
    have h : ((1 : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by simpa using e
    have := natCast_inj_lt (n := n) (by omega : 1 < n) (by omega : 0 < n) h
    omega
  have two_ne : (1 : ZMod n) + 1 ≠ 0 := by
    intro e
    have h : ((2 : ℕ) : ZMod n) = ((0 : ℕ) : ZMod n) := by simpa only [Nat.cast_ofNat, Nat.cast_zero, one_add_one_eq_two] using e
    have := natCast_inj_lt (n := n) (by omega : 2 < n) (by omega : 0 < n) h
    omega
  have step (x : ZMod n) : π.symm (x+1) = π.symm x + 1 ∨ π.symm (x+1) = π.symm x - 1 := by
    obtain ⟨s,k,hk,h⟩ := ho a x 2 (by omega)
    rw [ha,pre_perm] at h
    have hlen := congrArg Finset.card h
    rw [card_image_of_injective _ π.symm.injective,interval_card x (by omega),
      interval_card s hk] at hlen
    subst k
    rw [interval_two,interval_two] at h
    have h1 : π.symm x ∈ ({s,s+1} : Finset _) := h ▸ mem_image_of_mem _ (by simp)
    have h2 : π.symm (x+1) ∈ ({s,s+1} : Finset _) := h ▸ mem_image_of_mem _ (by simp)
    have ne : π.symm (x+1) ≠ π.symm x := by
      intro eq
      exact one_ne (by simpa using π.symm.injective eq)
    simp only [mem_insert,mem_singleton] at h1 h2
    rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;> simp_all
  obtain ⟨d,hd,h0⟩ : ∃ d : ZMod n, (d = 1 ∨ d = -1) ∧
      π.symm (0+1) = π.symm 0 + d := by
    rcases step 0 with h|h
    · exact ⟨1,Or.inl rfl,h⟩
    · exact ⟨-1,Or.inr rfl,by simpa [sub_eq_add_neg] using h⟩
  have hstepNat (k : ℕ) : π.symm ((k : ZMod n)+1) = π.symm k + d := by
    induction k with
    | zero => simpa using h0
    | succ k ih =>
      simp only [Nat.cast_succ]
      have no : π.symm ((k : ZMod n)+1+1) ≠ π.symm k := by
        intro e
        exact two_ne (by simpa [add_assoc] using π.symm.injective e)
      rcases hd with rfl|rfl <;> rcases step ((k : ZMod n)+1) with h|h <;>
        simp_all [sub_eq_add_neg,add_assoc]
  have affNat (k : ℕ) : π.symm k = π.symm 0 + (k : ZMod n) * d := by
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ,hstepNat,ih,add_mul,one_mul,add_assoc]
  have aff (x : ZMod n) : π.symm x = π.symm 0 + x*d := by simpa using affNat x.val
  rcases hd with rfl|rfl
  · let j := -π.symm 0
    have rot (p : ZMod n) : π p = p+j := by
      have h := aff (π p)
      simp only [Equiv.symm_apply_apply,mul_one] at h
      dsimp [j]
      conv_rhs => lhs; rw [h]
      abel
    refine ⟨a,j,fun p => by rw [ha]; exact rot p,?_⟩
    intro x y
    obtain ⟨k,hk⟩ := ht y x
    have cancel (m : ℕ) (z : ZMod n) :
        (fun p : ZMod n => p-j)^[m] ((π : ZMod n → ZMod n)^[m] z) = z := by
      induction m with
      | zero => rfl
      | succ m ih =>
        rw [Function.iterate_succ_apply,Function.iterate_succ_apply' (f := (π : ZMod n → ZMod n))]
        simpa [rot] using ih
    exact ⟨k,hk ▸ cancel k y⟩
  · exfalso
    let c := π.symm 0
    have refl' (p : ZMod n) : π p = c-p := by
      have h := aff (π p)
      simp only [Equiv.symm_apply_apply,mul_neg,mul_one] at h
      dsimp [c]
      conv_rhs => rhs; rw [h]
      abel
    have small (k : ℕ) : (π : ZMod n → ZMod n)^[k] 0 ∈ ({0,c} : Finset _) := by
      induction k with
      | zero => simp
      | succ k ih =>
        rw [Function.iterate_succ_apply',refl']
        simp only [mem_insert,mem_singleton] at ih ⊢
        rcases ih with h|h <;> simp [h]
    have allmem : (univ : Finset (ZMod n)) ⊆ {0,c} := by
      intro p _
      obtain ⟨k,rfl⟩ := ht 0 p
      exact small k
    have H := card_le_card allmem
    have E := card_insert_le 0 ({c} : Finset _)
    simp only [card_univ, ZMod.card, card_singleton] at H E
    omega

end Automaton
end CardosoSubsetSynchronization

namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n]

def fibre (f : ZMod n → ZMod n) (q : ZMod n) : ℕ := (pre f {q}).card

def height (f : ZMod n → ZMod n) (i : ZMod n) : ℤ :=
  ∑ k ∈ range i.val, ((fibre f (k : ZMod n) : ℤ) - 1)

private theorem sum_residues {M : Type*} [AddCommMonoid M] (g : ZMod n → M) :
    ∑ k ∈ range n, g k = ∑ i : ZMod n, g i := by
  apply sum_bij (fun (k : ℕ) _ => (k : ZMod n))
  · simp
  · intro x hx y hy e
    exact natCast_inj_lt (mem_range.mp hx) (mem_range.mp hy) e
  · intro i _
    exact ⟨i.val,mem_range.mpr i.val_lt,by simp⟩
  · simp

private theorem discrepancy_sum (f : ZMod n → ZMod n) :
    ∑ k ∈ range n, ((fibre f (k : ZMod n) : ℤ) - 1) = 0 := by
  have hn : 1 ≤ n := NeZero.pos n
  have H : ∑ i : ZMod n, fibre f i = n := by
    simpa [fibre] using pre_total f (l := 1) hn
  rw [sum_residues (fun i => (fibre f i : ℤ) - 1),sum_sub_distrib]
  simp [← Nat.cast_sum,H,ZMod.card]

theorem height_step (f : ZMod n → ZMod n) (i : ZMod n) :
    height f (i+1) = height f i + ((fibre f i : ℤ)-1) := by
  have Hv := i.val_lt
  have castSucc : ((i.val+1 : ℕ) : ZMod n) = i+1 := by simp
  by_cases h : i.val + 1 < n
  · have V : (i+1).val = i.val+1 := by
      rw [← castSucc, ZMod.val_natCast, Nat.mod_eq_of_lt h]
    simp only [height,V,sum_range_succ,ZMod.natCast_zmod_val]
  · have e : i.val+1 = n := by omega
    have wrap : i+1 = 0 := by rw [← castSucc,e]; simp
    have eq : ∑ k ∈ range (i.val+1), ((fibre f k : ℤ)-1) = 0 := by
      rw [e]; exact discrepancy_sum f
    rw [sum_range_succ] at eq
    simp only [ZMod.natCast_zmod_val] at eq
    rw [wrap]
    simpa [height] using eq.symm

theorem pre_succ_card (f : ZMod n → ZMod n) (i : ZMod n) {l : ℕ} (hl : l < n) :
    (pre f (interval i (l+1))).card = (pre f (interval i l)).card + fibre f (i+l) := by
  have notmem : i + (l : ZMod n) ∉ interval i l := by
    intro h
    obtain ⟨k,hk,e⟩ := mem_interval.mp h
    have := natCast_inj_lt (hk.trans hl) hl (add_left_cancel e)
    omega
  have eq : pre f (interval i (l+1)) = pre f (interval i l) ∪ pre f {i+l} := by
    ext p
    simp only [mem_pre,mem_union,mem_singleton,interval,range_add_one,image_insert,mem_insert]
    tauto
  rw [eq, card_union_of_disjoint]
  · rfl
  · rw [Finset.disjoint_left]
    intro p h1 h2
    have h := mem_pre.mp h1
    have e : f p = i+l := by simpa using h2
    exact notmem (e ▸ h)

theorem pre_card_height (f : ZMod n → ZMod n) (i : ZMod n) {l : ℕ} (hl : l ≤ n) :
    ((pre f (interval i l)).card : ℤ) = l + height f (i+l) - height f i := by
  induction l with
  | zero => simp [pre,interval]
  | succ l ih =>
    rw [pre_succ_card f i (by omega),Nat.cast_add, ih (by omega),Nat.cast_succ,
      Nat.cast_succ,← add_assoc,height_step]
    omega

theorem height_descents (f : ZMod n → ZMod n) :
    (univ.filter (fun i : ZMod n => height f (i+1) < height f i)).card =
      n - (univ.image f).card := by
  classical
  have eq : (univ.filter (fun i : ZMod n => height f (i+1) < height f i)) =
      univ \ univ.image f := by
    ext i
    simp only [mem_filter,mem_sdiff,mem_univ,true_and,height_step]
    have hz : fibre f i = 0 ↔ i ∉ univ.image f := by
      simp [fibre,pre,Finset.filter_eq_empty_iff,mem_image]
    rw [← hz]
    omega
  rw [eq,card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card]

end CardosoSubsetSynchronization

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

namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n] {α : Type*}

namespace Automaton

/-- Positions of length-`l` arcs for which an actual short synchronizing word
exists. Reaching one of these positions by backward rotation costs one copy
of the circular letter per step. -/
noncomputable def ready (A : Automaton n α) (l t : ℕ) : Finset (ZMod n) := by
  classical exact univ.filter fun i => ∃ w : List α, w.length ≤ t ∧ A.Synchronizes w (interval i l)

theorem mem_ready (A : Automaton n α) {i : ZMod n} {l t : ℕ} :
    i ∈ A.ready l t ↔ ∃ w : List α, w.length ≤ t ∧ A.Synchronizes w (interval i l) := by
  classical simp [ready]

def growing (A : Automaton n α) (b : α) (l : ℕ) : Finset (ZMod n) :=
  univ.filter fun i => l < (pre (A.δ b) (interval i l)).card

theorem ready_mono (A : Automaton n α) {t u l : ℕ} (h : t ≤ u) : A.ready l t ⊆ A.ready l u := by
  intro i hi
  obtain ⟨w,hw,hS⟩ := A.mem_ready.mp hi
  exact A.mem_ready.mpr ⟨w,hw.trans h,hS⟩

theorem ready_rotate (A : Automaton n α) {a : α} {j : ZMod n} (hr : ∀ x, A.δ a x = x+j)
    {i : ZMod n} {l u : ℕ} (hi : i ∈ A.ready l u) (k : ℕ) :
    (fun x : ZMod n => x-j)^[k] i ∈ A.ready l (u+k) := by
  induction k with
  | zero => simpa using hi
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨w,hw,q,hq⟩ := A.mem_ready.mp ih
    refine A.mem_ready.mpr ⟨a::w,by simp only [List.length_cons]; omega,q,?_⟩
    intro p hp
    obtain ⟨v,hv,rfl⟩ := mem_interval.mp hp
    apply hq
    apply mem_interval.mpr
    exact ⟨v,hv,by rw [hr]; abel⟩

theorem ready_prepend (A : Automaton n α) (ho : A.WeaklyOriented)
    {l t : ℕ} (hl : l ≤ n) {i : ZMod n} {b : α}
    (hi : i ∈ A.ready l t) (hg : i ∈ A.growing b l) :
    (A.ready (l+1) (t+1)).Nonempty := by
  obtain ⟨w,hw,q,hq⟩ := A.mem_ready.mp hi
  obtain ⟨s,k,hk,e⟩ := ho b i l hl
  have big := (mem_filter.mp hg).2
  rw [e, interval_card s hk] at big
  refine ⟨s,A.mem_ready.mpr ⟨b::w,by simp only [List.length_cons]; omega,q,?_⟩⟩
  intro p hp
  apply hq
  apply mem_pre.mp
  rw [e]
  exact interval_mono _ big hp

theorem grow_stage (A : Automaton n α) (ho : A.WeaklyOriented)
    {a b : α} {j : ZMod n} (hr : ∀ x, A.δ a x = x+j)
    (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    {l t : ℕ} (hl : l ≤ n) (hR : (A.ready l t).Nonempty)
    (hE : (A.growing b l).Nonempty) :
    (A.ready (l+1) (t + (n+1 - ((A.ready l t).card + (A.growing b l).card)) + 1)).Nonempty := by
  obtain ⟨i,hi,k,hk,hg⟩ := steer _ ht _ _ hR hE
  rw [ZMod.card] at hk
  obtain ⟨s,hs⟩ := A.ready_prepend ho hl (A.ready_rotate hr hi k) hg
  exact ⟨s,A.ready_mono (by omega) hs⟩

theorem seed (A : Automaton n α) (ho : A.WeaklyOriented) (hs : A.Synchronizing)
    (hn : 2 ≤ n) : (A.ready 2 1).Nonempty := by
  obtain ⟨b,i,hg⟩ := A.exists_growing ho hs (l := 1) (by decide) (by omega)
  have hi : i ∈ A.ready 1 0 := A.mem_ready.mpr ⟨[],by simp,i,by simp⟩
  exact A.ready_prepend ho (by omega) hi (b := b) (by simpa [growing] using hg)

/-- In the absence of further savings every arc-growth step costs at most
`n`. The first extension is a single letter, not a trip around the orbit. -/
theorem ordinary_growth (A : Automaton n α) (ho : A.WeaklyOriented)
    (hs : A.Synchronizing) {a : α} {j : ZMod n} (hr : ∀ x, A.δ a x = x+j)
    (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (k : ℕ) (hk : 2+k ≤ n) : (A.ready (2+k) (1+n*k)).Nonempty := by
  induction k with
  | zero => simpa using A.seed ho hs (by omega)
  | succ k ih =>
    obtain ⟨b,i,hg⟩ := A.exists_growing ho hs (l := 2+k) (by omega) (by omega)
    have hE : (A.growing b (2+k)).Nonempty := ⟨i,by simpa [growing] using hg⟩
    have hR := ih (by omega)
    obtain ⟨s,hs'⟩ := A.grow_stage ho hr ht (by omega) hR hE
    have epos := card_pos.mpr hE
    have rpos := card_pos.mpr hR
    refine ⟨s,A.ready_mono ?_ hs'⟩
    rw [Nat.mul_succ]
    omega

/-- Closing alignment. Each pair consisting of a specified point and one of
the `n-l` omitted positions forbids only one translate. -/
theorem align_subset (A : Automaton n α) {a : α} {j : ZMod n}
    (hr : ∀ x, A.δ a x = x+j)
    (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (S : Finset (ZMod n)) {l t : ℕ} (hl : l ≤ n) (h : S.card*(n-l) < n)
    (hR : (A.ready l t).Nonempty) :
    ∃ w : List α, w.length ≤ t + S.card*(n-l) ∧ A.Synchronizes w S := by
  classical
  let good := univ.filter fun i : ZMod n => S ⊆ interval i l
  let bad (p : ZMod n) := univ.filter fun i : ZMod n => p ∉ interval i l
  have cBad (p : ZMod n) : (bad p).card = n-l := by
    have h' := card_filter_add_card_filter_not (s := (univ : Finset (ZMod n))) (fun i => p ∈ interval i l)
    rw [starts_card p hl, card_univ, ZMod.card] at h'
    dsimp [bad]
    omega
  have diff : univ \ good = S.biUnion bad := by
    ext i
    simp [good,bad,Finset.not_subset]
  have cb := card_biUnion_le (s := S) (t := bad)
  rw [← diff,card_sdiff_of_subset (subset_univ _)] at cb
  simp only [cBad,sum_const,nsmul_eq_mul,card_univ,ZMod.card] at cb
  have cb' : n - good.card ≤ S.card * (n-l) := by simpa using cb
  have ne : good.Nonempty := card_pos.mp (by omega)
  obtain ⟨i,hi,k,hk,hg⟩ := steer _ ht _ _ hR ne
  rw [ZMod.card] at hk
  have hRpos := card_pos.mpr hR
  obtain ⟨w,hw,hsw⟩ := A.mem_ready.mp (A.ready_rotate hr hi k)
  exact ⟨w,by omega,hsw.mono (mem_filter.mp hg).2⟩

/-- The full-state case, including one and two states. -/
theorem full_bound (A : Automaton n α) (hs : A.Synchronizing)
    (hc : A.Circular) (ho : A.WeaklyOriented) :
    ∃ w : List α, w.length ≤ B n n ∧ A.Synchronizes w univ := by
  have hn : 0 < n := NeZero.pos n
  by_cases hn1 : n = 1
  · exact ⟨[],by simp,A.emptyWord_of_card_one _ (by simp [ZMod.card,hn1])⟩
  by_cases hn2 : n = 2
  · simpa [hn2] using A.pair_bound hs univ (by simp [ZMod.card,hn2])
  obtain ⟨a,j,hr,ht⟩ := A.circular_rotation hc ho (by omega)
  obtain ⟨i,hi⟩ := A.ordinary_growth ho hs hr ht (n-2) (by omega)
  obtain ⟨w,hw,hS⟩ := A.mem_ready.mp hi
  rw [show 2+(n-2) = n by omega, interval_full] at hS
  refine ⟨w,?_,hS⟩
  rw [B_full hn]
  have h1 : n-1+1 = n := by omega
  have h2 : n-2+2 = n := by omega
  nlinarith [congrArg (n * ·) h2,congrArg ((n-1) * ·) h1,congrArg (n * ·) h1]

end Automaton

end CardosoSubsetSynchronization

namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n] {α : Type*}

namespace Automaton

theorem growing_rises (A : Automaton n α) (b : α) {l : ℕ} (hl : l ≤ n) :
    rises (height (A.δ b)) (l : ZMod n) = (A.growing b l).card := by
  unfold rises growing
  congr 1
  ext i
  have H := pre_card_height (A.δ b) i hl
  simp only [mem_filter,mem_univ,true_and]
  omega

/-- Each overfull singleton fibre supplies a different synchronized pair:
map every such pair's start back to the fibre's output. -/
theorem seed_count (A : Automaton n α) (ho : A.WeaklyOriented) (b : α) (hn : 2 ≤ n) :
    (A.growing b 1).card ≤ (A.ready 2 1).card := by
  classical
  have hsub : A.growing b 1 ⊆ (A.ready 2 1).image (A.δ b) := by
    intro i hi
    have hgt : 1 < (pre (A.δ b) (interval i 1)).card := (mem_filter.mp hi).2
    obtain ⟨s,k,hk,e⟩ := ho b i 1 (by omega)
    rw [e,interval_card s hk] at hgt
    have allp (p : ZMod n) (hp : p ∈ interval s 2) : A.δ b p = i := by
      have hm := interval_mono s hgt hp
      rw [← e] at hm
      simpa using hm
    have hs : s ∈ interval s 2 := by simp
    exact mem_image.mpr ⟨s,A.mem_ready.mpr ⟨[b],by simp,i,by simpa using allp⟩,allp _ hs⟩
  exact (card_le_card hsub).trans card_image_le

private theorem choose_growing (A : Automaton n α) (ho : A.WeaklyOriented)
    (hs : A.Synchronizing) (b : α) {l : ℕ} (hl : 0 < l) (hlt : l < n) :
    ∃ c, (A.growing c l).Nonempty ∧ rises (height (A.δ b)) (l : ZMod n) ≤ (A.growing c l).card := by
  rw [A.growing_rises b hlt.le]
  by_cases H : (A.growing b l).Nonempty
  · exact ⟨b,H,le_refl _⟩
  · have eq := not_nonempty_iff_eq_empty.mp H
    obtain ⟨c,i,hi⟩ := A.exists_growing ho hs hl hlt
    exact ⟨c,⟨i,by simpa [growing] using hi⟩,by simp [eq]⟩

/-- Keep a credit for every rise over *all* shifts from 1 to L-1.
The singleton shift counts initial choices, not an extra paid stage.
If the first choice and the first target already overlap, two letters
suffice to synchronize a triple, so use the first alternative instead. -/
private theorem credited_growth (A : Automaton n α) (ho : A.WeaklyOriented)
    (hs : A.Synchronizing) (b : α) {a : α} {j : ZMod n}
    (hr : ∀ x, A.δ a x = x+j) (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (k : ℕ) (hk : 3+k ≤ n) :
    ∃ t, (A.ready (3+k) t).Nonempty ∧
      (t ≤ 2+n*k ∨ t + (∑ h ∈ range (2+k), rises (height (A.δ b)) ((h+1 : ℕ) : ZMod n)) ≤
        2+(k+1)*(n+1)) := by
  induction k with
  | zero =>
    obtain ⟨c,hE,hc⟩ := A.choose_growing ho hs b (l := 2) (by omega) (by omega)
    have hR := A.seed ho hs (by omega)
    have h := A.grow_stage ho hr ht (by omega) hR hE
    have h1 := A.seed_count ho b (by omega)
    rw [← A.growing_rises b (by omega)] at h1
    refine ⟨_,h,?_⟩
    simp only [Nat.add_zero,Nat.mul_zero,Nat.zero_add,Nat.one_mul]
    rw [show 2 = 1+1 by decide,sum_range_succ,sum_range_one]
    simp only [Nat.zero_add, Nat.reduceAdd] at *
    by_cases e : n+1 ≤ (A.ready 2 1).card+(A.growing c 2).card
    · left; omega
    · right; omega
  | succ k ih =>
    obtain ⟨t,hR,hbound⟩ := ih (by omega)
    obtain ⟨c,hE,hc⟩ := A.choose_growing ho hs b (l := 3+k) (by omega) (by omega)
    have grow := A.grow_stage ho hr ht (by omega) hR hE
    have er := card_pos.mpr hE
    have rr := card_pos.mpr hR
    have ce := card_le_univ (A.growing c (3+k))
    rw [ZMod.card] at ce
    refine ⟨_,grow,?_⟩
    rcases hbound with h|h
    · left
      rw [Nat.mul_succ]
      omega
    · right
      rw [show 2+(k+1) = (2+k)+1 by omega,sum_range_succ,
        show 2+k+1 = 3+k by omega, Nat.succ_mul]
      omega

private theorem rises_sum_lengths (F : ZMod n → ℤ) {v : ℕ} (hv : v < n)
    (hd : n/2+1 ≤ v) (hdesc : 2 ≤ (univ.filter (fun x => F (x+1) < F x)).card) :
    2*v ≤ (∑ k ∈ range v, rises F ((k+1 : ℕ) : ZMod n)) + 2 := by
  let f (k : ℕ) : ZMod n := (k+1 : ℕ)
  have hin : Set.InjOn f (range v) := by
    intro k hk l hl eq
    have hk' := mem_range.mp hk
    have hl' := mem_range.mp hl
    have := natCast_inj_lt (by omega : k+1 < n) (by omega : l+1 < n) eq
    omega
  have h0 : 0 ∉ (range v).image f := by
    intro e
    obtain ⟨k,hk,h⟩ := mem_image.mp e
    have hk' := mem_range.mp hk
    have := natCast_inj_lt (by omega : k+1 < n) (by omega : 0 < n) (by simpa [f] using h)
    omega
  have card : ((range v).image f).card = v := by rw [card_image_of_injOn hin,card_range]
  have H := aggregate_rises_of_descents F 1 ((range v).image f) h0
    (by rw [ZMod.card,card]; exact hd) hdesc
  rwa [card,Finset.sum_image hin] at H

/-- The aggregate argument for a singular letter with at least two missing
outputs. No individual length is assumed to grow under that same letter. -/
theorem corank_two_bound (A : Automaton n α) (hs : A.Synchronizing)
    (hc : A.Circular) (ho : A.WeaklyOriented) (b : α)
    (hb : (univ.image (A.δ b)).card + 2 ≤ n)
    (S : Finset (ZMod n)) (hm : 3 ≤ S.card) (hn : 5 ≤ n) :
    ∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S := by
  let m := S.card
  let g := (n-1)/m
  let k := n-g-3
  have hmn : m ≤ n := by simpa [m,ZMod.card] using card_le_univ S
  have h3m : 3 ≤ m := hm
  have hprod : m*g ≤ n-1 := by simpa [g,Nat.mul_comm] using Nat.div_mul_le_self (n-1) m
  have h3g : 3*g ≤ n-1 := (Nat.mul_le_mul_right g h3m).trans hprod
  have hd : n/2+1 ≤ 2+k := by dsimp [k]; omega
  have hk : 3+k ≤ n := by dsimp [k]; omega
  have hL : 3+k = n-g := by dsimp [k]; omega
  obtain ⟨a,j,hr,ht⟩ := A.circular_rotation hc ho (by omega)
  obtain ⟨t,hR,hbound⟩ := A.credited_growth ho hs b hr ht k hk
  have two := rises_sum_lengths (height (A.δ b)) (by omega : 2+k < n) hd
    (by rw [height_descents]; omega)
  have tn : t ≤ 2+(n-1)*(k+1) := by
    rcases hbound with H|H
    · have eq : n-1+1 = n := by omega
      nlinarith [congrArg (· * (k+1)) eq]
    · have eq : n-1+1 = n := by omega
      nlinarith [congrArg (· * (k+1)) eq]
  have hg : n - (3+k) = g := by omega
  obtain ⟨w,hw,hS⟩ := A.align_subset hr ht S hk (by change m * _ < n; rw [hg]; omega) hR
  refine ⟨w,?_,hS⟩
  rw [hg] at hw
  change w.length ≤ B n m
  change w.length ≤ t + m*g at hw
  have hw' : w.length ≤ 2+(n-1)*(k+1)+m*g := by omega
  have hz := closing_budget n m h3m hmn
  have hmprod := ceiling_product_le (by omega : 1 ≤ m) hmn
  change m*(g+1)+1 ≤ 2*n at hmprod
  have hun : (n : ℤ) - (g : ℤ) - 2 = (k : ℤ)+1 := by omega
  change 2 + ((n : ℤ)-1)*((n : ℤ)-(g : ℤ)-2) + m*g + ((m : ℤ)-3) ≤
    ((n : ℤ)-1)^2 - (g : ℤ)*(2*n-m*(g+1)-1) at hz
  rw [hun] at hz
  change w.length ≤ (n-1)^2 - g*(2*n-m*(g+1)-1)
  apply Nat.le_sub_of_add_le
  zify [show 1 ≤ n by omega, show m*(g+1) ≤ 2*n by omega,
    show 1 ≤ 2*n-m*(g+1) by omega] at hw' ⊢
  have hm' : (3 : ℤ) ≤ m := by exact_mod_cast h3m
  linarith only [hw',hz,hm']

end Automaton

end CardosoSubsetSynchronization

namespace CardosoSubsetSynchronization

open Finset

namespace Automaton

variable {n : ℕ} [NeZero n] {α : Type*}

theorem exists_singular (A : Automaton n α) (hs : A.Synchronizing)
    (ho : A.WeaklyOriented) (hn : 2 ≤ n) :
    ∃ b, (univ.image (A.δ b)).card < n := by
  obtain ⟨b,i,hg⟩ := A.exists_growing ho hs (l := 1) (by decide) (by omega)
  refine ⟨b,?_⟩
  by_contra! h
  have eq : (univ.image (A.δ b)).card = (univ : Finset (ZMod n)).card := by
    have hle := card_image_le (f := A.δ b) (s := (univ : Finset (ZMod n)))
    simpa [ZMod.card] using (le_antisymm hle (by simpa [ZMod.card] using h))
  have hinj := card_image_iff.mp eq
  obtain ⟨p,hp,q,hq,hne⟩ := one_lt_card.mp hg
  exact hne (hinj (mem_univ _) (mem_univ _) (by
    have ep : A.δ b p = i := by simpa using hp
    have eq' : A.δ b q = i := by simpa using hq
    exact ep.trans eq'.symm))

/-- Outside the one-, two-, and full-subset cases, only a triple at four
states needs separate handling below five states. -/
theorem small_bound (A : Automaton n α) (hs : A.Synchronizing)
    (hc : A.Circular) (ho : A.WeaklyOriented) (S : Finset (ZMod n))
    (hn : n < 5) (hS : S.Nonempty) : ∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S := by
  have hpos := card_pos.mpr hS
  have hle := card_le_univ S
  rw [ZMod.card] at hle
  by_cases h1 : S.card = 1
  · exact ⟨[],by simp,A.emptyWord_of_card_one S h1⟩
  by_cases h2 : S.card = 2
  · simpa only [h2] using A.pair_bound hs S h2
  by_cases hf : S.card = n
  · obtain ⟨w,hw,hsw⟩ := A.full_bound hs hc ho
    exact ⟨w,hf.symm ▸ hw,hsw.mono (subset_univ _)⟩
  have hn4 : n = 4 := by omega
  have h3 : S.card = 3 := by omega
  obtain ⟨a,j,hr,ht⟩ := A.circular_rotation hc ho (by omega)
  have hR := A.ordinary_growth ho hs hr ht 1 (by omega)
  obtain ⟨w,hw,h⟩ := A.align_subset hr ht S (by omega : 2+1 ≤ n)
    (by simp [hn4,h3]) hR
  exact ⟨w,by simpa [B,hn4,h3] using hw,h⟩

end Automaton
end CardosoSubsetSynchronization
namespace CardosoSubsetSynchronization

/-- A subtraction-free decomposition of Cardoso's integer expression.
The only natural differences on the right have ordered operands. -/
theorem B_square_form {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) :
    let g := (n-1)/m
    B n m = (n-1-g)^2 + (m-1)*g*(g+1) := by
  let g := (n-1)/m
  have hg : g ≤ n-1 := Nat.div_le_self _ _
  have hc := ceiling_product_le hm hmn
  change m*(g+1)+1 ≤ 2*n at hc
  change (n-1)^2 - g*(2*n-m*(g+1)-1) = (n-1-g)^2 + (m-1)*g*(g+1)
  have e : (n-1)^2 = (n-1-g)^2 + (m-1)*g*(g+1) + g*(2*n-m*(g+1)-1) := by
    zify [show 1 ≤ n by omega, hg, hm, show m*(g+1) ≤ 2*n by omega,
      show 1 ≤ 2*n - m*(g+1) by omega]
    ring
  rw [e,Nat.add_sub_cancel]

/-- Exact agreement with the integral expression of the counting lemmas;
no clipping to zero by natural subtraction is used. -/
theorem cast_B {n m : ℕ} (hm : 0 < m) (hmn : m ≤ n) : (B n m : ℤ) = bound n m := by
  rw [B_square_form hm hmn]
  unfold bound
  push_cast [Nat.cast_sub (Nat.div_le_self _ _), Nat.cast_sub (by omega : 1 ≤ n),
    Nat.cast_sub (by omega : 1 ≤ m)]
  ring

end CardosoSubsetSynchronization
