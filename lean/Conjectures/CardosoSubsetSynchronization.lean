import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

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

/-- Two comparisons suffice: their higher endpoints must be distinct, and
their lower endpoints must be distinct. They need not use a common shift. -/
theorem aggregate_rises_of_comparisons (F : G → ℤ) (J : Finset G)
    (h0 : 0 ∉ J) (hd : Fintype.card G / 2 + 1 ≤ J.card)
    (x y a b : G) (hxy : x ≠ y) (he : a ≠ b)
    (hx' : F a < F x) (hy' : F b < F y) :
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
  · have hm : ∃ u v, (∀ i, i ≠ u → F u < F i) ∧ (∀ i, i ≠ v → F i < F v) := by
      rcases le_total (F x) (F y) with h | h
      · exact ordered_drops _ _ _ _ _ hxy he hx' hy' h hb
      · exact ordered_drops _ _ _ _ _ hxy.symm he.symm hy' hx' h hb
    obtain ⟨u,v,hu,hv⟩ := hm
    have H := extrema_rises F J h0 u v hu hv
    omega

/-- Two distinct descents of the same shift force aggregate growth.
No cut, symmetry of the height function, or per-shift lower bound is assumed. -/
theorem aggregate_rises_of_descents (F : G → ℤ) (s : G) (J : Finset G)
    (h0 : 0 ∉ J) (hd : Fintype.card G / 2 + 1 ≤ J.card)
    (hdesc : 2 ≤ (univ.filter fun x => F (x+s) < F x).card) :
    2 * J.card ≤ (∑ l ∈ J, rises F l) + 2 := by
  classical
  obtain ⟨x,hx,y,hy,hxy⟩ := one_lt_card.mp hdesc
  exact aggregate_rises_of_comparisons F J h0 hd x y (x+s) (y+s) hxy
    (fun eq => hxy (add_right_cancel eq)) (mem_filter.mp hx).2 (mem_filter.mp hy).2

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
    (hd : n/2+1 ≤ v) (hagg : ∀ J : Finset (ZMod n), 0 ∉ J → n/2+1 ≤ J.card →
      2*J.card ≤ (∑ l ∈ J, rises F l)+2) :
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
  have H := hagg ((range v).image f) h0 (by rwa [card])
  rwa [card,Finset.sum_image hin] at H

private theorem bound_of_aggregate (A : Automaton n α) (hs : A.Synchronizing)
    (hc : A.Circular) (ho : A.WeaklyOriented) (b : α)
    (hagg : ∀ J : Finset (ZMod n), 0 ∉ J → n/2+1 ≤ J.card →
      2*J.card ≤ (∑ l ∈ J, rises (height (A.δ b)) l)+2)
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
    hagg
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

/-- The aggregate argument for a singular letter with at least two missing
outputs. No individual length is assumed to grow under that same letter. -/
theorem corank_two_bound (A : Automaton n α) (hs : A.Synchronizing)
    (hc : A.Circular) (ho : A.WeaklyOriented) (b : α)
    (hb : (univ.image (A.δ b)).card + 2 ≤ n)
    (S : Finset (ZMod n)) (hm : 3 ≤ S.card) (hn : 5 ≤ n) :
    ∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S := by
  apply A.bound_of_aggregate hs hc ho b _ S hm hn
  intro J h0 hd
  exact aggregate_rises_of_descents _ 1 J h0 (by simpa [ZMod.card] using hd)
    (by rw [height_descents]; omega)

/-- A missing output and a repeated output with neither adjacent to the
other give two comparisons in the periodic height function. -/
theorem separated_defect_bound (A : Automaton n α) (hs : A.Synchronizing)
    (hc : A.Circular) (ho : A.WeaklyOriented) (b : α) (u v : ZMod n)
    (hu : fibre (A.δ b) u = 0) (hv : 2 ≤ fibre (A.δ b) v)
    (hl : u+1 ≠ v) (hr : u ≠ v+1)
    (S : Finset (ZMod n)) (hm : 3 ≤ S.card) (hn : 5 ≤ n) :
    ∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S := by
  apply A.bound_of_aggregate hs hc ho b _ S hm hn
  intro J h0 hd
  apply aggregate_rises_of_comparisons _ J h0 (by simpa [ZMod.card] using hd)
    u (v+1) (u+1) v hr hl
  · rw [height_step,hu]; simp
  · rw [height_step]; omega

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
namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n] {α : Type*}

theorem back_steps (x j : ZMod n) (k : ℕ) :
    (fun p : ZMod n => p-j)^[k] x = x - (k : ZMod n)*j := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply',ih,Nat.cast_succ,add_mul,one_mul]; abel

namespace Automaton

private theorem target_count (S : Finset (ZMod n)) {l : ℕ} (hl : l ≤ n) :
    n - (univ.filter (fun i : ZMod n => S ⊆ interval i l)).card ≤ S.card*(n-l) := by
  classical
  let good := univ.filter fun i : ZMod n => S ⊆ interval i l
  let bad (p : ZMod n) := univ.filter fun i : ZMod n => p ∉ interval i l
  have cBad (p : ZMod n) : (bad p).card = n-l := by
    have h' := card_filter_add_card_filter_not (s := (univ : Finset (ZMod n))) (fun i => p ∈ interval i l)
    rw [starts_card p hl, card_univ, ZMod.card] at h'
    dsimp [bad]
    omega
  have diff : univ \ good = S.biUnion bad := by ext i; simp [good,bad,Finset.not_subset]
  have cb := card_biUnion_le (s := S) (t := bad)
  rw [← diff,card_sdiff_of_subset (subset_univ _)] at cb
  simpa [cBad,ZMod.card,good] using cb

private theorem all_starts (A : Automaton n α) {a : α} {j : ZMod n}
    (hr : ∀ x, A.δ a x = x+j) (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    {l u : ℕ} (hR : (A.ready l u).Nonempty) (s : ZMod n) :
    s ∈ A.ready l (u+(n-1)) := by
  obtain ⟨i,hi,k,hk,hs⟩ := steer _ ht _ {s} hR (singleton_nonempty _)
  rw [ZMod.card,card_singleton] at hk
  have e := mem_singleton.mp hs
  have h := A.ready_rotate hr hi k
  rw [e] at h
  have := card_pos.mpr hR
  exact A.ready_mono (by omega) h

/-- Under a successor or predecessor circular letter one can use the ordinary
growth bound. Either the target fits a shorter arc, or the admissible starts
are spaced by at least one more than the size of the omitted arc. -/
theorem unit_jump_bound (A : Automaton n α) (hs : A.Synchronizing)
    (ho : A.WeaklyOriented) {a : α} {j : ZMod n}
    (hr : ∀ x, A.δ a x = x+j) (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (hj : j = 1 ∨ j = -1) (S : Finset (ZMod n)) (hm : 3 ≤ S.card) (hn : 5 ≤ n) :
    ∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S := by
  classical
  let m := S.card
  let g := (n-1)/m
  let e := (n-1)%m + 1
  let d := n-g-2
  have hm' : 3 ≤ m := hm
  have hmn : m ≤ n := by simpa [m,ZMod.card] using card_le_univ S
  have he0 : 1 ≤ e := by dsimp [e]; omega
  have hem : e ≤ m := by
    have h := Nat.mod_lt (n-1) (by omega : 0 < m)
    dsimp [e]; omega
  have dec : n = m*g+e := by
    have h := Nat.mod_add_div (n-1) m
    dsimp [g,e]; omega
  have h3g : 3*g ≤ m*g := Nat.mul_le_mul_right g hm'
  have hd : d+g+2 = n := by dsimp [d]; omega
  have hd1 : 1 ≤ d := by omega
  have en : (e-1)*(g+1) ≤ n-1 := by
    have h := Nat.mul_le_mul_right g (by omega : e-1 ≤ m)
    rw [Nat.mul_add,Nat.mul_one]
    omega
  have price : B n m + (e-1)*(g+1) = (1+n*d)+(n-1) := by
    have hc := cast_B (by omega : 0 < m) hmn
    change (B n m : ℤ) = ((n:ℤ)-1)^2 - (g:ℤ)*(2*n-m*(g+1)-1) at hc
    have de : (n:ℤ) = m*(g:ℤ)+e := by exact_mod_cast dec
    have dd : (d:ℤ)+(g:ℤ)+2 = n := by exact_mod_cast hd
    zify [he0,show 1 ≤ n by omega]
    rw [hc]
    nlinarith [congrArg (· * (g:ℤ)) de, congrArg (· * (n:ℤ)) dd]
  let T := univ.filter fun i : ZMod n => S ⊆ interval i (2+d)
  have mt (i : ZMod n) : i ∈ T ↔ S ⊆ interval i (2+d) := by simp [T]
  have cT : e ≤ T.card := by
    have h := target_count S (l := 2+d) (by omega)
    change n - T.card ≤ m*(n-(2+d)) at h
    rw [show n-(2+d) = g by omega] at h
    omega
  by_cases short : ∃ i ∈ T, i ∉ S
  · obtain ⟨i,hi,hnS⟩ := short
    have sub : S ⊆ interval (i+1) (2+(d-1)) := by
      intro p hp
      obtain ⟨k,hk,e'⟩ := mem_interval.mp ((mt i).mp hi hp)
      cases k with
      | zero => exact False.elim (hnS (by simpa [← e'] using hp))
      | succ k => exact mem_interval.mpr ⟨k,by omega,by rw [← e',Nat.cast_succ]; abel⟩
    have hR := A.ordinary_growth ho hs hr ht (d-1) (by omega)
    obtain ⟨w,hw,hS⟩ := A.mem_ready.mp (A.all_starts hr ht hR (i+1))
    have eqd : d-1+1 = d := by omega
    have eqm := congrArg (n * ·) eqd
    rw [Nat.mul_add,Nat.mul_one] at eqm
    exact ⟨w,by change w.length ≤ B n m; omega,hS.mono sub⟩
  · have inS (i : ZMod n) (hi : i ∈ T) : i ∈ S := by
      by_contra h; exact short ⟨i,hi,h⟩
    have sep (i u : ZMod n) (hi : i ∈ T) (hu : u ∈ T) (k : ℕ)
        (hk : 0 < k) (hkg : k ≤ g) : i + (k : ZMod n) ≠ u := by
      intro E
      obtain ⟨v,hv,H⟩ := mem_interval.mp ((mt u).mp hu (inS i hi))
      have HH : i+((k : ZMod n)+v) = i+0 := by simpa only [← add_assoc,E,add_zero] using H
      have neq := natCast_inj_lt (by omega : k+v < n) (by omega : 0 < n)
        (by simpa only [Nat.cast_add,Nat.cast_zero] using add_left_cancel HH)
      omega
    let Φ (z : ZMod n × ℕ) := z.1 + (z.2 : ZMod n)*j
    let blocks := T ×ˢ range (g+1)
    let hit := blocks.image Φ
    have distinct (x y : ZMod n) (hx : x ∈ T) (hy : y ∈ T) (p q : ℕ)
        (h : p < q) (hq : q ≤ g) : x+(p : ZMod n)*j ≠ y+(q : ZMod n)*j := by
      intro E
      let k := q-p
      have hk : 0 < k := by dsimp [k]; omega
      have hkg : k ≤ g := by dsimp [k]; omega
      have eq : p+k = q := by dsimp [k]; omega
      have castEq : (p : ZMod n) + k = q := by rw [← Nat.cast_add,eq]
      have Y : y+(k : ZMod n)*j = x := by
        calc
          _ = y+((p : ZMod n)+k)*j - p*j := by ring
          _ = x := by rw [castEq,← E]; abel
      rcases hj with E'|E'
      · exact sep _ _ hy hx _ hk hkg (by simpa [E'] using Y)
      · exact sep _ _ hx hy _ hk hkg (by rw [← Y]; simp [E'])
    have hin : Set.InjOn Φ blocks := by
      rintro ⟨x,p⟩ hp ⟨y,q⟩ hq hE
      obtain ⟨hx,hp'⟩ := mem_product.mp hp
      obtain ⟨hy,hq'⟩ := mem_product.mp hq
      have hp'' := mem_range.mp hp'
      have hq'' := mem_range.mp hq'
      change x+(p : ZMod n)*j = y+(q : ZMod n)*j at hE
      rcases lt_trichotomy p q with H|H|H
      · exact False.elim (distinct x y hx hy p q H (by omega) hE)
      · subst q
        exact Prod.ext (add_right_cancel hE) rfl
      · exact False.elim (distinct y x hy hx q p H (by omega) hE.symm)
    have sz : hit.card = T.card*(g+1) := by
      change (blocks.image Φ).card = _
      rw [card_image_of_injOn hin]
      simp [blocks]
    have nz : hit.Nonempty := card_pos.mp (sz ▸ Nat.mul_pos (by omega) (by omega))
    have hR := A.ordinary_growth ho hs hr ht d (by omega)
    obtain ⟨i,hi,k,hk,hhit⟩ := steer _ ht _ _ hR nz
    rw [ZMod.card] at hk
    have hpR := card_pos.mpr hR
    obtain ⟨z,hz,hitEq⟩ := mem_image.mp hhit
    obtain ⟨hzT,hzt⟩ := mem_product.mp hz
    have hzt' := mem_range.mp hzt
    have hrot := A.ready_rotate hr (A.ready_rotate hr hi k) z.2
    rw [back_steps,← hitEq] at hrot
    change z.1 + (z.2 : ZMod n)*j - (z.2 : ZMod n)*j ∈ _ at hrot
    rw [add_sub_cancel_right] at hrot
    obtain ⟨w,hw,hsw⟩ := A.mem_ready.mp hrot
    have ub := card_le_univ hit
    rw [ZMod.card] at ub
    have lc : e*(g+1) ≤ hit.card := sz ▸ Nat.mul_le_mul_right _ cT
    have he : e-1+1=e := by omega
    have he' := congrArg (· * (g+1)) he
    rw [Nat.add_mul,Nat.one_mul] at he'
    exact ⟨w,by change w.length ≤ B n m; omega,hsw.mono ((mt _).mp hzT)⟩

end Automaton
end CardosoSubsetSynchronization
namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n] {α : Type*}

theorem fibre_zero_iff (f : ZMod n → ZMod n) (q : ZMod n) :
    fibre f q = 0 ↔ q ∉ univ.image f := by
  simp [fibre,pre,Finset.filter_eq_empty_iff,mem_image]

/-- A transformation missing exactly one output has exactly one double
fibre and all remaining nonempty fibres are singletons. -/
theorem defect_profile (f : ZMod n → ZMod n) (hr : (univ.image f).card+1 = n) :
    ∃ u v : ZMod n, u ≠ v ∧ ∀ q, fibre f q = if q = u then 0 else if q = v then 2 else 1 := by
  classical
  let R := univ.image f
  change R.card+1 = n at hr
  have hc : (univ \ R).card = 1 := by
    rw [card_sdiff_of_subset (subset_univ _),card_univ,ZMod.card]; omega
  obtain ⟨u,hu⟩ := card_eq_one.mp hc
  have miss (q : ZMod n) : q ∉ R ↔ q = u := by
    have h := Finset.ext_iff.mp hu q
    simpa using h
  have sumF : ∑ q : ZMod n, fibre f q = n := by
    simpa [fibre] using pre_total f (l := 1) (NeZero.pos n)
  have sumR : ∑ q ∈ R, fibre f q = n := by
    calc
      _ = ∑ q : ZMod n, fibre f q := by
        apply sum_subset (subset_univ _)
        intro q _ hq
        exact (fibre_zero_iff ..).mpr hq
      _ = n := sumF
  let extra (q : ZMod n) := fibre f q - 1
  have pos (q : ZMod n) (hq : q ∈ R) : 0 < fibre f q := by
    by_contra! H
    exact (fibre_zero_iff ..).mp (by omega) hq
  have pieces : ∑ q ∈ R, (extra q + 1) = n := by
    calc
      _ = ∑ q ∈ R, fibre f q := by
        apply sum_congr rfl
        intro q hq
        have := pos q hq
        dsimp [extra]; omega
      _ = n := sumR
  have budget : ∑ q ∈ R, extra q = 1 := by
    rw [sum_add_distrib] at pieces
    simp only [sum_const,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at pieces
    omega
  obtain ⟨v,hv,hv'⟩ : ∃ v ∈ R, 0 < extra v := by
    by_contra! no
    have zero := sum_eq_zero (fun q hq => Nat.eq_zero_of_le_zero (no q hq))
    omega
  have neuv : u ≠ v := by intro e; exact (miss v).mpr e.symm hv
  have ev : extra v ≤ 1 := by
    rw [← budget]
    exact single_le_sum (fun q _ => Nat.zero_le (extra q)) hv
  refine ⟨u,v,neuv,?_⟩
  intro q
  by_cases qu : q = u
  · simpa [qu] using (fibre_zero_iff f u).mpr ((miss u).mpr rfl)
  · have qr : q ∈ R := by by_contra h; exact qu ((miss q).mp h)
    have pq := pos q qr
    by_cases qv : q = v
    · subst q
      dsimp [extra] at hv' ev
      simp [qu] <;> omega
    · have le : extra q + extra v ≤ ∑ y ∈ R, extra y := by
        calc
          _ = ∑ y ∈ ({q,v} : Finset _), extra y := by simp [qv]
          _ ≤ _ := sum_le_sum_of_subset_of_nonneg (by
            intro y hy
            simp only [mem_insert,mem_singleton] at hy
            rcases hy with rfl|rfl
            · exact qr
            · exact hv)
            (fun _ _ _ => Nat.zero_le _)
      rw [budget] at le
      simp only [if_neg qu,if_neg qv]
      dsimp [extra] at le hv'
      omega

namespace Automaton

/-- Necessary structure of an unresolved upper-bound instance after the
growth, separation, and successor-jump arguments. -/
theorem residual_of_no_short_word (A : Automaton n α) (hs : A.Synchronizing)
    (hc : A.Circular) (ho : A.WeaklyOriented) (S : Finset (ZMod n)) (hS : S.Nonempty)
    (no : ¬∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S) :
    5 ≤ n ∧ 3 ≤ S.card ∧ S.card < n ∧
    ∃ (a b : α) (j u v : ZMod n),
      (∀ x, A.δ a x = x+j) ∧ (∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y) ∧
      j ≠ 1 ∧ j ≠ -1 ∧ u ≠ v ∧ (u+1 = v ∨ u = v+1) ∧
      (∀ q, fibre (A.δ b) q = if q = u then 0 else if q = v then 2 else 1) := by
  classical
  have hn : 5 ≤ n := by by_contra! h; exact no (A.small_bound hs hc ho S h hS)
  have hm : 3 ≤ S.card := by
    have hp := card_pos.mpr hS
    by_contra! h
    rcases (show S.card = 1 ∨ S.card = 2 by omega) with he|he
    · exact no ⟨[],by simp,A.emptyWord_of_card_one S he⟩
    · exact no (by simpa [he] using A.pair_bound hs S he)
  have lt : S.card < n := by
    have h := card_le_univ S
    rw [ZMod.card] at h
    by_contra! h'
    have e : S.card = n := by omega
    obtain ⟨w,hw,hSw⟩ := A.full_bound hs hc ho
    exact no ⟨w,by simpa only [e] using hw,hSw.mono (subset_univ _)⟩
  obtain ⟨a,j,hr,ht⟩ := A.circular_rotation hc ho (by omega)
  have nj : ¬(j = 1 ∨ j = -1) := fun h => no (A.unit_jump_bound hs ho hr ht h S hm hn)
  obtain ⟨b,hb⟩ := A.exists_singular hs ho (by omega)
  have eq : (univ.image (A.δ b)).card+1 = n := by
    by_contra h
    exact no (A.corank_two_bound hs hc ho b (by omega) S hm hn)
  obtain ⟨u,v,ne,prof⟩ := defect_profile _ eq
  have both : u+1 = v ∨ u = v+1 := by
    by_contra! h
    exact no (A.separated_defect_bound hs hc ho b u v (by simp [prof])
      (by simp [prof,Ne.symm ne]) h.1 h.2 S hm hn)
  exact ⟨hn,hm,lt,a,b,j,u,v,hr,ht,fun h => nj (Or.inl h),fun h => nj (Or.inr h),ne,both,prof⟩

end Automaton
end CardosoSubsetSynchronization
namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n] {α : Type*}

/-- The elementary fold sending the predecessor of zero to zero. -/
def foldPoint (z : ZMod n) : ZMod n := if z = -1 then 0 else z

theorem fold_grows {z : ZMod n} {l : ℕ} (hl : 0 < l) (hz : z ∈ interval (-1) (l+1)) :
    foldPoint z ∈ interval 0 l := by
  by_cases e : z = -1
  · simpa [foldPoint,e] using (mem_interval.mpr ⟨0,hl,by simp⟩ : (0 : ZMod n) ∈ interval 0 l)
  · rw [foldPoint,if_neg e]
    obtain ⟨k,hk,rfl⟩ := mem_interval.mp hz
    cases k with
    | zero => simp at e
    | succ k => exact mem_interval.mpr ⟨k,by omega,by push_cast; abel⟩

theorem fold_neutral (s : ZMod n) (l : ℕ) (hs : s ≠ 0) (he : s+l ≠ 0) (z : ZMod n)
    (hz : z ∈ interval s l) : foldPoint z ∈ interval s l := by
  by_cases e : z = -1
  · subst z
    obtain ⟨k,hk,h⟩ := mem_interval.mp hz
    have add : s + ((k+1 : ℕ) : ZMod n) = 0 := by rw [Nat.cast_succ,← add_assoc,h]; simp
    have lt : k+1 < l := by
      by_contra! hl
      have E : k+1=l := by omega
      exact he (E ▸ add)
    simpa [foldPoint] using (mem_interval.mpr ⟨k+1,lt,add⟩ : (0 : ZMod n) ∈ interval s l)
  · simpa [foldPoint,e] using hz

private def postStart (c d : ZMod n) (h : ℕ) : ZMod n := if d = 1 then c-1 else c-h

namespace Automaton

private theorem normalized_extend (A : Automaton n α) {b : α} {c d : ZMod n}
    (hd : d = 1 ∨ d = -1) (hb : ∀ z, A.δ b (c+d*z) = foldPoint z)
    {h t : ℕ} (hR : (0 : ZMod n) ∈ A.ready (1+h) t) :
    postStart c d h ∈ A.ready (2+h) (t+1) := by
  obtain ⟨w,hw,q,hq⟩ := A.mem_ready.mp hR
  refine A.mem_ready.mpr ⟨b::w,by simpa using Nat.succ_le_succ hw,q,?_⟩
  intro p hp
  obtain ⟨k,hk,rfl⟩ := mem_interval.mp hp
  apply hq
  by_cases inc : d=1
  · have eq : postStart c d h + k = c+d*(-1+(k : ZMod n)) := by simp [postStart,inc]; abel
    rw [eq,hb]
    exact fold_grows (by omega) (mem_interval.mpr ⟨k,by omega,rfl⟩)
  · have rev := hd.resolve_left inc
    have hk' : k ≤ 1+h := by omega
    have eq : postStart c d h + k = c+d*(-1+((1+h-k : ℕ) : ZMod n)) := by
      unfold postStart
      rw [if_neg inc,rev,Nat.cast_sub hk',Nat.cast_add,Nat.cast_one,neg_one_mul]
      abel
    rw [eq,hb]
    exact fold_grows (by omega) (mem_interval.mpr ⟨1+h-k,by omega,rfl⟩)

private theorem short_to_zero (A : Automaton n α) {a : α} {j : ZMod n}
    (hr : ∀ x, A.δ a x = x+j) (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    {s : ZMod n} {l t : ℕ} (hR : s ∈ A.ready l t) (hn : 2 ≤ n) (ns : s ≠ -j) :
    (0 : ZMod n) ∈ A.ready l (t+(n-2)) := by
  obtain ⟨i,hi,k,hk,h0⟩ := steer _ ht {s} {0} (singleton_nonempty _) (singleton_nonempty _)
  have ei := mem_singleton.mp hi
  subst i
  have e := mem_singleton.mp h0
  simp only [ZMod.card,card_singleton] at hk
  have short : k ≤ n-2 := by
    by_contra! long
    have ek : k+1 = n := by omega
    have endpt : (fun p : ZMod n => p-j)^[k+1] s = -j := by rw [Function.iterate_succ_apply',e]; simp
    rw [ek,back_steps] at endpt
    exact ns (by simpa using endpt)
  have h' := A.ready_rotate hr hR k
  rw [e] at h'
  exact A.ready_mono (by omega) h'

private theorem normalized_fast (A : Automaton n α) {a b : α} {j c d : ZMod n}
    (hr : ∀ x, A.δ a x = x+j) (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (hd : d = 1 ∨ d = -1) (hb : ∀ z, A.δ b (c+d*z) = foldPoint z)
    (hn : 3 ≤ n) (nj : j ≠ 0) (j1 : j ≠ 1) {h t : ℕ}
    (hi : (h : ZMod n) ≠ (if d=1 then j-2 else c+j))
    (hR : postStart c d h ∈ A.ready (2+h) t) :
    (0 : ZMod n) ∈ A.ready (2+h) (t+(n-2)) := by
  by_cases ns : postStart c d h = -j
  · have inc : d = 1 := by
      by_contra inc
      simp only [postStart,if_neg inc] at ns
      apply hi
      simp only [if_neg inc]
      calc
        (h : ZMod n) = c-(c-h) := by abel
        _ = c+j := by rw [ns]; abel
    have sc : c-1 = -j := by simpa [postStart,inc] using ns
    let s := c-1
    have ns0 : s ≠ 0 := by change c-1 ≠ 0; rw [sc]; simpa using nj
    have neEnd : s+((2+h : ℕ) : ZMod n) ≠ 0 := by
      intro he
      apply hi
      simp only [if_pos inc]
      change c-1+((2+h : ℕ) : ZMod n) = 0 at he
      rw [sc,Nat.cast_add,Nat.cast_ofNat] at he
      calc
        (h : ZMod n) = j-2+(-j+(2+(h : ZMod n))) := by abel
        _ = _ := by rw [he,add_zero]
    have c0 : c ≠ 0 := by
      intro e
      rw [e,zero_sub] at sc
      exact j1 (neg_injective sc.symm)
    have cNj : c ≠ -j := by
      intro e
      rw [← e] at sc
      have o : (1 : ZMod n) = 0 := by simpa using sc
      have := natCast_inj_lt (n := n) (by omega : 1 < n) (by omega : 0 < n) (by simpa using o)
      omega
    have start : s ∈ A.ready (2+h) t := by simpa [postStart,inc,s] using hR
    have h1 : s ∈ A.ready (2+h) (t+1) := A.ready_mono (by omega) start
    have h2 : s-j ∈ A.ready (2+h) (t+1) := by simpa using A.ready_rotate hr start 1
    have h3 : s+c ∈ A.ready (2+h) (t+1) := by
      obtain ⟨w,hw,q,hq⟩ := A.mem_ready.mp start
      refine A.mem_ready.mpr ⟨b::w,by simpa using Nat.succ_le_succ hw,q,?_⟩
      intro p hp
      obtain ⟨k,hk,rfl⟩ := mem_interval.mp hp
      apply hq
      have E : s+c+(k : ZMod n) = c+d*(s+k) := by rw [inc,one_mul]; abel
      rw [E,hb]
      exact fold_neutral s _ ns0 neEnd _ (mem_interval.mpr ⟨k,hk,rfl⟩)
    have n12 : s ≠ s-j := by simpa [sub_eq_add_neg] using nj
    have n13 : s ≠ s+c := by simpa using c0
    have n23 : s-j ≠ s+c := by simpa [sub_eq_add_neg] using Ne.symm cNj
    have sub : ({s,s-j,s+c} : Finset _) ⊆ A.ready (2+h) (t+1) := by
      intro x hx
      simp only [mem_insert,mem_singleton] at hx
      rcases hx with rfl|rfl|rfl
      · exact h1
      · exact h2
      · exact h3
    have cnt := card_le_card sub
    simp [n12,n13,n23] at cnt
    obtain ⟨x,hx,k,hk,hz⟩ := steer _ ht _ {0} ⟨s,h1⟩ (singleton_nonempty _)
    rw [ZMod.card,card_singleton] at hk
    have H := A.ready_rotate hr hx k
    rw [mem_singleton.mp hz] at H
    exact A.ready_mono (by omega) H
  · exact A.short_to_zero hr ht hR (by omega) ns

/-- Increasing or decreasing lifts of the elementary fold. At most one
length needs all n letters; every other growth saves at least one. -/
theorem normalized_growth (A : Automaton n α) {a b : α} {j c d : ZMod n}
    (hr : ∀ x, A.δ a x = x+j) (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (hd : d = 1 ∨ d = -1) (hb : ∀ z, A.δ b (c+d*z) = foldPoint z)
    (hn : 3 ≤ n) (nj : j ≠ 0) (j1 : j ≠ 1) (k : ℕ) (hk : 2+k ≤ n) :
    (A.ready (2+k) (2+(n-1)*k)).Nonempty := by
  let bad : ZMod n := if d=1 then j-2 else c+j
  have run (h : ℕ) (hh : h ≤ k) :
      postStart c d h ∈ A.ready (2+h) (1+(n-1)*h+if bad.val < h then 1 else 0) := by
    induction h with
    | zero =>
      have seed : (0 : ZMod n) ∈ A.ready 1 0 := A.mem_ready.mpr ⟨[],by simp,0,by simp⟩
      simpa using A.normalized_extend hd hb (h := 0) seed
    | succ h ih =>
      have start := ih (by omega)
      let t := 1+(n-1)*h+if bad.val<h then 1 else 0
      change postStart c d h ∈ A.ready (2+h) t at start
      by_cases crit : h=bad.val
      · have target := A.all_starts hr ht (show (A.ready (2+h) t).Nonempty from ⟨_,start⟩) 0
        have next := A.normalized_extend hd hb (h := h+1) (t := t+(n-1)) (by simpa [Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using target)
        apply A.ready_mono _ next
        dsimp [t]
        rw [Nat.mul_succ]
        split_ifs <;> omega
      · have hcrit : (h : ZMod n) ≠ bad := by
          intro E
          have hval := congrArg ZMod.val E
          rw [ZMod.val_natCast_of_lt (by omega)] at hval
          exact crit hval
        have target := A.normalized_fast hr ht hd hb hn nj j1 hcrit start
        have next := A.normalized_extend hd hb (h := h+1) (t := t+(n-2)) (by simpa [Nat.add_comm,Nat.add_assoc,Nat.add_left_comm] using target)
        apply A.ready_mono _ next
        dsimp [t]
        rw [Nat.mul_succ]
        split_ifs <;> omega
  refine ⟨_,A.ready_mono ?_ (run k (le_refl _))⟩
  split_ifs <;> omega

end Automaton
end CardosoSubsetSynchronization
namespace CardosoSubsetSynchronization

variable {n : ℕ} [NeZero n] {α : Type*}
open Finset

/-- Relabel the states by translation, possibly reversing the drawing of
the circle. The boolean only chooses the sign in this coordinate change. -/
def chart (v : ZMod n) (r : Bool) : Equiv.Perm (ZMod n) where
  toFun z := if r then v-z else v+z
  invFun z := if r then v-z else z-v
  left_inv z := by cases r <;> simp <;> abel
  right_inv z := by cases r <;> simp <;> abel

private theorem chart_arcs (v : ZMod n) (r : Bool) (i : ZMod n) (l : ℕ) :
    ∃ s, (interval i l).image (chart v r) = interval s l := by
  cases r with
  | false =>
    refine ⟨v+i,?_⟩
    ext x
    constructor
    · intro hx; obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      obtain ⟨k,hk,rfl⟩ := mem_interval.mp hy
      exact mem_interval.mpr ⟨k,hk,by change v+i+k = v+(i+k); abel⟩
    · intro hx; obtain ⟨k,hk,rfl⟩ := mem_interval.mp hx
      exact mem_image.mpr ⟨i+k,mem_interval.mpr ⟨k,hk,rfl⟩,by change v+(i+k) = v+i+k; abel⟩
  | true =>
    refine ⟨v-i-(l-1 : ℕ),?_⟩
    ext x
    have off (k : ℕ) (hk : k < l) : k + (l-1-k) = l-1 := by omega
    have caster (k : ℕ) (hk : k < l) :
        (k : ZMod n) + ((l-1-k : ℕ) : ZMod n) = ((l-1 : ℕ) : ZMod n) := by
      rw [← Nat.cast_add,off k hk]
    constructor
    · intro hx; obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      obtain ⟨k,hk,rfl⟩ := mem_interval.mp hy
      apply mem_interval.mpr
      refine ⟨l-1-k,by omega,?_⟩
      change v-i-((l-1 : ℕ) : ZMod n)+((l-1-k : ℕ) : ZMod n) = v-(i+k)
      rw [← caster k hk]; abel
    · intro hx; obtain ⟨k,hk,rfl⟩ := mem_interval.mp hx
      refine mem_image.mpr ⟨i+((l-1-k : ℕ) : ZMod n),mem_interval.mpr ⟨l-1-k,by omega,rfl⟩,?_⟩
      change v-(i+((l-1-k : ℕ) : ZMod n)) = v-i-((l-1 : ℕ) : ZMod n)+k
      rw [← caster k hk]; abel

private theorem chart_symm_arcs (v : ZMod n) (r : Bool) (i : ZMod n) (l : ℕ) :
    ∃ s, (interval i l).image (chart v r).symm = interval s l := by
  cases r with
  | true => exact chart_arcs v true i l
  | false =>
    have e : (chart v false).symm = chart (-v) false := by ext x; change x-v = -v+x; abel
    rw [e]
    exact chart_arcs _ _ _ _

namespace Automaton

def relabel (A : Automaton n α) (π : Equiv.Perm (ZMod n)) : Automaton n α :=
  ⟨fun a z => π.symm (A.δ a (π z))⟩

theorem act_relabel (A : Automaton n α) (π : Equiv.Perm (ZMod n)) (w : List α) (x : ZMod n) :
    π ((A.relabel π).act w x) = A.act w (π x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih => rw [act_cons,ih,act_cons]; simp [relabel]

theorem sync_of_relabel (A : Automaton n α) (π : Equiv.Perm (ZMod n)) {w : List α}
    {S : Finset (ZMod n)} (hs : (A.relabel π).Synchronizes w (S.image π.symm)) :
    A.Synchronizes w S := by
  obtain ⟨q,hq⟩ := hs
  refine ⟨π q,?_⟩
  intro p hp
  have h := congrArg π (hq (π.symm p) (mem_image_of_mem _ hp))
  simpa [act_relabel] using h

theorem pre_relabel (A : Automaton n α) (π : Equiv.Perm (ZMod n)) (b : α) (T : Finset (ZMod n)) :
    pre ((A.relabel π).δ b) T = (pre (A.δ b) (T.image π)).image π.symm := by
  ext x
  constructor
  · intro h
    have hx := mem_pre.mp h
    refine mem_image.mpr ⟨π x,mem_pre.mpr (mem_image.mpr ⟨_,hx,?_⟩),by simp⟩
    simp [relabel]
  · intro h
    obtain ⟨y,hy,rfl⟩ := mem_image.mp h
    obtain ⟨z,hz,e⟩ := mem_image.mp (mem_pre.mp hy)
    simpa [relabel,← e] using hz

theorem fibre_relabel (A : Automaton n α) (π : Equiv.Perm (ZMod n)) (b : α) (z : ZMod n) :
    fibre ((A.relabel π).δ b) z = fibre (A.δ b) (π z) := by
  simp [fibre,pre_relabel,card_image_of_injective _ π.symm.injective]

theorem chart_oriented (A : Automaton n α) (ho : A.WeaklyOriented) (v : ZMod n) (r : Bool) :
    (A.relabel (chart v r)).WeaklyOriented := by
  intro b i l hl
  obtain ⟨p,ep⟩ := chart_arcs v r i l
  obtain ⟨q,k,hk,eq⟩ := ho b p l hl
  obtain ⟨z,ez⟩ := chart_symm_arcs v r q k
  exact ⟨z,k,hk,by rw [pre_relabel,ep,eq,ez]⟩

theorem chart_rot (A : Automaton n α) {a : α} {j : ZMod n} (hr : ∀ x, A.δ a x = x+j)
    (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (v : ZMod n) (r : Bool) :
    (∀ x, (A.relabel (chart v r)).δ a x = x + (if r then -j else j)) ∧
    (∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-(if r then -j else j))^[k] x = y) := by
  constructor
  · intro x
    cases r <;> simp [relabel,chart,hr] <;> abel
  · intro x y
    obtain ⟨k,hk⟩ := ht (chart v r x) (chart v r y)
    refine ⟨k,?_⟩
    rw [back_steps] at hk ⊢
    cases r with
    | false =>
      change v+x-(k : ZMod n)*j = v+y at hk
      change x-(k : ZMod n)*j = y
      exact add_left_cancel (a := v) (by rw [← hk]; abel)
    | true =>
      change v-x-(k : ZMod n)*j = v-y at hk
      change x-(k : ZMod n)*(-j) = y
      exact sub_right_injective (b := v) (show v-(x-(k : ZMod n)*(-j)) = v-y by rw [← hk,mul_neg]; abel)

end Automaton
end CardosoSubsetSynchronization
namespace CardosoSubsetSynchronization

open Finset

variable {n : ℕ} [NeZero n] {α : Type*}

private theorem cast_ne_zero {k : ℕ} (hk : 0 < k) (hkn : k < n) : (k : ZMod n) ≠ 0 := by
  intro e
  have := natCast_inj_lt hkn (by omega : 0 < n) (by simpa using e)
  omega

private theorem cast_ne_last {k : ℕ} (hk : k+1 < n) : (k : ZMod n) ≠ -1 := by
  intro e
  apply cast_ne_zero (by omega : 0 < k+1) hk
  simp [Nat.cast_add,e]

namespace Automaton

/-- With zero the doubled state and its predecessor missing, the lifts of
1 through n-2 form a path of distinct adjacent points. Such a path cannot
turn back. This determines the entire letter, including its double fibre. -/
theorem normalized_shape (A : Automaton n α) (ho : A.WeaklyOriented) (b : α)
    (hn : 5 ≤ n) (prof : ∀ z, fibre (A.δ b) z = if z = -1 then 0 else if z = 0 then 2 else 1) :
    ∃ c d : ZMod n, (d=1 ∨ d = -1) ∧ ∀ z, A.δ b (c+d*z) = foldPoint z := by
  classical
  let f := A.δ b
  let lift (z : ZMod n) := if h : ∃ x, f x = z then Classical.choose h else 0
  have single (z : ZMod n) (h0 : z ≠ 0) (h1 : z ≠ -1) :
      pre f {z} = {lift z} ∧ f (lift z) = z := by
    have hcard : (pre f {z}).card = 1 := by simpa [fibre,f,h0,h1] using prof z
    obtain ⟨x,hx⟩ := card_eq_one.mp hcard
    have hz : f x = z := by
      have mem : x ∈ pre f {z} := by rw [hx]; simp
      simpa using mem
    have ex : ∃ x, f x = z := ⟨x,hz⟩
    have hL : f (lift z) = z := by simp only [lift,dif_pos ex]; exact Classical.choose_spec ex
    have hmem : lift z ∈ pre f {z} := by simpa using hL
    rw [hx,mem_singleton] at hmem
    exact ⟨by rw [hx,hmem],hL⟩
  have liftR (k : ℕ) (hk : 0<k) (hnk : k+1<n) : f (lift k) = (k : ZMod n) :=
    (single k (cast_ne_zero hk (by omega)) (cast_ne_last hnk)).2
  have unique' {z p : ZMod n} (z0 : z ≠ 0) (z1 : z ≠ -1) (hp : f p=z) :
      p=lift z := by
    have h : p ∈ pre f {z} := by simpa using hp
    rwa [(single z z0 z1).1,mem_singleton] at h
  have step (k : ℕ) (hk : 1≤k) (hkn : k+2<n) :
      lift ((k+1 : ℕ) : ZMod n) = lift k+1 ∨ lift ((k+1 : ℕ) : ZMod n) = lift k-1 := by
    let y := ((k+1 : ℕ) : ZMod n)
    have singleK := (single k (cast_ne_zero hk (by omega)) (cast_ne_last (by omega))).1
    have singleY := (single y (cast_ne_zero (by omega) (by omega)) (cast_ne_last (by omega))).1
    have ne : lift k ≠ lift y := by
      intro he
      have E := congrArg f he
      rw [liftR k hk (by omega),show f (lift y) = y from liftR _ (by omega) (by omega)] at E
      have H := natCast_inj_lt (by omega : k<n) (by omega : k+1<n) E
      omega
    have eq : pre f (interval (k : ZMod n) 2) = {lift k,lift y} := by
      have split : pre f (interval (k : ZMod n) 2) = pre f {(k : ZMod n)} ∪ pre f {y} := by
        ext p
        simp [y,interval_two,Nat.cast_add]
      rw [split,singleK,singleY]; simp
    obtain ⟨s,r,hr,e⟩ := ho b (k : ZMod n) 2 (by omega)
    change pre f (interval (k : ZMod n) 2) = interval s r at e
    rw [eq] at e
    have len := congrArg Finset.card e
    rw [interval_card s hr] at len
    have er : r=2 := by simpa [ne] using len.symm
    rw [er,interval_two] at e
    have hL : lift k ∈ ({s,s+1} : Finset _) := e ▸ (by simp)
    have hR : lift y ∈ ({s,s+1} : Finset _) := e ▸ (by simp)
    change lift y = lift k + 1 ∨ lift y = lift k - 1
    simp only [mem_insert,mem_singleton] at hL hR
    rcases hL with hL|hL <;> rcases hR with hR|hR <;> simp_all
  obtain ⟨d,hd,first⟩ : ∃ d : ZMod n, (d=1 ∨ d = -1) ∧
      lift ((1+1 : ℕ) : ZMod n) = lift (1 : ℕ) + d := by
    rcases step 1 (by decide) (by omega) with h|h
    · exact ⟨1,Or.inl rfl,h⟩
    · exact ⟨-1,Or.inr rfl,by simpa [sub_eq_add_neg] using h⟩
  let c := lift 1-d
  have chain (h : ℕ) (hh : h+3 < n) :
      lift ((h+2 : ℕ) : ZMod n) = lift ((h+1 : ℕ) : ZMod n)+d := by
    induction h with
    | zero => exact first
    | succ h ih =>
      have E := ih (by omega)
      have H := step (h+2) (by omega) (by omega)
      have ne : lift ((h+2+1 : ℕ) : ZMod n) ≠ lift ((h+1 : ℕ) : ZMod n) := by
        intro he
        have he' := congrArg f he
        rw [liftR _ (by omega) (by omega),liftR _ (by omega) (by omega)] at he'
        have dif := natCast_inj_lt (by omega : h+2+1<n) (by omega : h+1<n) he'
        omega
      change lift ((h+2+1 : ℕ) : ZMod n) = lift ((h+2 : ℕ) : ZMod n)+d
      rcases hd with rfl|rfl <;> rcases H with H|H <;> simp_all [sub_eq_add_neg,add_assoc]
  have loc (h : ℕ) (hh : h+2<n) :
      lift ((h+1 : ℕ) : ZMod n) = c+d*((h+1 : ℕ) : ZMod n) := by
    induction h with
    | zero => simp [c]
    | succ h ih =>
      change lift ((h+2 : ℕ) : ZMod n) = c+d*((h+2 : ℕ) : ZMod n)
      rw [chain h (by omega), ih (by omega)]
      push_cast; ring
  have mid (z : ZMod n) (z0 : z ≠ 0) (z1 : z ≠ -1) : lift z = c+d*z := by
    have hv := z.val_lt
    have hz : 0 < z.val := by
      by_contra! h
      have E : z.val = 0 := by omega
      have hh : (z.val : ZMod n) = 0 := by rw [E]; simp
      exact z0 (by simpa using hh)
    have last : z.val+1<n := by
      by_contra! h
      have E : z.val+1 = n := by omega
      have hh : (z : ZMod n)+1 = 0 := by
        have hh := congrArg (fun k : ℕ => (k : ZMod n)) E
        simpa using hh
      exact z1 (eq_neg_of_add_eq_zero_left hh)
    have H := loc (z.val-1) (by omega)
    simpa only [show z.val-1+1=z.val by omega,ZMod.natCast_zmod_val] using H
  have midF (z : ZMod n) (z0 : z ≠ 0) (z1 : z ≠ -1) : f (c+d*z) = z := by
    rw [← mid z z0 z1]
    exact (single z z0 z1).2
  have one : (1 : ZMod n) ≠ 0 := by simpa using cast_ne_zero (n := n) (by decide : 0<1) (by omega)
  have nz : (0 : ZMod n) ≠ -1 := by simpa using one
  refine ⟨c,d,hd,?_⟩
  intro z
  by_cases special : z=0 ∨ z = -1
  · let y := f (c+d*z)
    have y1 : y ≠ -1 := by
      intro eq
      have mem : (-1 : ZMod n) ∈ univ.image f := mem_image.mpr ⟨_,mem_univ _,eq⟩
      have zero : fibre f (-1) = 0 := by simp [f,prof]
      exact (fibre_zero_iff ..).mp zero mem
    have y0 : y = 0 := by
      by_contra yy
      have hi := unique' yy y1 (rfl : f (c+d*z) = y)
      rw [mid y yy y1] at hi
      have same : z=y := by rcases hd with rfl|rfl <;> simpa using add_left_cancel hi
      rcases special with h|h
      · exact yy (same ▸ h)
      · exact y1 (same ▸ h)
    change y = foldPoint z
    rcases special with h|h <;> simp [foldPoint,h,y0,nz]
  · push_neg at special
    simpa [foldPoint,special.2] using midF z special.1 special.2

end Automaton
end CardosoSubsetSynchronization
namespace CardosoSubsetSynchronization

open Finset
variable {n : ℕ} [NeZero n] {α : Type*}

namespace Automaton

private theorem normalized_bound (A : Automaton n α) {a b : α} {j c d : ZMod n}
    (hr : ∀ x, A.δ a x = x+j) (ht : ∀ x y, ∃ k : ℕ, (fun p : ZMod n => p-j)^[k] x = y)
    (hd : d = 1 ∨ d = -1) (hb : ∀ z, A.δ b (c+d*z) = foldPoint z)
    (hn : 5 ≤ n) (j1 : j ≠ 1) (S : Finset (ZMod n)) (hm : 3 ≤ S.card) :
    ∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S := by
  let m := S.card
  let g := (n-1)/m
  let k := n-g-2
  have hmn : m ≤ n := by simpa [m,ZMod.card] using card_le_univ S
  have h3m : 3 ≤ m := hm
  have hmg : m*g ≤ n-1 := by simpa [g,Nat.mul_comm] using Nat.div_mul_le_self (n-1) m
  have h3g := Nat.mul_le_mul_right g h3m
  have hL : 2+k+g = n := by dsimp [k]; omega
  have hk : 2+k ≤ n := by omega
  have nj : j ≠ 0 := by
    intro e
    obtain ⟨i,hi⟩ := ht 0 1
    rw [back_steps,e] at hi
    have one : (1 : ZMod n) ≠ 0 := by simpa using cast_ne_zero (n := n) (by decide : 0<1) (by omega)
    exact one (by simpa using hi.symm)
  obtain ⟨w,hw,hS⟩ := A.align_subset hr ht S hk
    (by change m*(n-(2+k)) < n; rw [show n-(2+k) = g by omega]; omega)
    (A.normalized_growth hr ht hd hb (by omega) nj j1 k hk)
  rw [show n-(2+k) = g by omega] at hw
  change w.length ≤ 2+(n-1)*k+m*g at hw
  have H := closing_budget n m h3m hmn
  change 2+((n:ℤ)-1)*((n:ℤ)-g-2)+m*g+((m:ℤ)-3) ≤ bound n m at H
  have hK : ((n:ℤ)-g-2) = (k : ℤ) := by omega
  rw [hK] at H
  zify [show 1 ≤ n by omega] at hw
  have low : (w.length : ℤ) ≤ B n m := by
    rw [cast_B (by omega) hmn]
    have h3 : (3 : ℤ) ≤ m := by exact_mod_cast h3m
    linarith only [H,hw,h3]
  exact ⟨w,by exact_mod_cast low,hS⟩

/-- Cardoso's bound for every nonempty specified subset of a synchronizing
weakly oriented circular automaton. There is no restriction on the jump,
the rank of a letter, the alphabet, or the number of states other than
nonemptiness of the state space. -/
theorem weaklyOrientedCircular_bound (A : Automaton n α)
    (hs : A.Synchronizing) (hc : A.Circular) (ho : A.WeaklyOriented)
    (S : Finset (ZMod n)) (hne : S.Nonempty) :
    ∃ w : List α, w.length ≤ B n S.card ∧ A.Synchronizes w S := by
  classical
  by_contra no
  obtain ⟨hn,hm,_,a,b,j,u,v,hr,ht,nj1,njm,_,adj,prof⟩ :=
    A.residual_of_no_short_word hs hc ho S hne no
  obtain ⟨r,pu⟩ : ∃ r : Bool, chart v r (-1) = u := by
    rcases adj with H|H
    · refine ⟨false,?_⟩
      change v+(-1) = u
      rw [← H]; abel
    · refine ⟨true,?_⟩
      change v-(-1) = u
      rw [H]; abel
  let π := chart v r
  have pv : π 0 = v := by cases r <;> simp [π,chart]
  let A' := A.relabel π
  have fprof (z : ZMod n) :
      fibre (A'.δ b) z = if z = -1 then 0 else if z=0 then 2 else 1 := by
    rw [show fibre (A'.δ b) z = fibre (A.δ b) (π z) from A.fibre_relabel π b z,prof]
    have E1 : π z = u ↔ z = -1 := by rw [← pu]; exact π.injective.eq_iff
    have E0 : π z = v ↔ z = 0 := by rw [← pv]; exact π.injective.eq_iff
    simp only [E1,E0]
  obtain ⟨c,d,hd,hb⟩ := A'.normalized_shape (A.chart_oriented ho v r) b hn fprof
  obtain ⟨hr',ht'⟩ := A.chart_rot hr ht v r
  have J : (if r then -j else j) ≠ 1 := by
    cases r with
    | false => exact nj1
    | true =>
      intro e
      apply njm
      simpa using congrArg Neg.neg e
  let T := S.image π.symm
  have card : T.card = S.card := card_image_of_injective _ π.symm.injective
  obtain ⟨w,hw,hsw⟩ := A'.normalized_bound hr' ht' hd hb hn J T (by omega)
  exact no ⟨w,card ▸ hw,A.sync_of_relabel π hsw⟩

end Automaton
end CardosoSubsetSynchronization
