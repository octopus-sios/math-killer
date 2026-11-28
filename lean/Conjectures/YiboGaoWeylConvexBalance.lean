import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Equality in the classical fully commutative heap strip model

The first three lemmas give the local calculation used below.
After the first median turn the first two steps cannot both be increments.
In a connected strip the third layer then has states 0,1,2. The fourth layer
has positive continuation counts at 1 and 2, and may be truncated at 0 or 3.
The counts below sum actual four-step paths, with arbitrary continuation
weights. The main theorem `classicalStripClassification` removes all bounds
on the length of the strip and on the size of its terminal block. It does not
assume any intermediate continuation counts.
-/

namespace YiboGaoWeylConvexBalance

/-- The first two median tail bounds force equal continuations at 0 and 1;
there can be no continuation at 2. The prefix multiplicities are 1,2,1. -/
theorem secondLayerForced (r₀ r₁ r₂ N : ℕ)
    (hN : N = r₀ + 2 * r₁ + r₂)
    (h₁ : 3 * (r₁ + r₂) ≤ N) (h₂ : 3 * r₀ ≤ N) :
    r₂ = 0 ∧ r₀ = r₁ ∧ N = 3 * r₀ := by
  omega

structure Weights where
  w₀ : ℕ
  w₁ : ℕ
  w₂ : ℕ
  w₃ : ℕ

def weightAt (u : Weights) : ℕ → ℕ
  | 0 => u.w₀
  | 1 => u.w₁
  | 2 => u.w₂
  | 3 => u.w₃
  | _ => 0

private def stepSum (f : ℕ → ℕ) : ℕ := f 0 + f 1

/-- Weight of a selected event on four 0/1 steps. The event observes the
states at times 1, 2 and 4. The allowed interval at time 2 is [0,1]. -/
def countPaths (u : Weights) (test : ℕ → ℕ → ℕ → Bool) : ℕ :=
  stepSum fun a => stepSum fun b =>
    if a + b ≤ 1 then
      stepSum fun c => stepSum fun d =>
        if test a (a + b) (a + b + c + d) then weightAt u (a + b + c + d) else 0
    else 0

/-- For log-concave fourth-layer continuation weights, the two tail
inequalities at an initial turn force a *strictly* middle-third cut. -/
theorem fourColumnBalanced (u : Weights)
    (h₁ : 0 < u.w₁) (h₂ : 0 < u.w₂) (hlc : u.w₀ * u.w₂ ≤ u.w₁ * u.w₁)
    (first : 3 * countPaths u (fun a _ _ => a == 1) ≤ countPaths u (fun _ _ _ => true))
    (second : 3 * countPaths u (fun _ j _ => j == 0) ≤ countPaths u (fun _ _ _ => true)) :
    countPaths u (fun _ _ _ => true) < 3 * countPaths u (fun _ _ k => decide (k ≤ 1)) ∧
    3 * countPaths u (fun _ _ k => decide (k ≤ 1)) < 2 * countPaths u (fun _ _ _ => true) := by
  norm_num [countPaths, stepSum, weightAt] at first second ⊢
  have hsmall : u.w₂ < 2 * u.w₁ := by
    by_contra! hlarge
    have ha : u.w₁ ≤ u.w₀ := by omega
    have hb := Nat.mul_le_mul ha hlarge
    have hc : u.w₁ * u.w₁ < u.w₁ * (2 * u.w₁) :=
      Nat.mul_lt_mul_of_pos_left (by omega) h₁
    exact (not_lt_of_ge (hb.trans hlc)) hc
  omega

/-- Once a positive free-prefix count survives the peak marginal test,
at most eight binary prefixes force at most five ideals in the block. -/
theorem smallPeak (A B F M : ℕ) (hf : 0 < F) (prefixes : A + B + F ≤ 8)
    (gap : 3 * (M - 1) * F ≤ A + B + M * F) : M ≤ 5 := by
  by_contra! h
  have hM : M = (M - 1) + 1 := by omega
  have he : M * F = (M - 1) * F + F := by
    conv_lhs => rw [hM, Nat.add_mul, Nat.one_mul]
  have hg : 5 * F ≤ (M - 1) * F := Nat.mul_le_mul_right F (by omega)
  rw [Nat.mul_assoc] at gap
  omega

end YiboGaoWeylConvexBalance
namespace YiboGaoWeylConvexBalance

/-! ## Binary strips of arbitrary length

At time `t` retain the integer interval `[lo t, hi t]`; the step adds 0
or 1. All counts below are computed from the walls, not supplied as data.
The prefix functional sums a payoff over all admissible prefixes. -/

structure Walls where
  lo : ℕ → ℕ
  hi : ℕ → ℕ

namespace Walls

structure Valid (S : Walls) (q : ℕ) : Prop where
  lo_zero : S.lo 0 = 0
  hi_zero : S.hi 0 = 0
  step_lo : ∀ t < q, S.lo t ≤ S.lo (t+1) ∧ S.lo (t+1) ≤ S.lo t + 1
  step_hi : ∀ t < q, S.hi t ≤ S.hi (t+1) ∧ S.hi (t+1) ≤ S.hi t + 1
  wide : ∀ t, 0 < t → t ≤ q → S.lo t < S.hi t

variable {S : Walls} {q : ℕ}

private theorem bounds (v : S.Valid q) {t : ℕ} (ht : t ≤ q) :
    S.lo t ≤ S.hi t ∧ S.hi t ≤ t := by
  induction t with
  | zero => simp [v.lo_zero, v.hi_zero]
  | succ t ih =>
    have := ih (by omega)
    have := v.step_hi t (by omega)
    have := v.wide (t+1) (by omega) ht
    omega

private theorem firstBounds (v : S.Valid q) (ht : 1 ≤ q) :
    S.lo 1 = 0 ∧ S.hi 1 = 1 := by
  have := bounds v ht
  have := v.wide 1 (by decide) ht
  omega

abbrev Row := ℕ → ℕ

def clip (S : Walls) (t : ℕ) (w : Row) (i : ℕ) : ℕ :=
  if S.lo t ≤ i ∧ i ≤ S.hi t then w i else 0

def pascal (w : Row) (i : ℕ) : ℕ := w i + w (i+1)

def front (S : Walls) : ℕ → Row → ℕ
  | 0, w => w 0
  | t+1, w => S.front t (pascal (S.clip (t+1) w))

private theorem front_congr (v : S.Valid q) {t : ℕ} (ht : t ≤ q) {u w : Row}
    (h : ∀ i, S.lo t ≤ i → i ≤ S.hi t → u i = w i) :
    S.front t u = S.front t w := by
  cases t with
  | zero => exact h 0 (by simp [v.lo_zero]) (by omega)
  | succ t =>
    have eq : S.clip (t+1) u = S.clip (t+1) w := by
      funext i; simp only [clip]; split <;> first | rfl | exact h i ‹_ ∧ _›.1 ‹_ ∧ _›.2
    simp only [front, eq]

private theorem front_clip (v : S.Valid q) {t : ℕ} (ht : t ≤ q) (w : Row) :
    S.front t (S.clip t w) = S.front t w :=
  front_congr v ht fun _ a b => ite_eq_left ⟨a,b⟩

private theorem front_add (S : Walls) (t : ℕ) (u w : Row) :
    S.front t (fun i => u i + w i) = S.front t u + S.front t w := by
  induction t generalizing u w with
  | zero => rfl
  | succ t ih =>
    simp only [front, ← ih]; congr 1; funext i
    simp [pascal, clip]; split_ifs <;> omega

private theorem front_scale (S : Walls) (t c : ℕ) (w : Row) :
    S.front t (fun i => c * w i) = c * S.front t w := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    simp only [front, ← ih]; congr 1; funext i
    simp [pascal, clip, Nat.mul_add]

private theorem front_mono (S : Walls) (t : ℕ) {u w : Row} (h : ∀ i, u i ≤ w i) :
    S.front t u ≤ S.front t w := by
  induction t generalizing u w with
  | zero => exact h 0
  | succ t ih =>
    apply ih; intro i; unfold pascal clip
    split_ifs <;> have := h i <;> have := h (i+1) <;> omega

private theorem front_one_le (S : Walls) (t : ℕ) :
    S.front t (fun _ => 1) ≤ 2^t := by
  induction t with
  | zero => simp [front]
  | succ t ih =>
    calc
      _ ≤ S.front t (fun _ => 2 * 1) := by
        rw [front]; apply S.front_mono; intro i; simp [pascal, clip]; split_ifs <;> decide
      _ = 2 * S.front t (fun _ => 1) := front_scale ..
      _ ≤ 2^(t+1) := by rw [pow_succ]; omega

/-- The backwards recursion includes the mask at the *current* layer. -/
def suffixAux (S : Walls) (w : Row) : ℕ → ℕ → Row
  | 0, t => S.clip t w
  | n+1, t => S.clip t (pascal (S.suffixAux w n (t+1)))

def suffix (S : Walls) (q : ℕ) (w : Row) (t : ℕ) := S.suffixAux w (q-t) t

private theorem suffix_step (S : Walls) {t q : ℕ} (ht : t < q) (w : Row) :
    S.suffix q w t = S.clip t (pascal (S.suffix q w (t+1))) := by
  unfold suffix
  rw [show q-t = (q-(t+1))+1 by omega, suffixAux]

private theorem suffix_end (S : Walls) (q : ℕ) (w : Row) :
    S.suffix q w q = S.clip q w := by simp [suffix, suffixAux]

private theorem front_suffix (v : S.Valid q) (w : Row) {t : ℕ} (ht : t ≤ q) :
    S.front t (S.suffix q w t) = S.front q w := by
  induction d : q-t generalizing t with
  | zero =>
    have : t=q := by omega
    subst t; rw [suffix_end, front_clip v (by omega)]
  | succ d ih =>
    have hlt : t<q := by omega
    rw [suffix_step _ hlt, front_clip v ht]
    rw [← ih (t := t+1) (by omega) (by omega), front]
    congr 1
    apply congrArg pascal
    funext i; unfold suffix; cases q-(t+1) <;> simp only [suffixAux, clip] <;> split_ifs <;> rfl

private theorem suffix_support (v : S.Valid q) (w : Row)
    (endPos : ∀ i, S.lo q ≤ i → i ≤ S.hi q → 0 < w i)
    {t : ℕ} (ht : t ≤ q) (i : ℕ) :
    0 < S.suffix q w t i ↔ S.lo t ≤ i ∧ i ≤ S.hi t := by
  induction d : q-t generalizing t i with
  | zero =>
    have : t=q := by omega
    subst t; rw [suffix_end]; unfold clip
    split_ifs with h
    · exact iff_of_true (endPos i h.1 h.2) h
    · simp_all
  | succ d ih =>
    have hs : t<q := by omega
    rw [suffix_step S hs]; unfold clip pascal
    split_ifs with h
    · have a := v.step_lo t hs
      have b := v.step_hi t hs
      have c := (ih (t := t+1) (by omega) i (by omega))
      have e := (ih (t := t+1) (by omega) (i+1) (by omega))
      have := bounds v (show t+1 ≤ q by omega)
      omega
    · simp_all

private theorem front_pos (v : S.Valid q) {t i : ℕ} (ht : t ≤ q)
    (hl : S.lo t ≤ i) (hh : i ≤ S.hi t) {w : Row} (hw : 0 < w i) :
    0 < S.front t w := by
  induction t generalizing i w with
  | zero =>
    have : i=0 := by simpa [v.hi_zero] using hh
    simpa [front, this] using hw
  | succ t ih =>
    have a := v.step_lo t (by omega)
    have b := v.step_hi t (by omega)
    have c := bounds v (show t ≤ q by omega)
    simp only [front]
    by_cases h : i ≤ S.hi t
    · apply ih (i := i) (by omega) (by omega) h
      unfold pascal; rw [show S.clip (t+1) w i = w i from ite_eq_left ⟨hl,hh⟩]; omega
    · have he : S.hi t + 1 = i := by omega
      apply ih (i := S.hi t) (by omega) c.1 (by omega)
      unfold pascal; rw [he, show S.clip (t+1) w i = w i from ite_eq_left ⟨hl,hh⟩]; omega

/-- The all-zero path and the paths with a single increment. -/
private theorem front_lower (v : S.Valid q) {t : ℕ} (ht : t ≤ q) (hz : S.lo t = 0)
    (w : Row) : w 0 + t * w 1 ≤ S.front t w := by
  induction t generalizing w with
  | zero => simp [front]
  | succ t ih =>
    have a := v.step_lo t (by omega)
    have b := v.wide (t+1) (by omega) ht
    let g := pascal (S.clip (t+1) w)
    have h := ih (by omega) (by omega) g
    have g0 : g 0 = w 0 + w 1 := by
      simp [g, pascal, clip, hz, show 1 ≤ S.hi (t+1) by omega]
    have g1 : w 1 ≤ g 1 := by
      simp [g, pascal, clip, hz, show 1 ≤ S.hi (t+1) by omega]
    have hm := Nat.mul_le_mul_left t g1
    change _ ≤ S.front t g
    rw [g0] at h; rw [Nat.succ_mul]; omega

private theorem front_zero_state (v : S.Valid q) {t : ℕ} (ht : t ≤ q) (a : ℕ) :
    S.front t (fun i => if i = 0 then a else 0) = if S.lo t = 0 then a else 0 := by
  induction t generalizing a with
  | zero => simp [front, v.lo_zero]
  | succ t ih =>
    have h := v.step_lo t (by omega)
    let b := if S.lo (t+1) = 0 then a else 0
    have eq : pascal (S.clip (t+1) (fun i => if i = 0 then a else 0)) =
        fun i => if i = 0 then b else 0 := by
      funext i; cases i <;> simp [b, pascal, clip]
    rw [front, eq, ih (by omega)]
    dsimp [b]; split_ifs <;> omega

def cut (S : Walls) (q : ℕ) (w : Row) (t k : ℕ) : ℕ :=
  S.front t fun i => if i ≤ k then S.suffix q w t i else 0

def Outside (N c : ℕ) : Prop := 3*c ≤ N ∨ 2*N ≤ 3*c

def Gap (S : Walls) (q : ℕ) (w : Row) : Prop :=
  ∀ t ≤ q, ∀ k, Outside (S.front q w) (S.cut q w t k)

private theorem cut_zero (v : S.Valid q) {t : ℕ} (ht : t ≤ q) (w : Row) :
    S.cut q w t 0 = S.suffix q w t 0 := by
  unfold cut
  rw [show (fun i => if i ≤ 0 then S.suffix q w t i else 0) =
      (fun i => if i = 0 then S.suffix q w t 0 else 0) by
        funext i; cases i <;> simp, front_zero_state v ht]
  split_ifs with h
  · rfl
  · unfold suffix; cases q-t <;> simp [suffixAux, clip, h]

/-- The ordered cross-product form includes log-concavity and permits
zero boundary values; it is stable under both operations in the recursion. -/
def Cross (w : Row) : Prop := ∀ i j, i ≤ j → w i * w (j+1) ≤ w (i+1) * w j

private theorem cross_pascal {w : Row} (h : Cross w) : Cross (pascal w) := by
  intro i j hij
  rcases hij.eq_or_lt with he|hl
  · subst j; simp [Nat.mul_comm]
  · have a := h i j (by omega)
    have b := h i (j+1) (by omega)
    have c := h (i+1) j (by omega)
    have d := h (i+1) (j+1) (by omega)
    unfold pascal; nlinarith only [a,b,c,d]

private theorem cross_clip (S : Walls) (t : ℕ) {w : Row} (h : Cross w) :
    Cross (S.clip t w) := by
  intro i j hij; simp only [clip]
  split_ifs <;> first | apply h i j hij | (simp_all; done) | omega

private theorem cross_suffix (S : Walls) (q : ℕ) (w : Row) (hc : Cross (S.clip q w))
    {t : ℕ} (ht : t ≤ q) : Cross (S.suffix q w t) := by
  induction d : q-t generalizing t with
  | zero =>
    have : t=q := by omega
    subst t; simpa [suffix_end] using hc
  | succ d ih =>
    rw [suffix_step S (show t<q by omega)]
    exact cross_clip _ _ (cross_pascal (ih (t := t+1) (by omega) (by omega)))

end Walls
end YiboGaoWeylConvexBalance
namespace YiboGaoWeylConvexBalance.Walls

variable {S : Walls} {q : ℕ} {w : Row}

/-- For four or more regular columns, if the lower endpoint is the majority
at the first cut, it remains the majority all the way to the terminal payoff.
No median, prefix multiplicity or internal log-concavity is assumed. -/
theorem straight_of_first (v : S.Valid q) (hq : 4 ≤ q)
    (endPos : ∀ i, S.lo q ≤ i → i ≤ S.hi q → 0 < w i)
    (lc : Cross (S.clip q w)) (gap : S.Gap q w)
    (first : 2 * S.front q w ≤ 3 * S.cut q w 1 0) :
    ∀ t, 1 ≤ t → t ≤ q → 2 * S.front q w ≤ 3 * S.suffix q w t 0 := by
  let N := S.front q w
  let r := S.suffix q w
  have pos : 0 < N := front_pos v (le_refl q) (i := S.lo q) (le_refl _)
    (bounds v (le_refl _)).1 (endPos _ (le_refl _) (bounds v (le_refl _)).1)
  have supp (t i : ℕ) (h : t ≤ q) : 0 < r t i ↔ S.lo t ≤ i ∧ i ≤ S.hi t :=
    suffix_support v w endPos h i
  have step (t i : ℕ) (h : t<q) (a : S.lo t ≤ i) (b : i ≤ S.hi t) :
      r t i = r (t+1) i + r (t+1) (i+1) := by
    simp [r, suffix_step S h, clip, a,b, pascal]
  have first' : 2*N ≤ 3*r 1 0 := by simpa only [cut_zero v (show 1≤q by omega)] using first
  have dich (t : ℕ) (h : t ≤ q) : Outside N (r t 0) := by
    simpa only [cut_zero v h] using gap t h 0
  obtain ⟨l₁,h₁⟩ := firstBounds v (show 1≤q by omega)
  have init (u : Row) : S.front 1 u = u 0 + u 1 := by
    simp [front, pascal, clip, l₁,h₁]
  have tot : N = r 1 0 + r 1 1 := by
    rw [← init]; exact (front_suffix v w (by omega)).symm
  have e₀ := step 1 0 (by omega) (by omega) (by omega)
  have e₁ := step 1 1 (by omega) (by omega) (by omega)
  norm_num1 at e₀ e₁
  have second : 2*N ≤ 3*r 2 0 := by
    by_contra h
    have d := dich 2 (by omega)
    unfold Outside at d
    obtain ⟨rr,eq,n3⟩ := secondLayerForced (r 2 0) (r 2 1) (r 2 2) N
      (by omega) (by omega) (by omega)
    have b₂ := bounds v (show 2≤q by omega)
    have a₀ := supp 2 0 (by omega); have a₂ := supp 2 2 (by omega)
    have w₂ := v.wide 2 (by omega) (by omega)
    have l₂ : S.lo 2 = 0 := by omega
    have h₂ : S.hi 2 = 1 := by omega
    have e₂ := step 2 0 (by omega) (by omega) (by omega)
    have e₃ := step 2 1 (by omega) (by omega) (by omega)
    norm_num1 at e₂ e₃
    have s₀ := supp 3 0 (by omega); have s₂ := supp 3 2 (by omega)
    have l₂₃ := v.step_lo 2 (by omega); have h₂₃ := v.step_hi 2 (by omega)
    have w₃ := v.wide 3 (by omega) (by omega)
    norm_num1 at l₂₃ h₂₃
    have l₃ : S.lo 3 = 0 := by omega
    have h₃ : S.hi 3 = 2 := by omega
    have e₄ := step 3 0 (by omega) (by omega) (by omega)
    have e₅ := step 3 1 (by omega) (by omega) (by omega)
    have e₆ := step 3 2 (by omega) (by omega) (by omega)
    let u : Weights := ⟨r 4 0, r 4 1, r 4 2, r 4 3⟩
    have a := v.step_lo 3 (by omega); have b := v.step_hi 3 (by omega)
    norm_num1 at a b e₄ e₅ e₆
    have mid := fourColumnBalanced u
      ((supp 4 1 (by omega)).2 (by constructor <;> omega))
      ((supp 4 2 (by omega)).2 (by constructor <;> omega))
      (cross_suffix S q w lc (show 4 ≤ q by omega) 0 1 (by decide))
      (by norm_num [u, countPaths, stepSum, weightAt]; omega)
      (by norm_num [u, countPaths, stepSum, weightAt]; omega)
    norm_num [countPaths, stepSum, weightAt, u] at mid
    have four (f : Row) :
        S.front 4 f = S.clip 4 f 0 + 4*S.clip 4 f 1 + 5*S.clip 4 f 2 + 2*S.clip 4 f 3 := by
      change S.front 3 (pascal (S.clip 4 f)) = _
      generalize S.clip 4 f = g
      norm_num [front, pascal, clip, l₁,h₁,l₂,h₂,l₃,h₃]; omega
    have mc (i : ℕ) : S.clip 4 (fun j => if j ≤ 1 then r 4 j else 0) i =
        if i ≤ 1 then r 4 i else 0 := by
      have hh := supp 4 i (by omega)
      dsimp only [clip]; split_ifs <;> first | rfl | omega
    have event : S.cut q w 4 1 = r 4 0 + 4*r 4 1 := by
      change S.front 4 (fun j => if j ≤ 1 then r 4 j else 0) = _
      rw [four]; norm_num [mc]
    have bad := gap 4 (by omega) 1
    change Outside N _ at bad
    rw [event] at bad; unfold Outside at bad
    omega
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact fun _ => first'
  | succ t ht ih =>
    intro hq'
    by_cases ht' : t=1
    · subst t; exact second
    have h := ih (by omega)
    change 2*N ≤ 3*r t 0 at h
    have h0 := supp t 0 (by omega)
    have l : S.lo t = 0 := by omega
    have b := v.wide t (by omega) (by omega)
    have f := front_lower v (show t ≤ q by omega) l (r t)
    have ff : S.front t (r t) = N := front_suffix v _ (by omega)
    have z := step t 0 (by omega) (by omega) (by omega)
    have o := step t 1 (by omega) (by omega) (by omega)
    norm_num1 at z o
    have m : 2 * r t 1 ≤ t * r t 1 := Nat.mul_le_mul_right _ (by omega)
    have d := dich (t+1) hq'
    change 2*N ≤ 3*r (t+1) 0
    unfold Outside at d; omega

end YiboGaoWeylConvexBalance.Walls
namespace YiboGaoWeylConvexBalance.Walls

/-- Reflect a path by replacing its state at time `t` by `t-i`. -/
def flip (S : Walls) : Walls := ⟨fun t => t-S.hi t, fun t => t-S.lo t⟩

variable {S : Walls} {q t : ℕ}

private theorem valid_flip (v : S.Valid q) : S.flip.Valid q := by
  constructor
  · simp [flip]
  · simp [flip]
  · intro t h; have := v.step_hi t h; dsimp [flip]; omega
  · intro t h; have := v.step_lo t h; dsimp [flip]; omega
  · intro t ht h; have := v.wide t ht h; have := bounds v h; dsimp [flip]; omega

private theorem clip_flip (v : S.Valid q) (ht : t ≤ q) {u w : Row}
    (hw : ∀ i ≤ t, u (t-i) = w i) (i : ℕ) (hi : i ≤ t) :
    S.flip.clip t u (t-i) = S.clip t w i := by
  have := bounds v ht
  have hc : (t-S.hi t ≤ t-i ∧ t-i ≤ t-S.lo t) ↔ (S.lo t ≤ i ∧ i ≤ S.hi t) := by omega
  simp only [clip, flip, hc, hw i hi]

private theorem pascal_flip {u w : Row} (h : ∀ i ≤ t+1, u (t+1-i) = w i)
    (i : ℕ) (hi : i ≤ t) : pascal u (t-i) = pascal w i := by
  have a := h i (by omega)
  have b := h (i+1) (by omega)
  rw [show t+1-i=t-i+1 by omega] at a
  rw [show t+1-(i+1)=t-i by omega] at b
  simp [pascal, a,b, Nat.add_comm]

private theorem front_flip (v : S.Valid q) (ht : t ≤ q) {u w : Row}
    (h : ∀ i ≤ t, u (t-i) = w i) : S.flip.front t u = S.front t w := by
  induction t generalizing u w with
  | zero => exact h 0 (by omega)
  | succ t ih =>
    simp only [front]
    exact ih (by omega) (pascal_flip (clip_flip v ht h))

private theorem suffix_flip (v : S.Valid q) {u w : Row} (hw : ∀ i ≤ q, u (q-i) = w i)
    (ht : t ≤ q) : ∀ i ≤ t, S.flip.suffix q u t (t-i) = S.suffix q w t i := by
  induction d : q-t generalizing t with
  | zero =>
    have e : t=q := by omega
    subst t; simp only [suffix_end]; exact clip_flip v ht hw
  | succ d ih =>
    have h : t < q := by omega
    rw [suffix_step _ h, suffix_step _ h w]
    exact clip_flip v ht (pascal_flip (ih (t := t+1) (by omega) (by omega)))

private theorem cut_flip (v : S.Valid q) {u w : Row} (hw : ∀ i ≤ q, u (q-i) = w i)
    (ht : t ≤ q) {k : ℕ} (hk : k < t) :
    S.flip.cut q u t k + S.cut q w t (t-k-1) = S.front q w := by
  have he : S.flip.cut q u t k = S.front t (fun i => if t-i ≤ k then S.suffix q w t i else 0) := by
    apply front_flip v ht
    intro i hi; split_ifs <;> first | rfl | exact suffix_flip v hw ht i hi
  rw [he, cut, ← front_add, ← front_suffix v w ht]
  apply front_congr v ht
  intro i hl hh
  have := bounds v ht
  split_ifs <;> omega

private theorem gap_flip (v : S.Valid q) {u w : Row} (hw : ∀ i ≤ q, u (q-i) = w i)
    (hg : S.Gap q w) : S.flip.Gap q u := by
  intro t ht k
  rw [front_flip v (le_refl _) hw]
  by_cases hk : k<t
  · have h := cut_flip v hw ht hk
    have g := hg t ht (t-k-1)
    unfold Outside at *; omega
  · have f : S.flip.cut q u t k = S.flip.front q u := by
      rw [← front_suffix (valid_flip v) u ht]
      apply front_congr (valid_flip v) ht
      intro i hl hh; have := bounds (valid_flip v) ht
      simp [show i ≤ k by omega]
    rw [f, front_flip v (le_refl _) hw]; right; omega

end YiboGaoWeylConvexBalance.Walls

namespace YiboGaoWeylConvexBalance

/-- `chain a f` is the chain on `2a+3` points; `fork a f` has two
incomparable twins between chains of length `a`. The terminal gap is `f`. -/
inductive Cap where
  | plain
  | chain (a f : ℕ)
  | fork (a f : ℕ)
deriving DecidableEq, Repr

namespace Cap

open Walls

def free : Cap → ℕ
  | .plain => 0
  | .chain _ f | .fork _ f => f

def ideals : Cap → ℕ
  | .plain => 1
  | .chain a _ | .fork a _ => 2*a+4

/-- Membership counts realized by the individual block points. -/
def HasCount : Cap → ℕ → Prop
  | .plain, _ => False
  | .chain a _, d => 1 ≤ d ∧ d ≤ 2*a+3
  | .fork a _, d => (1 ≤ d ∧ d ≤ a) ∨ d = a+2 ∨ (a+4 ≤ d ∧ d ≤ 2*a+3)

def weight (b : Cap) (i : ℕ) : ℕ := if i=b.free then b.ideals else 1

/-- Payoff for membership of a block point with local ideal count `d`. -/
def member (b : Cap) (d : ℕ) (i : ℕ) : ℕ :=
  if i = b.free then d else if b.free < i then 1 else 0

def Fits (b : Cap) (S : Walls) (q : ℕ) : Prop := b = .plain ∨
  (S.lo q ≤ b.free ∧ b.free ≤ S.hi q ∧ b.free ≤ S.lo q + 1 ∧ S.hi q ≤ b.free+1)

def Gap (b : Cap) (S : Walls) (q : ℕ) : Prop :=
  ∀ d, b.HasCount d → Outside (S.front q b.weight) (S.front q (b.member d))

def flip (q : ℕ) : Cap → Cap
  | .plain => .plain
  | .chain a f => .chain a (q-f)
  | .fork a f => .fork a (q-f)

private theorem weight_pos (b : Cap) (i : ℕ) : 0 < b.weight i := by
  unfold weight; split <;> cases b <;> simp [ideals]

private theorem cross_weight {S : Walls} {b : Cap} {q : ℕ} (hf : b.Fits S q) :
    Cross (S.clip q b.weight) := by
  rcases hf with rfl|⟨a,c,d,e⟩
  · apply cross_clip
    intro i j h; simp only [weight, ideals, ite_self, le_refl]
  intro i j hij
  by_cases eq : i=j
  · subst j; rw [Nat.mul_comm]
  by_cases hl : S.lo q ≤ i ∧ i ≤ S.hi q
  · by_cases hh : S.lo q ≤ j+1 ∧ j+1 ≤ S.hi q
    · have e₁ : i+1 = b.free := by omega
      have e₂ : j = b.free := by omega
      have h₁ : i ≠ b.free := by omega
      have h₂ : j+1 ≠ b.free := by omega
      have hj : S.lo q ≤ b.free ∧ b.free ≤ S.hi q := ⟨a,c⟩
      have p : 1 ≤ b.ideals := by cases b <;> simp [ideals]
      have pp := Nat.mul_le_mul p p
      simp only [clip, hl, ite_true, e₁,e₂, hj, weight]
      simp_all
    · simp [clip, hh]
  · simp [clip, hl]

private theorem fits_flip {S : Walls} {b : Cap} {q : ℕ} (v : S.Valid q) (hf : b.Fits S q) :
    (b.flip q).Fits S.flip q := by
  rcases hf with rfl|⟨a,c,d,e⟩
  · exact Or.inl rfl
  have := bounds v (le_refl q)
  cases b <;> simp_all [Fits, flip, Walls.flip, free] <;> omega

private theorem weight_flip {S : Walls} {b : Cap} {q : ℕ} (v : S.Valid q) (hf : b.Fits S q) :
    ∀ i ≤ q, (b.flip q).weight (q-i) = b.weight i := by
  intro i hi
  rcases hf with rfl|⟨a,c,d,e⟩
  · by_cases he : q-i = plain.free <;> simp [weight, flip, ideals, he]
  have := bounds v (le_refl q)
  have fbound : b.free ≤ q := by omega
  cases b with
  | plain => by_cases he : q-i = plain.free <;> simp [weight, flip, ideals, he]
  | chain a f | fork a f =>
    simp only [flip, weight, ideals, free] at *
    by_cases he : i=f
    · subst i; simp
    · have he' : q-i ≠ q-f := by omega
      simp [he,he']

private theorem gap_flip_cap {S : Walls} {b : Cap} {q : ℕ} (v : S.Valid q) (hf : b.Fits S q)
    (hg : b.Gap S q) : (b.flip q).Gap S.flip q := by
  intro d hd
  rw [front_flip v (le_refl _) (weight_flip v hf)]
  have hd' : b.HasCount (b.ideals-d) := by
    cases b <;> simp_all [flip, HasCount, ideals] <;> omega
  have h := hg _ hd'
  have rev : S.flip.front q ((b.flip q).member d) =
      S.front q (fun i => (b.flip q).member d (q-i)) :=
    front_flip v (le_refl _) (fun _ _ => rfl)
  have sum : S.flip.front q ((b.flip q).member d) + S.front q (b.member (b.ideals-d)) =
      S.front q b.weight := by
    rw [rev, ← front_add]
    apply front_congr v (le_refl _)
    intro i hl hh; have := bounds v (le_refl q)
    rcases hf with rfl|⟨a,c,_,_⟩
    · contradiction
    cases b with
    | plain => contradiction
    | chain a f | fork a f =>
      simp only [flip, HasCount, ideals, member, weight, free] at *
      rcases lt_trichotomy i f with h|h|h
      · have h₁ : q-f < q-i := by omega
        simp [h.ne, h₁.ne', h₁, h.not_gt]
      · subst i; simp; omega
      · have h₁ : q-i < q-f := by omega
        simp [h.ne', h₁.ne, h₁.not_gt, h]
  unfold Outside at *; omega

end Cap
end YiboGaoWeylConvexBalance
namespace YiboGaoWeylConvexBalance

open Walls

variable {S : Walls} {q : ℕ} {b : Cap}

/-- The endpoint of a straight majority cannot carry the requisite weight.
In the free state a block has a point in *exactly half* its ideals. At the
only possible tie the count 1 is forbidden, unless the block is tiny; in
that case the single-increment paths already have too much weight. -/
private theorem no_straight (v : S.Valid q) (hq : 4 ≤ q) (hg : b.Gap S q)
    (endpt : 2*S.front q b.weight ≤ 3*S.suffix q b.weight q 0) : False := by
  let N := S.front q b.weight
  have pos : 0 < N := front_pos v (le_refl q) (le_refl (S.lo q)) (bounds v (le_refl q)).1
    (b.weight_pos _)
  rw [suffix_end] at endpt
  change 2*N ≤ 3*S.clip q b.weight 0 at endpt
  have zero : S.lo q = 0 := by
    by_contra h; simp [clip,h] at endpt; omega
  rw [show S.clip q b.weight 0 = b.weight 0 from ite_eq_left ⟨by omega,by omega⟩] at endpt
  have lower : b.weight 0 + q*b.weight 1 ≤ N := front_lower v (le_refl _) zero _
  have enough := Nat.mul_le_mul_left q (b.weight_pos 1)
  have many : b.weight 0 + q ≤ N := by omega
  have free : b.free = 0 := by
    by_contra h
    have e : b.weight 0 = 1 := by simp [Cap.weight, Ne.symm h]
    omega
  have atFree : b.weight 0 = b.ideals := by simp [Cap.weight, free]
  have total (d : ℕ) (hd : d ≤ b.ideals) :
      S.front q (b.member d) + (b.ideals-d) = N := by
    let extra := fun i : ℕ => if i = 0 then b.ideals-d else 0
    have e : S.front q extra = b.ideals-d := by
      simp [extra, front_zero_state v (le_refl q), zero]
    rw [← e, ← front_add]; apply front_congr v (le_refl _)
    intro i _ _; cases i
    · simp [Cap.member, Cap.weight, extra, free]; omega
    · simp [Cap.member, Cap.weight, extra, free]
  cases b with
  | plain => change Cap.plain.weight 0 = 1 at atFree; omega
  | chain a f | fork a f =>
    have mid := hg (a+2) (by first | (simp [Cap.HasCount]; done) | (simp [Cap.HasCount]; omega))
    have midSum := total (a+2) (by simp [Cap.ideals]; omega)
    simp only [Cap.ideals] at atFree midSum
    change Outside N _ at mid; unfold Outside at mid
    have ha : 0<a := by omega
    have one := hg 1 (by first | (simp [Cap.HasCount]; done) | (simp [Cap.HasCount]; omega))
    have oneSum := total 1 (by simp [Cap.ideals])
    simp only [Cap.ideals] at oneSum
    change Outside N _ at one; unfold Outside at one
    omega

/-- All-ranks reduction on the classical heap path model, including both
orientations and chain or doubled-center substitutions of unbounded size. -/
theorem atMostThreeColumns (v : S.Valid q) (hf : b.Fits S q)
    (g : S.Gap q b.weight) (h : b.Gap S q) : q ≤ 3 := by
  by_contra! hq
  have hh : 4 ≤ q := by omega
  rcases g 1 (by omega) 0 with low|high
  · let c := b.flip q
    have vf := valid_flip v
    have cf := Cap.fits_flip v hf
    have refl := Cap.weight_flip v hf
    have H := cut_flip v refl (show 1≤q by omega) (show 0<1 by decide)
    have T := front_flip v (le_refl q) refl
    have first : 2*S.flip.front q c.weight ≤ 3*S.flip.cut q c.weight 1 0 := by
      change 2*S.flip.front q (b.flip q).weight ≤ _
      norm_num1 at H; dsimp only [c]; omega
    exact no_straight vf hh (Cap.gap_flip_cap v hf h)
      (straight_of_first vf hh (fun i _ _ => c.weight_pos i) (Cap.cross_weight cf)
        (Walls.gap_flip v refl g) first q (by omega) (le_refl _))
  · exact no_straight v hh h (straight_of_first v hh (fun i _ _ => b.weight_pos i)
      (Cap.cross_weight hf) g high q (by omega) (le_refl _))

/-- A free middle point bounds the peak size before the small census. -/
private theorem arm_bound (v : S.Valid q) (hf : b.Fits S q) (hq : q ≤ 3)
    (hg : b.Gap S q) : b.ideals ≤ 16 := by
  rcases hf with rfl|⟨fl,fh,_,_⟩
  · decide
  let ind := fun i : ℕ => if i = b.free then 1 else 0
  let F := S.front q ind
  let P := S.front q (fun _ => 1)
  let N := S.front q b.weight
  have fpos : 0 < F := front_pos v (le_refl q) fl fh (by simp [ind])
  have psmall : P ≤ 8 := (front_one_le S q).trans
    (show 2^q ≤ 2^3 from Nat.pow_le_pow_right (by decide) hq)
  have budget : N ≤ P+b.ideals*F := by
    rw [show b.ideals*F = S.front q (fun i => b.ideals * ind i) from (front_scale ..).symm]
    unfold P N; rw [← front_add]; apply front_mono; intro i
    dsimp only [Cap.weight,ind]; split_ifs <;> omega
  have lower (d : ℕ) (hd : 2*d=b.ideals) :
      d*F ≤ S.front q (b.member d) ∧ d*F + S.front q (b.member d) ≤ N := by
    rw [show d*F = S.front q (fun i => d*ind i) from (front_scale ..).symm]
    constructor
    · apply front_mono; intro i; dsimp [ind,Cap.member]; split_ifs <;> simp
    · rw [← front_add]; apply front_mono; intro i
      dsimp [ind,Cap.member,Cap.weight]; split_ifs <;> first | (simp_all; done) | (simp_all; omega)
  cases b with
  | plain => decide
  | chain a f | fork a f =>
    let d := a+2
    have hd : 2*d = 2*a+4 := by dsimp [d]; omega
    have := lower d hd
    have gap := hg d (by first | (simp [Cap.HasCount, d]; done) | (simp [Cap.HasCount, d]; omega))
    change Outside N _ at gap
    unfold Outside at gap
    change N ≤ P+(2*a+4)*F at budget
    rw [← hd, Nat.mul_assoc] at budget
    have m := Nat.mul_le_mul_left d fpos
    change 2*a+4 ≤ 16
    omega

end YiboGaoWeylConvexBalance
namespace YiboGaoWeylConvexBalance

open Walls

abbrev Layer := ℕ × ℕ

/-- Wall intervals in terminal-to-initial order (omitting the dummy layer). -/
def Walls.trace (S : Walls) : ℕ → List Layer
  | 0 => []
  | t+1 => (S.lo (t+1), S.hi (t+1)) :: S.trace t

theorem trace_length (S : Walls) (q : ℕ) : (S.trace q).length = q := by
  induction q <;> simp_all [Walls.trace]

def wallsOf (s : List Layer) : Walls :=
  ⟨fun t => (s[s.length-t]?.getD (0,0)).1, fun t => (s[s.length-t]?.getD (0,0)).2⟩

theorem read_trace {S : Walls} {q : ℕ} (v : S.Valid q) {t : ℕ} (ht : t ≤ q) :
    (wallsOf (S.trace q)).lo t = S.lo t ∧ (wallsOf (S.trace q)).hi t = S.hi t := by
  have read (n : ℕ) (hn : n ≤ q) (k : ℕ) (hk : k ≤ n) :
      ((S.trace n)[n-k]?).getD (0,0) = (S.lo k, S.hi k) := by
    induction n generalizing k with
    | zero =>
      have : k=0 := by omega
      simp [this, Walls.trace, v.lo_zero, v.hi_zero]
    | succ n ih =>
      by_cases h : k=n+1
      · simp [h, Walls.trace]
      · rw [show n+1-k=(n-k)+1 by omega]
        simpa only [Walls.trace, List.getElem?_cons_succ] using ih (by omega) k (by omega)
  simp only [wallsOf, trace_length, read q (le_refl _) t ht, and_self]

private theorem front_ext {S T : Walls} {q : ℕ}
    (h : ∀ t ≤ q, T.lo t=S.lo t ∧ T.hi t=S.hi t) {t : ℕ} (ht : t ≤ q) (w : Row) :
    T.front t w = S.front t w := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    have e : T.clip (t+1) w = S.clip (t+1) w := by
      funext i; simp [clip,(h _ ht).1,(h _ ht).2]
    rw [front, front, e, ih (by omega)]

private theorem suffix_ext {S T : Walls} {q : ℕ}
    (h : ∀ t ≤ q, T.lo t=S.lo t ∧ T.hi t=S.hi t) {t : ℕ} (ht : t ≤ q) (w : Row) :
    T.suffix q w t = S.suffix q w t := by
  induction d : q-t generalizing t with
  | zero =>
    have e : t=q := by omega
    subst t; funext i; simp [suffix_end, clip,(h _ ht).1,(h _ ht).2]
  | succ d ih =>
    have lt : t<q := by omega
    rw [suffix_step T lt, suffix_step S lt, ih (t := t+1) (by omega) (by omega)]
    funext i; simp [clip,(h _ ht).1,(h _ ht).2]

instance (b : Cap) (d : ℕ) : Decidable (b.HasCount d) := by
  cases b <;> unfold Cap.HasCount <;> infer_instance

instance (b : Cap) (S : Walls) (q : ℕ) : Decidable (b.Fits S q) := by
  unfold Cap.Fits; infer_instance

instance (N c : ℕ) : Decidable (Outside N c) := by unfold Outside; infer_instance

/-- Exact cut counts: column thresholds, and membership in the terminal
block. Repeated counts do not affect the maximum. The constant cuts 0 or N
do not affect it either. -/
def counts (S : Walls) (q : ℕ) (b : Cap) : List ℕ :=
  ((List.range (q+1)).flatMap fun t => (List.range (q+1)).map fun k => S.cut q b.weight t k) ++
  (((List.range (b.ideals+1)).filter fun d => decide (b.HasCount d)).map fun d =>
    S.front q (b.member d))

/-- Integer form of "the maximum of min(p,1-p) equals one third":
no count is strictly inside the middle third, and some count is on its boundary. -/
def exactThird (S : Walls) (q : ℕ) (b : Cap) : Bool :=
  let N := S.front q b.weight
  let cs := counts S q b
  cs.all (fun c => decide (Outside N c)) && cs.any (fun c => decide (3*c=N ∨ 3*c=2*N))

private theorem gaps_of_exact {S : Walls} {q : ℕ} {b : Cap} (v : S.Valid q)
    (eq : exactThird S q b) : S.Gap q b.weight ∧ b.Gap S q := by
  have H := (Bool.and_eq_true_iff.mp eq).1
  have out (c : ℕ) (hc : c ∈ counts S q b) : Outside (S.front q b.weight) c :=
    of_decide_eq_true (List.all_eq_true.mp H c hc)
  constructor
  · intro t ht k
    by_cases hk : k ≤ q
    · apply out; apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨t,List.mem_range.mpr (by omega),
        List.mem_map.mpr ⟨k,List.mem_range.mpr (by omega),rfl⟩⟩
    · have e : S.cut q b.weight t k = S.front q b.weight := by
        rw [← front_suffix v b.weight ht]; apply front_congr v ht
        intro i hl hh; have := bounds v ht; simp [show i≤k by omega]
      rw [e]; right; omega
  · intro d hd
    apply out; apply List.mem_append_right; apply List.mem_map.mpr
    refine ⟨d, List.mem_filter.mpr ⟨List.mem_range.mpr ?_, decide_eq_true hd⟩,rfl⟩
    cases b <;> simp_all [Cap.HasCount,Cap.ideals] <;> omega

private theorem flat_congr {α β : Type} {f g : α → List β} (l : List α)
    (h : ∀ a ∈ l, f a=g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, h a (by simp), ih (fun b hb => h b (by simp [hb]))]

private theorem exact_ext {S T : Walls} {q : ℕ} (b : Cap)
    (h : ∀ t ≤ q, T.lo t=S.lo t ∧ T.hi t=S.hi t) :
    exactThird T q b = exactThird S q b := by
  have mems : counts T q b = counts S q b := by
    unfold counts; congr 1
    · apply flat_congr; intro t ht
      have ht' : t ≤ q := by have := List.mem_range.mp ht; omega
      simp only [cut, suffix_ext h ht', front_ext h ht']
    · simp only [front_ext h (le_refl q)]
  simp only [exactThird,mems,front_ext h (le_refl q)]

/-- The only nonempty classical equality strips. In each pair the second
entry is the reflection of the first. In order: a two-point chain; a
four-point three-column heap; a four-point heap with terminal twins. -/
def examples : List (List Layer × Cap) :=
  [( [(0,1),(0,1)], Cap.plain ),
    ( [(1,2),(0,1)], Cap.plain ),
    ( [(0,2),(0,1),(0,1)], Cap.plain ),
    ( [(1,3),(1,2),(0,1)], Cap.plain ),
    ( [(0,1),(0,1)], Cap.fork 0 0 ),
    ( [(1,2),(0,1)], Cap.fork 0 2 )]

def listed (s : List Layer) (b : Cap) : Bool := examples.contains (s,b)

def traces : ℕ → List (List Layer)
  | 0 => [[]]
  | t+1 => (traces t).flatMap fun s =>
      let p := s.headD (0,0)
      ([(p.1,p.2), (p.1+1,p.2), (p.1,p.2+1), (p.1+1,p.2+1)] : List Layer).filterMap
        fun z => if z.1<z.2 then some (z::s) else none

theorem trace_mem {S : Walls} {q : ℕ} (v : S.Valid q) {t : ℕ} (ht : t ≤ q) :
    S.trace t ∈ traces t := by
  induction t with
  | zero => simp [traces, Walls.trace]
  | succ t ih =>
    have prev : (S.trace t).headD (0,0) = (S.lo t,S.hi t) := by
      cases t <;> simp [Walls.trace,v.lo_zero,v.hi_zero]
    apply List.mem_flatMap.mpr
    refine ⟨S.trace t, ih (by omega), ?_⟩
    apply List.mem_filterMap.mpr
    refine ⟨(S.lo (t+1),S.hi (t+1)), ?_, ?_⟩
    · have a := v.step_lo t (by omega); have b := v.step_hi t (by omega)
      rw [prev]; simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]; omega
    · simp [v.wide (t+1) (by omega) ht,Walls.trace]

def caps : List Cap :=
  .plain :: (List.range 7).flatMap fun a => (List.range 5).flatMap fun f =>
    [Cap.chain a f, Cap.fork a f]

theorem cap_mem {S : Walls} {q : ℕ} {b : Cap} (v : S.Valid q)
    (hf : b.Fits S q) (hq : q ≤ 4) (hm : b.ideals ≤ 16) : b ∈ caps := by
  rcases hf with rfl|⟨_,fh,_,_⟩
  · simp [caps]
  have := bounds v (le_refl _)
  cases b with
  | plain => simp [caps]
  | chain a f | fork a f =>
    simp only [Cap.free, Cap.ideals] at *
    apply List.mem_cons_of_mem
    apply List.mem_flatMap.mpr; refine ⟨a,List.mem_range.mpr (by omega),?_⟩
    apply List.mem_flatMap.mpr; exact ⟨f,List.mem_range.mpr (by omega),by simp⟩

/- Exhaustion uses the four possible unit increments of the two walls,
not a list of candidate equality examples as the input to the test. -/
set_option maxRecDepth 16384 in
set_option maxHeartbeats 1600000 in
private theorem small_census : (List.range 4).all (fun q => (traces q).all fun s =>
    caps.all fun b => !(decide (b.Fits (wallsOf s) q)) ||
      (exactThird (wallsOf s) q b == listed s b)) = true := by decide +kernel

/-- Complete equality classification in the connected classical
alternating-strip/terminal-block model. There is no input bound on rank,
arm length, number of columns or column heights. -/
theorem classicalStripClassification {S : Walls} {q : ℕ} {b : Cap}
    (v : S.Valid q) (hf : b.Fits S q) :
    exactThird S q b = true ↔ listed (S.trace q) b = true := by
  have link (hq : q ≤ 3) (hm : b.ideals ≤ 16) : exactThird S q b = listed (S.trace q) b := by
    have E (t : ℕ) (ht : t ≤ q) := read_trace v ht
    have fits : b.Fits (wallsOf (S.trace q)) q := by
      simpa only [Cap.Fits,(E q (le_refl _)).1,(E q (le_refl _)).2] using hf
    have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp small_census q
        (List.mem_range.mpr (by omega))) _ (trace_mem v (le_refl _))) _ (cap_mem v hf (by omega) hm)
    simpa [fits,exact_ext b E] using h
  constructor
  · intro e
    obtain ⟨g,h⟩ := gaps_of_exact v e
    have hq := atMostThreeColumns v hf g h
    rwa [← link hq (arm_bound v hf hq h)]
  · intro e
    have small : examples.all (fun p => decide (p.1.length ≤ 3 ∧ p.2.ideals ≤ 16)) = true := by decide
    have pair : (S.trace q,b) ∈ examples := List.contains_iff_mem.mp e
    obtain ⟨l,r⟩ := of_decide_eq_true (List.all_eq_true.mp small _ pair)
    rw [link (by simpa only [trace_length] using l) r]; exact e

end YiboGaoWeylConvexBalance
