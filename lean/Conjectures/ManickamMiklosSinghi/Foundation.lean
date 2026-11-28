import Mathlib

/-!
# Manickam–Miklós–Singhi: finite counting and certificate foundations

Entry points are in the namespace `ManickamMiklosSinghi`. Sets are sets of **indices**
(so repeated values are never identified); `Fin n` uses zero-based indexing.
-/

namespace ManickamMiklosSinghi

open Finset
open scoped BigOperators

noncomputable section

/-- Nonnegative k-sums among the indices of an arbitrary finite ground set. -/
def good {α : Type*} (U : Finset α) (k : ℕ) (x : α → ℝ) : Finset (Finset α) :=
  (U.powersetCard k).filter fun S => 0 ≤ ∑ i ∈ S, x i

@[simp] theorem mem_good {α : Type*} {U S : Finset α} {k : ℕ} {x : α → ℝ} :
    S ∈ good U k x ↔ (S ⊆ U ∧ S.card = k) ∧ 0 ≤ ∑ i ∈ S, x i := by
  classical
  simp only [good, mem_filter, mem_powersetCard]

def nonnegKSubsets (n k : ℕ) (x : Fin n → ℝ) : Finset (Finset (Fin n)) := good univ k x

/-- The fixed-parameter assertion; admissible parameters are 1 ≤ k ≤ n. -/
def MMSHolds (n k : ℕ) : Prop :=
  ∀ x : Fin n → ℝ, 0 ≤ ∑ i, x i → (n-1).choose (k-1) ≤ (nonnegKSubsets n k x).card

/-- The selected coordinates of a Bernoulli outcome. -/
def support {m : ℕ} (v : Fin m → Bool) : Finset (Fin m) := univ.filter fun i => v i = true

/-- Product mass of the event of attaining or exceeding the normalized mean. -/
def exceedance {m : ℕ} (w : Fin m → ℝ) (p : ℝ) : ℝ :=
  ∑ v : Fin m → Bool, if p ≤ ∑ i ∈ support v, w i then
    p ^ (support v).card * (1-p) ^ (m - (support v).card) else 0

def milojevicSudakovConjectureOne : Prop :=
  ∀ (p : ℝ), 0 ≤ p → p ≤ 1/3 → ∀ (m : ℕ) (w : Fin m → ℝ),
    (∀ i, 0 < w i) → ∑ i, w i = 1 → p ≤ exceedance w p

def milojevicSudakovConjectureThree : Prop :=
  ∀ ε C : ℝ, 0 < ε → 0 < C → ∃ N : ℕ, ∀ n k : ℕ, N ≤ n → N ≤ k → 0 < k →
    (3+ε) * k ≤ n → ∀ x : Fin n → ℝ, ∑ i, x i = 0 →
    ((univ.filter fun i => 0 ≤ x i).card : ℝ) ≤ C →
    (∀ i j, x i < 0 → x j < 0 → x i = x j) →
    (n-1).choose (k-1) ≤ (nonnegKSubsets n k x).card

/-- Relabeling indices preserves the family, not just its cardinality. -/
theorem good_map {α β : Type*} (e : α ↪ β) (U : Finset α) (k : ℕ) (x : β → ℝ) :
    (good U k (x ∘ e)).map (Finset.mapEmbedding e).toEmbedding = good (U.map e) k x := by
  classical
  ext T
  constructor
  · rintro h
    obtain ⟨S, hS, rfl⟩ := mem_map.mp h
    obtain ⟨⟨hSU, hc⟩, hz⟩ := mem_good.mp hS
    exact mem_good.mpr ⟨⟨map_subset_map.mpr hSU, by simpa using hc⟩, by simpa [Function.comp_def] using hz⟩
  · intro h
    obtain ⟨⟨ht, hc⟩, hz⟩ := mem_good.mp h
    let S := U.filter fun i => e i ∈ T
    have hST : S.map e = T := by
      ext i
      constructor
      · intro hi
        obtain ⟨a, ha, rfl⟩ := mem_map.mp hi
        exact (mem_filter.mp ha).2
      · intro hi
        obtain ⟨a, ha, rfl⟩ := mem_map.mp (ht hi)
        exact mem_map.mpr ⟨a, mem_filter.mpr ⟨ha, hi⟩, rfl⟩
    refine mem_map.mpr ⟨S, mem_good.mpr ⟨⟨filter_subset _ _, ?_⟩, ?_⟩, hST⟩
    · simpa [← hST] using hc
    · simpa [← hST, Function.comp_def] using hz

theorem good_mono {α : Type*} (U : Finset α) (k : ℕ) {x y : α → ℝ}
    (h : ∀ i ∈ U, x i ≤ y i) : good U k x ⊆ good U k y := by
  intro S hS
  obtain ⟨⟨hSU,hc⟩,hz⟩ := mem_good.mp hS
  exact mem_good.mpr ⟨⟨hSU,hc⟩, hz.trans (sum_le_sum fun i hi => h i (hSU hi))⟩

/-- The sorted, exactly zero-total problem is equivalent to the original assertion. -/
theorem mms_iff_sorted_zero {n k : ℕ} (hn : 0 < n) :
    MMSHolds n k ↔ ∀ x : Fin n → ℝ, Antitone x → ∑ i, x i = 0 →
      (n-1).choose (k-1) ≤ (nonnegKSubsets n k x).card := by
  constructor
  · intro h x _ hz
    exact h x hz.ge
  intro h x hx
  let a : ℝ := (∑ i, x i) / n
  let y : Fin n → ℝ := fun i => x i - a
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hy : ∑ i, y i = 0 := by
    simp [y, sum_sub_distrib, a, mul_div_cancel₀, hn', nsmul_eq_mul]
  let e := Tuple.sort (fun i => -y i)
  have he : Antitone (y ∘ e) := by
    intro i j hij
    exact neg_le_neg_iff.mp (Tuple.monotone_sort (fun i => -y i) hij)
  have h0 : ∑ i, (y ∘ e) i = 0 := (Equiv.sum_comp e y).trans hy
  have hmap := congrArg Finset.card (good_map e.toEmbedding univ k y)
  have hcard : (nonnegKSubsets n k (y ∘ e)).card = (good univ k y).card := by
    simpa [nonnegKSubsets] using hmap
  exact (h (y ∘ e) he h0).trans (hcard.le.trans (card_le_card (good_mono univ k
    (fun i _ => sub_le_self (x i) (div_nonneg hx (Nat.cast_nonneg _))))))

/-- Gale order given explicitly by the two increasing enumerations. -/
def GaleLE {n k : ℕ} (S T : Finset (Fin n)) (hS : S.card = k) (hT : T.card = k) : Prop :=
  ∀ j, S.orderEmbOfFin hS j ≤ T.orderEmbOfFin hT j

theorem sum_le_of_gale {n k : ℕ} {x : Fin n → ℝ} (hx : Antitone x)
    {S T : Finset (Fin n)} {hS : S.card = k} {hT : T.card = k} (h : GaleLE S T hS hT) :
    ∑ i ∈ T, x i ≤ ∑ i ∈ S, x i := by
  calc
    ∑ i ∈ T, x i = ∑ j : Fin k, x (T.orderEmbOfFin hT j) := by
      exact (congrArg (fun U => ∑ i ∈ U, x i) (T.map_orderEmbOfFin_univ hT).symm).trans
        (Finset.sum_map univ (T.orderEmbOfFin hT).toEmbedding x)
    _ ≤ ∑ j : Fin k, x (S.orderEmbOfFin hS j) := sum_le_sum fun j _ => hx (h j)
    _ = ∑ i ∈ S, x i := by
      exact (Finset.sum_map univ (S.orderEmbOfFin hS).toEmbedding x).symm.trans
        (congrArg (fun U => ∑ i ∈ U, x i) (S.map_orderEmbOfFin_univ hS))

theorem nonneg_of_gale {n k : ℕ} {x : Fin n → ℝ} (hx : Antitone x)
    {S T : Finset (Fin n)} {hS : S.card = k} {hT : T.card = k} (h : GaleLE S T hS hT)
    (hz : 0 ≤ ∑ i ∈ T, x i) : 0 ≤ ∑ i ∈ S, x i := hz.trans (sum_le_of_gale hx h)

/-- Transport the fixed-parameter assertion to a subset of any finite linear order. -/
theorem mms_on {α : Type*} [LinearOrder α] {n k : ℕ} (h : MMSHolds n k)
    (U : Finset α) (hU : U.card = n) (x : α → ℝ) (hx : 0 ≤ ∑ i ∈ U, x i) :
    (n-1).choose (k-1) ≤ (good U k x).card := by
  let e := (U.orderEmbOfFin hU).toEmbedding
  have he : univ.map e = U := U.map_orderEmbOfFin_univ hU
  have h0 : 0 ≤ ∑ i, (x ∘ e) i := by
    simpa only [← he, sum_map, Function.comp_apply] using hx
  have hmap := congrArg Finset.card (good_map e univ k x)
  rw [card_map, he] at hmap
  exact (h (x ∘ e) h0).trans hmap.le

private theorem choose_star {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    n * (n-1).choose (k-1) = n.choose k * k := by
  obtain ⟨a,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  obtain ⟨b,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  exact Nat.add_one_mul_choose_eq a b

/-- Chowdhury step. Count ordered disjoint pairs (bad k-set, good k-set).
Every bad set has at least choose(n-1,k-1) good neighbours by the hypothesis;
every good set has at most choose(n,k) bad neighbours. -/
theorem mms_add_k {n k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (h : MMSHolds n k) :
    MMSHolds (n+k) k := by
  classical
  intro x hx
  let U : Finset (Fin (n+k)) := univ
  let K := U.powersetCard k
  let G := good U k x
  let B := K.filter fun S => ¬ 0 ≤ ∑ i ∈ S, x i
  let t := (n-1).choose (k-1)
  have hc {S : Finset (Fin (n+k))} (hS : S ∈ K) : Sᶜ.card = n := by
    simp [card_compl, (mem_powersetCard.mp hS).2]
  have hpart : G.card+B.card = (n+k).choose k := by
    simpa [G, B, K, U, good, card_powersetCard] using
      (card_filter_add_card_filter_not (s := K) (fun S => 0 ≤ ∑ i ∈ S, x i))
  have hlo (S) (hS : S ∈ B) : t ≤ (G.filter (fun T => Disjoint S T)).card := by
    obtain ⟨hsK, hsbad⟩ := mem_filter.mp hS
    have hz := sum_add_sum_compl S x
    have hm := mms_on h Sᶜ (hc hsK) x (by linarith : 0 ≤ ∑ i ∈ Sᶜ, x i)
    refine hm.trans (card_le_card ?_)
    intro T ht
    obtain ⟨⟨hTU, hTk⟩, hgood⟩ := mem_good.mp ht
    exact mem_filter.mpr ⟨mem_good.mpr ⟨⟨subset_univ _, hTk⟩, hgood⟩,
      disjoint_left.mpr fun i his hit => (mem_compl.mp (hTU hit)) his⟩
  have hhi (T) (hT : T ∈ G) : (B.filter (fun S => Disjoint S T)).card ≤ n.choose k := by
    have hcT := hc ((mem_filter.mp hT).1)
    refine le_trans ?_ (le_of_eq (show (Tᶜ.powersetCard k).card = n.choose k by
      rw [card_powersetCard, hcT]))
    apply card_le_card
    intro S hs
    obtain ⟨hsB, hd⟩ := mem_filter.mp hs
    exact mem_powersetCard.mpr ⟨fun i hi => mem_compl.mpr fun ht => disjoint_left.mp hd hi ht,
      (mem_powersetCard.mp (mem_filter.mp hsB).1).2⟩
  have dc : B.card * t ≤ G.card * n.choose k := calc
    _ = ∑ _S ∈ B, t := by simp
    _ ≤ ∑ S ∈ B, (G.filter fun T => Disjoint S T).card := sum_le_sum hlo
    _ = ∑ T ∈ G, (B.filter fun S => Disjoint S T).card := by
      simp only [card_eq_sum_ones, sum_filter]
      exact sum_comm
    _ ≤ ∑ _T ∈ G, n.choose k := sum_le_sum hhi
    _ = _ := by simp
  have ht : 0 < t := Nat.choose_pos (by omega)
  have hn := hk.trans_le hkn
  have hnk : 0 < n+k := by omega
  have dc' : (B.card * k) * t ≤ (G.card * n) * t := calc
    _ = (B.card * t) * k := by ac_rfl
    _ ≤ (G.card * n.choose k) * k := Nat.mul_le_mul_right _ dc
    _ = (G.card * n) * t := by dsimp only [t]; rw [mul_assoc, ← choose_star hn hk]; ac_rfl
  have bound : B.card * k ≤ G.card * n := Nat.le_of_mul_le_mul_right dc' ht
  apply Nat.le_of_mul_le_mul_left (c := n+k)
  · change (n+k) * (n+k-1).choose (k-1) ≤ (n+k) * G.card
    rw [choose_star hnk hk, ← hpart]
    nlinarith only [bound]
  · exact hnk

theorem mms_self {k : ℕ} (_hk : 0 < k) : MMSHolds k k := by
  intro x hx
  rw [Nat.choose_self]
  apply card_pos.mpr
  exact ⟨univ, mem_good.mpr ⟨⟨Subset.rfl, by simp⟩, hx⟩⟩

/-- Divisible case, equivalently repeated disjoint-block averaging. -/
theorem mms_of_dvd {n k : ℕ} (hk : 0 < k) (hn : 0 < n) (hd : k ∣ n) : MMSHolds n k := by
  obtain ⟨m,rfl⟩ := hd
  cases m with
  | zero => simp at hn
  | succ m =>
    clear hn
    induction m with
    | zero => simpa using mms_self hk
    | succ m ih =>
      rw [Nat.mul_succ k (m+1)]
      exact mms_add_k hk (by rw [Nat.mul_succ]; omega) ih

/-- The seven nondivisible base cases suffice; 32 is discharged by the divisible theorem. -/
theorem eight_of_seven (h : ∀ n ∈ ({26,27,28,29,30,31,33} : Finset ℕ), MMSHolds n 8) :
    ∀ n ≥ 26, MMSHolds n 8 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hb : n ≤ 33
    · by_cases hn' : n = 32
      · subst n
        exact mms_of_dvd (by decide) (by decide) (by decide)
      · apply h
        simp only [mem_insert, mem_singleton]
        omega
    · have hr := mms_add_k (n := n-8) (k := 8) (by decide) (by omega)
          (ih (n-8) (by omega) (by omega))
      simpa [Nat.sub_add_cancel (show 8 ≤ n by omega)] using hr

/-- 22 entries equal to 3, followed by three entries equal to -22. -/
def witness25 (i : Fin 25) : ℝ := (if i < (22 : Fin 25) then 25 else 0) - 22

private theorem sum_witness25 (S : Finset (Fin 25)) :
    ∑ i ∈ S, witness25 i =
      ((S.filter fun i => i < (22 : Fin 25)).card : ℝ) * 25 - (S.card : ℝ) * 22 := by
  simp [witness25, sum_sub_distrib, ← sum_filter, nsmul_eq_mul]

private theorem pos_card : (Iio (22 : Fin 25)).card = 22 := by decide

theorem witness25_total : ∑ i, witness25 i = 0 := by
  rw [sum_witness25]
  have he : univ.filter (fun i : Fin 25 => i < (22 : Fin 25)) = Iio (22 : Fin 25) := by ext; simp
  rw [he]
  norm_num

theorem witness25_family :
    nonnegKSubsets 25 8 witness25 = (Iio (22 : Fin 25)).powersetCard 8 := by
  classical
  ext S
  simp only [nonnegKSubsets, mem_good, subset_univ, true_and, mem_powersetCard, sum_witness25]
  let P := fun i : Fin 25 => i < (22 : Fin 25)
  have hle : (S.filter P).card ≤ S.card := card_filter_le _ _
  constructor
  · rintro ⟨hc, hz⟩
    have h8 : 8 ≤ (S.filter P).card := by
      by_contra! h
      have h7 : ((S.filter P).card : ℝ) ≤ 7 := by exact_mod_cast (show (S.filter P).card ≤ 7 by omega)
      rw [hc] at hz
      change 0 ≤ ((S.filter P).card : ℝ) * 25 - (8:ℝ)*22 at hz
      linarith
    have he : S.filter P = S := eq_of_subset_of_card_le (filter_subset _ _) (hc ▸ h8)
    exact ⟨fun i hi => mem_Iio.mpr (mem_filter.mp (he.symm ▸ hi : i ∈ S.filter P)).2, hc⟩
  · rintro ⟨hs, hc⟩
    have he : S.filter P = S := filter_true_of_mem fun i hi => mem_Iio.mp (hs hi)
    refine ⟨hc, ?_⟩
    change 0 ≤ ((S.filter P).card : ℝ) * 25 - (S.card : ℝ)*22
    rw [he,hc]
    norm_num

theorem witness25_count : (nonnegKSubsets 25 8 witness25).card = 319770 := by
  rw [witness25_family, card_powersetCard, pos_card]
  decide

theorem not_mms_25_8 : ¬ MMSHolds 25 8 := by
  intro h
  have h' := h witness25 witness25_total.ge
  rw [witness25_count] at h'
  exact (show ¬ (25-1).choose (8-1) ≤ 319770 by decide) h'

/-- No threshold through which MMS holds thereafter can be less than 26. -/
theorem threshold_eight_ge {m : ℕ} (h : ∀ n ≥ m, MMSHolds n 8) : 26 ≤ m := by
  by_contra! hm
  exact not_mms_25_8 (h 25 (by omega))

/-- First incidence moment on an arbitrary finite ground set. -/
theorem powersetCard_sum {α : Type*} [DecidableEq α] (U : Finset α) {k : ℕ}
    (hk : 0 < k) (x : α → ℝ) :
    ∑ S ∈ U.powersetCard k, ∑ i ∈ S, x i =
      ((U.card - 1).choose (k - 1) : ℝ) * ∑ i ∈ U, x i := by
  classical
  have star (i : α) (hi : i ∈ U) :
      ((U.powersetCard k).filter (fun S => i ∈ S)).card = (U.card-1).choose (k-1) := by
    simpa using card_filter_powersetCard_subset ({i} : Finset α) U k
      (singleton_subset_iff.mpr hi) (by simp only [card_singleton]; omega)
  calc
    _ = ∑ S ∈ U.powersetCard k, ∑ i ∈ U, if i ∈ S then x i else 0 := by
      refine sum_congr rfl fun S hS => ?_
      rw [← sum_filter]
      have he : U.filter (· ∈ S) = S := by
        ext j
        simp only [mem_filter, and_iff_right_iff_imp]
        exact fun hj => (mem_powersetCard.mp hS).1 hj
      rw [he]
    _ = ∑ i ∈ U, ∑ S ∈ U.powersetCard k, if i ∈ S then x i else 0 := sum_comm
    _ = _ := by
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      rw [← sum_filter]
      simp [star i hi, nsmul_eq_mul]

/-- CSS complementary-ground-set identity: no order assumption, R is arbitrary. -/
theorem intersect_sum {n k : ℕ} (hk : 0 < k) (x : Fin n → ℝ) (hx : ∑ i, x i = 0)
    (R : Finset (Fin n)) :
    ∑ S ∈ ((univ : Finset (Fin n)).powersetCard k).filter (fun S => ¬ Disjoint S R),
        ∑ i ∈ S, x i = ((n-R.card-1).choose (k-1) : ℝ) * ∑ i ∈ R, x i := by
  classical
  let K := (univ : Finset (Fin n)).powersetCard k
  have he : K.filter (fun S => Disjoint S R) = Rᶜ.powersetCard k := by
    ext S
    simp only [K, mem_filter, mem_powersetCard, subset_univ, true_and]
    rw [and_comm]
    exact and_congr_left fun _ => by
      simp [Finset.disjoint_left, Finset.subset_iff]
  have hz := sum_filter_add_sum_filter_not K (fun S => Disjoint S R)
    (fun S => ∑ i ∈ S, x i)
  rw [he, powersetCard_sum _ hk, show K = _ from rfl, powersetCard_sum _ hk, hx,
      mul_zero, Finset.card_compl] at hz
  have hR := Finset.sum_add_sum_compl R x
  rw [hx] at hR
  simp only [Fintype.card_fin] at hz
  change ∑ S ∈ K.filter _, _ = _
  linear_combination hz - ((n-R.card-1).choose (k-1) : ℝ) * hR

theorem star_sum {n k : ℕ} (hk : 0 < k) (x : Fin n → ℝ) (hx : ∑ i, x i = 0)
    (i : Fin n) : ∑ S ∈ ((univ : Finset (Fin n)).powersetCard k).filter (fun S => i ∈ S),
      ∑ j ∈ S, x j = ((n-2).choose (k-1) : ℝ) * x i := by
  simpa [Nat.sub_sub] using intersect_sum hk x hx {i}

/-! ## Rational certificates, with real primal variables and mixed strict rows -/

namespace Certificate

structure Row (n : ℕ) where
  coeff : Fin n → ℚ
  rhs : ℚ
  strict : Bool
  deriving DecidableEq

def slack {n : ℕ} (r : Row n) (x : Fin n → ℝ) : ℝ :=
  (∑ j, (r.coeff j : ℝ) * x j) - (r.rhs : ℝ)

def Holds {n : ℕ} (r : Row n) (x : Fin n → ℝ) : Prop :=
  if r.strict = true then 0 < slack r x else 0 ≤ slack r x

def Feasible {n : ℕ} (Γ : List (Row n)) (x : Fin n → ℝ) : Prop := ∀ r ∈ Γ, Holds r x

/-- All these checks are on rational numbers, booleans and finite index sets.
Strictness requires either an improved RHS or a strict row with a positive multiplier. -/
structure Dual {n : ℕ} (Γ : List (Row n)) (c : Row n) (lam : Fin Γ.length → ℚ) : Prop where
  nonneg : ∀ i, 0 ≤ lam i
  column : ∀ j, ∑ i, lam i * (Γ.get i).coeff j = c.coeff j
  rhs : c.rhs ≤ ∑ i, lam i * (Γ.get i).rhs
  strict : c.strict = true →
    c.rhs < ∑ i, lam i * (Γ.get i).rhs ∨ ∃ i, 0 < lam i ∧ (Γ.get i).strict = true

theorem dual_sound {n : ℕ} {Γ : List (Row n)} {c : Row n} {lam : Fin Γ.length → ℚ}
    (d : Dual Γ c lam) {x : Fin n → ℝ} (hx : Feasible Γ x) : Holds c x := by
  classical
  let t : Fin Γ.length → ℝ := fun i => (lam i : ℝ) * slack (Γ.get i) x
  have hg i := hx (Γ.get i) (List.get_mem Γ i)
  have hlam (i) : (0:ℝ) ≤ lam i := by exact_mod_cast d.nonneg i
  have ht (i) : 0 ≤ t i := by
    apply mul_nonneg (hlam i)
    have hi := hg i
    unfold Holds at hi
    split at hi
    · exact hi.le
    · exact hi
  have ht0 : 0 ≤ ∑ i, t i := sum_nonneg fun i _ => ht i
  have hcol (j) : (∑ i, (lam i : ℝ) * ((Γ.get i).coeff j : ℝ)) = (c.coeff j : ℝ) := by
    exact_mod_cast d.column j
  have hid : ∑ i, t i =
      (∑ j, (c.coeff j : ℝ) * x j) - ∑ i, (lam i : ℝ) * ((Γ.get i).rhs : ℝ) := by
    simp only [t, slack, mul_sub, sum_sub_distrib, mul_sum, ← mul_assoc]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl fun j _ => by rw [← sum_mul, hcol]
  have hb : (c.rhs : ℝ) ≤ ∑ i, (lam i : ℝ) * ((Γ.get i).rhs : ℝ) := by exact_mod_cast d.rhs
  unfold Holds slack
  split
  · rename_i hs
    rcases d.strict hs with h | ⟨i, hp, hi⟩
    · have h' : (c.rhs : ℝ) < ∑ i, (lam i : ℝ) * ((Γ.get i).rhs : ℝ) := by exact_mod_cast h
      linarith
    · have hpos : 0 < t i := mul_pos (by exact_mod_cast hp)
          (by simpa only [Holds,hi,ite_true] using hg i)
      have hsum := sum_pos' (s := univ) (fun j _ => ht j) ⟨i, mem_univ _, hpos⟩
      linarith
  · linarith

def contradictionRow (n : ℕ) : Row n := ⟨fun _ => 0, 0, true⟩

theorem dual_infeasible {n : ℕ} {Γ : List (Row n)} {lam : Fin Γ.length → ℚ}
    (d : Dual Γ (contradictionRow n) lam) : ¬ ∃ x, Feasible Γ x := by
  rintro ⟨x,hx⟩
  simpa [Holds, slack, contradictionRow] using dual_sound d hx

def setRow {n : ℕ} (S : Finset (Fin n)) (negative : Bool) : Row n :=
  ⟨fun j => if j ∈ S then (if negative then -1 else 1) else 0, 0, negative⟩

@[simp] theorem holds_positive {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    Holds (setRow S false) x ↔ 0 ≤ ∑ j ∈ S, x j := by
  classical
  simp [setRow, Holds, slack, apply_ite (fun z : ℚ => (z : ℝ)), ite_mul]

@[simp] theorem holds_negative {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) :
    Holds (setRow S true) x ↔ ∑ j ∈ S, x j < 0 := by
  classical
  simp [setRow, Holds, slack, apply_ite (fun z : ℚ => (z : ℝ)), ite_mul]

/-- Context satisfaction is purely conjunctive; the list order indexes dual multipliers. -/
theorem feasible_cons {n : ℕ} {Γ : List (Row n)} {r : Row n} {x : Fin n → ℝ} :
    Feasible (r :: Γ) x ↔ Holds r x ∧ Feasible Γ x := by simp [Feasible]

/-- Finite proof-producing branch-and-cut: fork on an actual subset sum, derive a row by
rational arithmetic, or discharge by infeasibility or an explicit counted family. -/
inductive CertTree (n k target : ℕ) : List (Row n) → Prop
  | impossible {Γ} (lam) (d : Dual Γ (contradictionRow n) lam) : CertTree n k target Γ
  | count {Γ} (F : Finset (Finset (Fin n))) (enough : target ≤ F.card)
      (known : ∀ S ∈ F, S.card = k ∧ setRow S false ∈ Γ) : CertTree n k target Γ
  | cut {Γ} (r : Row n) (lam) (d : Dual Γ r lam) (tail : CertTree n k target (r :: Γ)) :
      CertTree n k target Γ
  | branch {Γ} (S : Finset (Fin n)) (left : CertTree n k target (setRow S false :: Γ))
      (right : CertTree n k target (setRow S true :: Γ)) : CertTree n k target Γ

theorem tree_sound {n k target : ℕ} {Γ : List (Row n)} (tree : CertTree n k target Γ)
    (x : Fin n → ℝ) (hx : Feasible Γ x) : target ≤ (nonnegKSubsets n k x).card := by
  induction tree with
  | impossible lam d => exact (dual_infeasible d ⟨x,hx⟩).elim
  | count F enough known =>
    refine enough.trans (card_le_card ?_)
    intro S hS
    obtain ⟨hc, hm⟩ := known S hS
    exact mem_good.mpr ⟨⟨subset_univ _, hc⟩, (holds_positive S x).mp (hx _ hm)⟩
  | cut r lam d _ ih => exact ih (feasible_cons.mpr ⟨dual_sound d hx, hx⟩)
  | branch S _ _ ihl ihr =>
    by_cases hp : 0 ≤ ∑ i ∈ S, x i
    · exact ihl (feasible_cons.mpr ⟨(holds_positive S x).mpr hp, hx⟩)
    · exact ihr (feasible_cons.mpr ⟨(holds_negative S x).mpr (lt_of_not_ge hp), hx⟩)

/-- Weak rows expressing a coordinate comparison and a signed total. -/
def orderRow {n : ℕ} (i j : Fin n) : Row n :=
  ⟨fun a => (if a=i then 1 else 0) - (if a=j then 1 else 0), 0, false⟩

def totalRow (n : ℕ) (negative : Bool) : Row n :=
  ⟨fun _ => if negative then -1 else 1, 0, false⟩

inductive Initial {n : ℕ} : Row n → Prop
  | order {i j : Fin n} (h : i ≤ j) : Initial (orderRow i j)
  | total (b : Bool) : Initial (totalRow n b)
  | maximum (i : Fin n) (h : ∀ j, i ≤ j) : Initial (setRow {i} false)

theorem initial_sound {n : ℕ} {r : Row n} (hi : Initial r) {x : Fin n → ℝ}
    (hx : Antitone x) (hz : ∑ i, x i = 0) : Holds r x := by
  classical
  cases hi with
  | order hij => simpa [Holds, slack, orderRow, apply_ite (fun z : ℚ => (z : ℝ)), sub_mul, sum_sub_distrib, ite_mul] using hx hij
  | total b => cases b <;> simp [Holds, slack, totalRow, hz]
  | maximum i hi =>
    apply (holds_positive {i} x).mpr
    simp only [sum_singleton]
    by_contra! hn
    have hs := sum_neg (s := (univ : Finset (Fin n))) (fun j _ => (hx (hi j)).trans_lt hn)
      ⟨i, mem_univ _⟩
    linarith

/-- A certificate at the sorted zero-sum root proves the unrestricted MMS statement. -/
theorem mms_of_tree {n k : ℕ} (hn : 0 < n) {Γ : List (Row n)}
    (roots : ∀ r ∈ Γ, Initial r) (tree : CertTree n k ((n-1).choose (k-1)) Γ) :
    MMSHolds n k := (mms_iff_sorted_zero hn).mpr fun x hx hz =>
      tree_sound tree x (fun r hr => initial_sound (roots r hr) hx hz)

end Certificate


end

end ManickamMiklosSinghi
