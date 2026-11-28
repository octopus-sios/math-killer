module

public import Conjectures.NabergallChordalDiagrams
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.Tactic.LinearCombination

@[expose] public section

/-!
# Algebra of the earliest-cut recurrence

Weight is marked by a Laurent variable; length is marked by the power
series variable. All generating functions in this file are formal.
-/

namespace NabergallChordalDiagrams.Series
noncomputable section
open scoped BigOperators

abbrev Table := ℕ → ℕ → ℕ
abbrev WeightRow := ℕ →₀ ℕ

/-- Histogram of the positive weights at a fixed length. -/
def weights (F : Table) (n : ℕ) : WeightRow :=
  ∑ a ∈ Finset.range n, Finsupp.single (a+1) (F n (a+1))

/-- For each length split and each positive pair of weights, use the
histogram `g i j` of possible resulting weights. Zero-length pieces
contribute an empty inner sum. -/
def splitCounts (I H : Table) (g : ℕ → ℕ → WeightRow) (n : ℕ) : WeightRow :=
  ∑ ab ∈ Finset.antidiagonal n,
    ∑ i ∈ Finset.range ab.1, ∑ j ∈ Finset.range ab.2,
      (I ab.1 (i+1) * H ab.2 (j+1)) • g (i+1) (j+1)

/-- The weights resulting from 1 through `min i q` links, where the
second child's weight is `q+1`. Index `h` represents `h+1` links. -/
def links (i q : ℕ) : WeightRow :=
  ∑ h ∈ Finset.range (min i q), Finsupp.single (i+q-1-2*h) 1

def seed (n : ℕ) : WeightRow := if n = 1 then Finsupp.single 1 1 else 0

/-- Section 3, as equalities of finite weight histograms. Evaluating the
two equalities at `k` gives the scalar counting recurrences. The empty
fragment is not included in either table. -/
structure Recurrences (I H : Table) : Prop where
  i_zero : ∀ n, I n 0 = 0
  h_zero : ∀ n, H n 0 = 0
  i_support : ∀ n k, n < k → I n k = 0
  h_support : ∀ n k, n < k → H n k = 0
  sequence : ∀ n, weights H n = weights I n +
    splitCounts I H (fun i j => Finsupp.single (i+j) 1) n
  earliest : ∀ n, weights I n = seed n +
    splitCounts I H (fun i j => links i (j-1)) n

/-- Evaluation expands a split into the scalar convolution over lengths
and positive child weights. -/
theorem splitCounts_apply (I H : Table) (g : ℕ → ℕ → WeightRow) (n k : ℕ) :
    splitCounts I H g n k =
      ∑ ab ∈ Finset.antidiagonal n, ∑ i ∈ Finset.range ab.1, ∑ j ∈ Finset.range ab.2,
      I ab.1 (i+1) * H ab.2 (j+1) * g (i+1) (j+1) k := by
  simp [splitCounts, Finsupp.finsetSum_apply]

theorem links_apply (i q k : ℕ) :
    links i q k =
      ∑ h ∈ Finset.range (min i q), if i+q-1-2*h = k then 1 else 0 := by
  simp [links, Finsupp.finsetSum_apply, Finsupp.single_apply]

/-- Under the published support conditions, the histogram contains
exactly the original table entries (including zeros off the range). -/
theorem weights_apply (F : Table) (n k : ℕ) (h0 : F n 0 = 0)
    (hs : ∀ i, n < i → F n i = 0) : weights F n k = F n k := by
  cases k with
  | zero =>
    simp [weights, Finsupp.finsetSum_apply, h0]
  | succ k =>
    by_cases hk : k < n
    · simp [weights, Finsupp.finsetSum_apply, Finsupp.single_apply, hk]
    · simp [weights, Finsupp.finsetSum_apply, Finsupp.single_apply, hk, hs _ (by omega : n < k+1)]

/-- Pointwise constructor: equality of finite histograms in the structure
can equally well be discharged by the two ordinary scalar recurrences. -/
theorem Recurrences.of_pointwise {I H : Table}
    (i0 : ∀ n, I n 0 = 0) (h0 : ∀ n, H n 0 = 0)
    (isupp : ∀ n k, n < k → I n k = 0)
    (hsupp : ∀ n k, n < k → H n k = 0)
    (hs : ∀ n k, H n k = I n k +
      splitCounts I H (fun i j => Finsupp.single (i+j) 1) n k)
    (hi : ∀ n k, I n k = seed n k +
      splitCounts I H (fun i j => links i (j-1)) n k) : Recurrences I H where
  i_zero := i0
  h_zero := h0
  i_support := isupp
  h_support := hsupp
  sequence n := by
    ext k
    simpa [weights_apply I n k (i0 n) (isupp n), weights_apply H n k (h0 n) (hsupp n)]
      using hs n k
  earliest n := by
    ext k
    simpa [weights_apply I n k (i0 n) (isupp n)] using hi n k

private theorem split_congr_short {I H J K : Table} {n : ℕ}
    (shorter : ∀ m < n, I m = J m ∧ H m = K m) (g : ℕ → ℕ → WeightRow) :
    splitCounts I H g n = splitCounts J K g n := by
  unfold splitCounts
  apply Finset.sum_congr rfl
  intro ab hab
  have h := Finset.mem_antidiagonal.mp hab
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have ha := Finset.mem_range.mp hi
  have hb := Finset.mem_range.mp hj
  rw [(shorter ab.1 (by omega)).1, (shorter ab.2 (by omega)).2]

/-- The positive-length decomposition determines both tables uniquely. -/
theorem Recurrences.unique {I H J K : Table} (r : Recurrences I H) (s : Recurrences J K) :
    I = J ∧ H = K := by
  suffices aux : ∀ n, I n = J n ∧ H n = K n from
    ⟨funext fun n => (aux n).1, funext fun n => (aux n).2⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have same (g : ℕ → ℕ → WeightRow) := split_congr_short ih g
    have wi : weights I n = weights J n := by rw [r.earliest, s.earliest, same]
    have wh : weights H n = weights K n := by rw [r.sequence, s.sequence, wi, same]
    constructor
    · funext k
      simpa [weights_apply I n k (r.i_zero n) (r.i_support n),
        weights_apply J n k (s.i_zero n) (s.i_support n)]
        using congrArg (fun p : WeightRow => p k) wi
    · funext k
      simpa [weights_apply H n k (r.h_zero n) (r.h_support n),
        weights_apply K n k (s.h_zero n) (s.h_support n)]
        using congrArg (fun p : WeightRow => p k) wh


/-- One simultaneous update of the positive-length decomposition. `I`
is updated first, since the sequence rule includes a one-piece sequence. -/
private def sweep : ℕ → Table × Table
  | 0 => (fun _ _ => 0, fun _ _ => 0)
  | p+1 =>
    let (I,H) := sweep p
    let rowI (n : ℕ) := seed n + splitCounts I H (fun i j => links i (j-1)) n
    let rowH (n : ℕ) := rowI n + splitCounts I H (fun i j => Finsupp.single (i+j) 1) n
    (fun n k => rowI n k, fun n k => rowH n k)

/-- Canonical iterated recurrence at a fixed length. Only `n+1` sweeps
are used, since each nonempty split has strictly shorter children. -/
@[no_expose] def Irec (n : ℕ) := (sweep (n+1)).1 n
@[no_expose] def Hrec (n : ℕ) := (sweep (n+1)).2 n

private theorem sweep_stable (n : ℕ) : ∀ p q, n < p → n < q →
    (sweep p).1 n = (sweep q).1 n ∧ (sweep p).2 n = (sweep q).2 n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p q hp hq
    cases p with
    | zero => omega
    | succ p =>
      cases q with
      | zero => omega
      | succ q =>
        have eq := @split_congr_short (sweep p).1 (sweep p).2 (sweep q).1 (sweep q).2 n
          (fun m hm => ih m hm p q (by omega) (by omega))
        constructor
        · funext k
          change (seed n + splitCounts _ _ _ n) k = (seed n + splitCounts _ _ _ n) k
          rw [eq]
        · funext k
          change (seed n + splitCounts _ _ _ n + splitCounts _ _ _ n) k =
            (seed n + splitCounts _ _ _ n + splitCounts _ _ _ n) k
          simp only [eq]

private theorem split_support (I H : Table) (n k : ℕ) (bad : k = 0 ∨ n < k)
    (g : ℕ → ℕ → WeightRow)
    (hg : ∀ i j, 0 < i → 0 < j → k = 0 ∨ i+j < k → g i j k = 0) :
    splitCounts I H g n k = 0 := by
  rw [splitCounts_apply]
  apply Finset.sum_eq_zero
  intro ab hab
  have h := Finset.mem_antidiagonal.mp hab
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  have ha := Finset.mem_range.mp hi
  have hb := Finset.mem_range.mp hj
  rw [hg _ _ (by omega) (by omega) (by omega), mul_zero]

set_option maxHeartbeats 800000 in
/-- The recurrences are consistent: the canonical tables themselves
satisfy every base/support condition and both decomposition identities. -/
theorem recurrences_canonical : Recurrences Irec Hrec := by
  have eq (n : ℕ) (g : ℕ → ℕ → WeightRow) :
      splitCounts (sweep n).1 (sweep n).2 g n = splitCounts Irec Hrec g n :=
    split_congr_short (fun m hm => sweep_stable m n (m+1) hm (by omega)) g
  have ci (n k : ℕ) : Irec n k = seed n k + splitCounts Irec Hrec (fun i j => links i (j-1)) n k := by
    change (seed n + splitCounts (sweep n).1 (sweep n).2 _ n) k = _
    rw [eq, Finsupp.add_apply]
  have ch (n k : ℕ) : Hrec n k = Irec n k +
      splitCounts Irec Hrec (fun i j => Finsupp.single (i+j) 1) n k := by
    change Irec n k + splitCounts (sweep n).1 (sweep n).2 _ n k = _
    rw [eq]
  have badI (n k : ℕ) (bad : k=0 ∨ n<k) : Irec n k = 0 := by
    rw [ci, split_support _ _ _ _ bad, add_zero]
    · by_cases hn : n=1
      · simp [seed, hn, show 1 ≠ k by omega]
      · simp [seed, hn]
    · intro i j hi hj hh
      rw [links_apply]
      apply Finset.sum_eq_zero
      intro a ha
      have h := Finset.mem_range.mp ha
      exact ite_eq_right (by omega)
  have badH (n k : ℕ) (bad : k=0 ∨ n<k) : Hrec n k = 0 := by
    rw [ch, badI n k bad, zero_add]
    apply split_support _ _ _ _ bad
    intro i j hi hj hh
    simp [show i+j ≠ k by omega]
  exact Recurrences.of_pointwise (fun n => badI n 0 (Or.inl rfl))
    (fun n => badH n 0 (Or.inl rfl)) (fun n k hk => badI n k (Or.inr hk))
    (fun n k hk => badH n k (Or.inr hk)) ch ci

theorem Recurrences.eq_rec {I H : Table} (r : Recurrences I H) : I = Irec ∧ H = Hrec :=
  r.unique recurrences_canonical

section Transforms
open PowerSeries
variable {A : Type*} [CommRing A]

private abbrev ev (w : ℕ → A) := Finsupp.linearCombination ℕ w

private def series (row : ℕ → WeightRow) (w : ℕ → A) : PowerSeries A :=
  PowerSeries.mk (fun n => ev w (row n))

private abbrev gen (F : Table) (w : ℕ → A) := series (weights F) w

private theorem gen_coeff (F : Table) (w : ℕ → A) (n : ℕ) :
    coeff n (gen F w) = ∑ i ∈ Finset.range n, (F n (i+1) : A) * w (i+1) := by
  simp [gen, series, weights, ev, nsmul_eq_mul]

private theorem gen_const (F : Table) (w : ℕ → A) : constantCoeff (gen F w) = 0 := by
  simp [gen, series, weights]

private theorem gen_sub (F : Table) (f g : ℕ → A) :
    gen F (fun k => f k - g k) = gen F f - gen F g := by
  apply PowerSeries.ext
  intro n
  simp [gen_coeff, mul_sub, Finset.sum_sub_distrib]

private theorem gen_mul_sub (F : Table) (u v : A) (huv : u*v=1) :
    gen F (fun k => u^(k-1) - v^(k-1)) =
      C v * gen F (fun k => u^k) - C u * gen F (fun k => v^k) := by
  apply PowerSeries.ext
  intro n
  simp only [map_sub, coeff_C_mul, gen_coeff, Nat.add_sub_cancel, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [pow_succ]
  linear_combination -((F n (i+1) : A) * (u^i-v^i)) * huv

private theorem series_split (I H : Table) (g : ℕ → ℕ → WeightRow)
    (a : A) (w f h : ℕ → A)
    (rules : ∀ i j, a * ev w (g (i+1) (j+1)) = f (i+1) * h (j+1)) :
    C a * series (splitCounts I H g) w = gen I f * gen H h := by
  apply PowerSeries.ext
  intro n
  rw [coeff_C_mul, coeff_mul]
  simp only [gen_coeff, Finset.sum_mul]
  simp only [series, coeff_mk, splitCounts, map_sum, map_nsmul,
    nsmul_eq_mul, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ab _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  linear_combination (I ab.1 (i+1) : A) * (H ab.2 (j+1) : A) * rules i j

private theorem links_succ (i j : ℕ) :
    links (i+1) (j+1) = Finsupp.single (i+j+1) 1 + links i j := by
  unfold links
  rw [show min (i+1) (j+1) = min i j + 1 by omega, Finset.sum_range_succ']
  rw [add_comm]
  congr 1
  · congr 1; omega
  · apply Finset.sum_congr rfl
    intro k _
    congr 1; omega

/-- Cleared version of the Laurent Chebyshev product law. -/
private theorem links_character (u v : A) (huv : u*v=1) (i j : ℕ) :
    (u-v) * ev (fun k => u^k-v^k) (links i j) = (u^i-v^i)*(u^j-v^j) := by
  induction i generalizing j with
  | zero => simp [links]
  | succ i ih =>
    cases j with
    | zero => simp [links]
    | succ j =>
      rw [links_succ, map_add, mul_add, ih]
      simp only [ev, Finsupp.linearCombination_single, one_smul, pow_succ, pow_add]
      linear_combination -((u^i-v^i)*(u^j-v^j)) * huv

private theorem sequence_inv (I H : Table) (h : Recurrences I H) (u : A) :
    (1 + gen H (fun k => u^k)) * (1 - gen I (fun k => u^k)) = 1 := by
  let w := fun k : ℕ => u^k
  let g := fun i j : ℕ => Finsupp.single (i+j) (1:ℕ)
  have s : gen H w = gen I w + series (splitCounts I H g) w := by
    apply PowerSeries.ext
    intro n
    simp only [gen, series, map_add, coeff_mk, h.sequence, g]
  have eq := series_split I H g 1 w w w (fun i j => by simp [g,w,ev,pow_add])
  simp only [map_one, one_mul] at eq
  change (1 + gen H w) * (1 - gen I w) = 1
  linear_combination s + eq

private theorem seed_series (w : ℕ → A) : series seed w = X * C (w 1) := by
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [series, seed]
  | succ n => cases n <;> simp [series, seed, ev, coeff_X]

private theorem earliest_kernel (I H : Table) (h : Recurrences I H)
    (u v : A) (huv : u*v=1) :
    ((1 - gen I (fun k => v^k)) - (1 - gen I (fun k => u^k))) *
      (C u * (1 + gen H (fun k => v^k)) - C v * (1 + gen H (fun k => u^k))) =
      X * (C u - C v)^2 := by
  let w := fun k : ℕ => u^k - v^k
  let w' := fun k : ℕ => u^(k-1) - v^(k-1)
  let g := fun i j : ℕ => links i (j-1)
  have s : gen I w = X * C (u-v) + series (splitCounts I H g) w := by
    have aux : gen I w = series seed w + series (splitCounts I H g) w := by
      apply PowerSeries.ext
      intro n
      simp only [gen, series, map_add, coeff_mk, h.earliest, g]
    simpa [seed_series, w, pow_one] using aux
  have eq := series_split I H g (u-v) w w w' (fun i j => by
    simpa [w, w', g] using links_character u v huv (i+1) j)
  have cut : C (u-v) * gen I w = X * (C (u-v))^2 + gen I w * gen H w' := by
    linear_combination (C (u-v)) * s + eq
  dsimp [w,w'] at cut
  rw [gen_sub, gen_mul_sub H u v huv, map_sub] at cut
  linear_combination cut

end Transforms

section WalkSeries

open PowerSeries
variable {A : Type*} [CommRing A]

/-- The polynomial of walks ending at height `y`. Horizontal steps have combined
weight `s`. Reflection accounts for the two neighbours of zero. -/
def walkRow (s : A) : ℕ → ℕ → A
  | 0, y => if y = 0 then 1 else 0
  | n + 1, 0 => s * walkRow s n 0 + walkRow s n 1 + walkRow s n 1
  | n + 1, y + 1 => s * walkRow s n (y+1) + walkRow s n y + walkRow s n (y+2)

private theorem walkRow_vanish (s : A) {n y : ℕ} (h : n < y) : walkRow s n y = 0 := by
  induction n generalizing y with
  | zero => simp [walkRow, Nat.ne_of_gt h]
  | succ n ih =>
    cases y with
    | zero => omega
    | succ y => simp [walkRow, ih (show n < y + 1 by omega),
        ih (show n < y by omega), ih (show n < y + 2 by omega)]

noncomputable def walkSeries (s : A) (y : ℕ) : PowerSeries A :=
  PowerSeries.mk fun n => walkRow s n y

private theorem walkSeries_zero (s : A) :
    walkSeries s 0 = 1 + X * (C s * walkSeries s 0 + walkSeries s 1 + walkSeries s 1) := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [walkSeries, walkRow, coeff_C_mul]

private theorem walkSeries_succ (s : A) (y : ℕ) :
    walkSeries s (y + 1) =
      X * (C s * walkSeries s (y + 1) + walkSeries s y + walkSeries s (y + 2)) := by
  apply PowerSeries.ext
  intro n
  cases n <;> simp [walkSeries, walkRow, coeff_C_mul]

/-- The half-line walk recurrence has a conserved quadratic expression in
two successive height generating functions. It vanishes at arbitrary
order by finite propagation, so it vanishes already at height zero. -/
theorem walkSeries_discriminant (s : A) :
    ((1 - X * C s)^2 - 4 * X^2) * (walkSeries s 0)^2 = 1 := by
  let f := walkSeries s
  let b : PowerSeries A := 1 - X * C s
  let q (y : ℕ) := X * (f y ^ 2 + f (y+1) ^ 2) - b * f y * f (y+1)
  have hstep (y : ℕ) : b * f (y+1) = X * (f y + f (y+2)) := by
    dsimp [b, f]
    linear_combination walkSeries_succ s y
  have hbase : b * f 0 - 2 * X * f 1 = 1 := by
    dsimp [b, f]
    linear_combination walkSeries_zero s
  have hq (y : ℕ) : q y = q 0 := by
    induction y with
    | zero => rfl
    | succ y ih =>
      rw [← ih]
      dsimp [q]
      linear_combination (f y - f (y+2)) * hstep y
  have hdvd (a y : ℕ) (h : a ≤ y) : X ^ a ∣ f y := by
    apply X_pow_dvd_iff.mpr
    intro i hi
    simpa [f, walkSeries] using walkRow_vanish s (show i < y by omega)
  have hz : q 0 = 0 := by
    apply PowerSeries.ext
    intro n
    obtain ⟨u, hu⟩ := hdvd (n+1) (n+1) le_rfl
    obtain ⟨v, hv⟩ := hdvd (n+1) (n+2) (by omega)
    have hD : X ^ (n+1) ∣ q (n+1) := by
      use X * (u * f (n+1) + v * f (n+2)) - b * u * f (n+2)
      dsimp [q]
      rw [hu, hv]
      ring
    rw [← hq (n+1)]
    simpa using X_pow_dvd_iff.mp hD n (Nat.lt_succ_self n)
  change (b^2 - 4 * X^2) * (f 0)^2 = 1
  dsimp [q] at hz
  linear_combination (b * f 0 - 2*X*f 1 + 1) * hbase - 4 * X * hz

end WalkSeries

section Kernel
open PowerSeries

variable {A : Type*} [CommRing A] [IsDomain A]

/-- Algebra of the quadratic kernel. The two prefix series are represented
with their inverses explicitly, so no fractions or square roots are needed. -/
private theorem kernel_log_derivative (u v : A) (huv : u * v = 1) (hne : u ≠ v) (h2 : (2:A) ≠ 0)
    (P Q Pi Qi : PowerSeries A)
    (hp : P * Pi = 1) (hq : Q * Qi = 1)
    (cp : constantCoeff P = 1) (cq : constantCoeff Q = 1)
    (cpi : constantCoeff Pi = 1) (cqi : constantCoeff Qi = 1)
    (hk : (Qi - Pi) * (C u * Q - C v * P) = X * (C u - C v)^2) :
    derivative P * Pi - derivative Q * Qi = (C u - C v) * walkSeries (u+v) 0 := by
  let U : PowerSeries A := C u
  let V : PowerSeries A := C v
  let r := P * Qi
  let t := Q * Pi
  let l := derivative P * Pi - derivative Q * Qi
  let b := U*t - V*r
  let W := walkSeries (u+v) 0
  have uv : U*V = 1 := by simp [U, V, ← map_mul, huv]
  have uvne : U ≠ V := fun h => hne (by simpa [U,V] using congrArg constantCoeff h)
  have rt : r * t = 1 := by
    change P * Qi * (Q * Pi) = 1
    calc
      _ = (P * Pi) * (Q * Qi) := by ring
      _ = 1 := by rw [hp, hq]; ring
  have quad : U*t + V*r = U+V-X*(U-V)^2 := by
    dsimp [U,V,r,t]
    linear_combination -hk + C u * hq + C v * hp
  have dpi : derivative Pi = -(derivative P * Pi^2) := by
    have h := congrArg derivative hp
    simp only [Derivation.leibniz, smul_eq_mul, derivative_one] at h
    linear_combination Pi * h - derivative Pi * hp
  have dqi : derivative Qi = -(derivative Q * Qi^2) := by
    have h := congrArg derivative hq
    simp only [Derivation.leibniz, smul_eq_mul, derivative_one] at h
    linear_combination Qi * h - derivative Qi * hq
  have dr : derivative r = l * r := by
    dsimp [r,l]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, dqi]
    linear_combination -(derivative P * Qi) * hp
  have dt : derivative t = -(l * t) := by
    dsimp [t,l]
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, dpi]
    linear_combination -(derivative Q * Pi) * hq
  have derivK : b * l = (U-V)^2 := by
    have h := congrArg derivative quad
    simp only [map_add, map_sub, Derivation.leibniz, smul_eq_mul, derivative_pow,
      show derivative U = 0 by simp [U], show derivative V = 0 by simp [V],
      dr, dt, derivative_X, sub_self, add_zero, mul_zero, zero_add] at h
    dsimp [b]
    linear_combination -h
  have discr : b^2 = (U-V)^2 * ((1-X*(U+V))^2-4*X^2) := by
    calc
      _ = (U*t+V*r)^2 - 4*(U*V)*(r*t) := by dsimp [b]; ring
      _ = _ := by
        rw [quad, uv, rt]
        linear_combination (4 - 4*X^2*(U-V)^2) * uv
  have sq : (b * W)^2 = (U-V)^2 := by
    have h : ((1-X*(U+V))^2-4*X^2)*W^2 = 1 := by
      simpa [U, V, W] using walkSeries_discriminant (u+v)
    rw [mul_pow, discr, mul_assoc, h, mul_one]
  have bw : b * W = U - V := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp sq with e|e
    · exact e
    · have h := congrArg constantCoeff e
      simp [b, W, r, t, U, V, cp, cq, cpi, cqi, walkSeries, walkRow] at h
      exfalso
      exact hne (by
        have hz : (2:A) * (u-v) = 0 := by linear_combination h
        exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left h2))
  change l = (U-V) * W
  apply mul_left_cancel₀ (sub_ne_zero.mpr uvne)
  linear_combination -l * bw + W * derivK
end Kernel
section Coefficients

open PowerSeries
private abbrev L := LaurentPolynomial ℤ
private abbrev T (e : ℤ) : L := LaurentPolynomial.T e

private def pick (x : ℤ) : L →+ ℤ where
  toFun p := p.coeff x
  map_zero' := by simp
  map_add' := by simp

@[simp] private theorem pick_T (x e : ℤ) : pick x (T e) = if e=x then 1 else 0 :=
  LaurentPolynomial.T_apply ..
@[simp] private theorem pick_one (x : ℤ) : pick x 1 = if (0:ℤ)=x then 1 else 0 := by
  simpa only [T, LaurentPolynomial.T_zero] using pick_T x 0

private theorem pick_T_mul (x e : ℤ) (p : L) :
    pick x (T e * p) = pick (x-e) p := by
  induction p using LaurentPolynomial.induction_on' with
  | add a b ha hb => simp only [mul_add, map_add, ha, hb]
  | C_mul_T k c =>
    change (T e * (LaurentPolynomial.C c * T k)).coeff x =
      (LaurentPolynomial.C c * T k).coeff (x-e)
    rw [mul_comm (T e), LaurentPolynomial.mul_T_assoc]
    simp only [T, ← LaurentPolynomial.single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs <;> first | rfl | omega

private theorem axial_reflect (n : ℕ) (x y : ℤ) :
    axialWalks n x (-y) = axialWalks n x y := by
  induction n generalizing x y with
  | zero => simp [axialWalks]
  | succ n ih =>
    simp only [axialWalks, show -y-1 = -(y+1) by ring,
      show -y+1 = -(y-1) by ring, ih]
    omega

private theorem walk_coeff (n y : ℕ) (x : ℤ) :
    pick x (walkRow (T 1 + T (-1)) n y) = (axialWalks n x y : ℤ) := by
  induction n generalizing x y with
  | zero =>
    cases y <;> by_cases hx : x = 0 <;> simp [walkRow, axialWalks, hx, eq_comm]; omega
  | succ n ih =>
    cases y with
    | zero =>
      have hy := axial_reflect n x 1
      simp [-LaurentPolynomial.T_mul, walkRow, add_mul, pick_T_mul, ih, axialWalks, hy]
    | succ y =>
      simp [-LaurentPolynomial.T_mul, walkRow, add_mul, pick_T_mul, ih, axialWalks, Nat.cast_add, Nat.cast_succ,
        add_assoc]

private abbrev marked (F : Table) (e : ℤ) := gen F (fun k => (T e)^k)

private theorem pick_scale (x : ℤ) (m : ℕ) (p : L) :
    pick x ((m:L) * p) = (m:ℤ) * pick x p := by
  simp only [← nsmul_eq_mul, map_nsmul]

private theorem marked_pair (F G : Table) (e : ℤ) (he : e = 1 ∨ e = -1) (a b : ℕ) :
    pick 1 (coeff a (marked F e) * coeff b (marked G e)) = 0 := by
  simp only [marked, gen_coeff, Finset.sum_mul]
  simp only [Finset.mul_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have m : (F a (i+1) : L) * (T e)^(i+1) * ((G b (j+1):L) * (T e)^(j+1)) =
      ((F a (i+1) * G b (j+1) : ℕ) : L) * (T e)^((i+1)+(j+1)) := by
    rw [Nat.cast_mul, pow_add]; ring
  rw [m, pick_scale, LaurentPolynomial.T_pow, pick_T]
  have ne : ((↑((i+1)+(j+1) : ℕ) : ℤ) * e) ≠ 1 := by
    rcases he with rfl|rfl <;> push_cast <;> omega
  rw [ite_eq_right ne, mul_zero]

private theorem marked_dprod (F G : Table) (e : ℤ) (he : e = 1 ∨ e = -1) (n : ℕ) :
    pick 1 (coeff n (derivative (marked F e) * marked G e)) = 0 := by
  rw [coeff_mul, map_sum]
  apply Finset.sum_eq_zero
  intro p _
  rw [coeff_derivative]
  have h : (coeff (p.1+1) (marked F e) * (↑p.1+1)) * coeff p.2 (marked G e) =
      ((p.1+1:ℕ):L) * (coeff (p.1+1) (marked F e) * coeff p.2 (marked G e)) := by
    push_cast
    ring
  rw [h, pick_scale, marked_pair F G e he, mul_zero]

private theorem marked_pos (F : Table) (n : ℕ) :
    pick 1 (coeff (n+1) (marked F 1)) = F (n+1) 1 := by
  rw [gen_coeff, map_sum, Finset.sum_range_succ']
  have vanish (i : ℕ) : pick 1 ((F (n+1) (i+1+1):L) * T 1 ^ (i+1+1)) = 0 := by
    rw [pick_scale, LaurentPolynomial.T_pow, pick_T, ite_eq_right (by push_cast; omega), mul_zero]
  simp only [vanish, Finset.sum_const_zero, zero_add, pow_one, pick_scale, pick_T]
  simp

private theorem marked_neg (F : Table) (n : ℕ) :
    pick 1 (coeff n (marked F (-1))) = 0 := by
  simp only [marked, gen_coeff, map_sum, pick_scale, LaurentPolynomial.T_pow, pick_T]
  apply Finset.sum_eq_zero
  intro i _
  have neg : ((↑(i+1 : ℕ) : ℤ)) * -1 ≠ 1 := by omega
  rw [ite_eq_right neg, mul_zero]

private theorem first_log (I H : Table) (n : ℕ) (e : ℤ) (he : e = 1 ∨ e = -1) :
    pick 1 (coeff n (derivative (1 + marked H e) * (1 - marked I e))) =
      ((n+1:ℕ):ℤ) * pick 1 (coeff (n+1) (marked H e)) := by
  simp only [map_add, derivative_one, zero_add, mul_sub, mul_one, map_sub,
    marked_dprod H I e he n, sub_zero, coeff_derivative]
  rw [mul_comm]
  simpa only [Nat.cast_add, Nat.cast_one] using
    pick_scale 1 (n+1) (coeff (n+1) (marked H e))

/-- All-length coefficient equation, before specializing the axial-walk
coefficient to even length. -/
theorem weight_one_walks (I H : Table) (h : Recurrences I H) (n : ℕ) :
    ((n+1:ℕ):ℤ) * H (n+1) 1 = (axialWalks n 0 0 : ℤ) - axialWalks n 2 0 := by
  have huv : T 1 * T (-1) = 1 := by rw [← LaurentPolynomial.T_add]; norm_num [T]
  have hne : T 1 ≠ T (-1) := by
    intro eq
    have h' := congrArg (pick 1) eq
    norm_num at h'
  have h2 : (2:L) ≠ 0 := by
    intro hz
    have h' : (1:L) + 1 = 0 := by simpa only [one_add_one_eq_two] using hz
    have e := congrArg (pick 0) h'
    rw [map_add, map_zero, pick_one] at e
    norm_num at e
  have k := kernel_log_derivative (T 1) (T (-1)) huv hne h2
    (1+marked H 1) (1+marked H (-1)) (1-marked I 1) (1-marked I (-1))
    (sequence_inv I H h (T 1)) (sequence_inv I H h (T (-1)))
    (by simp [marked, gen_const]) (by simp [marked, gen_const])
    (by simp [marked, gen_const]) (by simp [marked, gen_const])
    (earliest_kernel I H h (T 1) (T (-1)) huv)
  have eq := congrArg (fun p : PowerSeries L => pick 1 (coeff n p)) k
  simp only [map_sub, sub_mul, coeff_C_mul, walkSeries, coeff_mk, pick_T_mul,
    first_log I H n 1 (Or.inl rfl), first_log I H n (-1) (Or.inr rfl)] at eq
  simpa [marked_pos, marked_neg, walk_coeff] using eq

/-- The positive weight-one table entry for any two Section 3 tables. -/
theorem count_weight_one_eq_catalan_sq (I H : ℕ → ℕ → ℕ) (h : Recurrences I H) (m : ℕ) :
    H (2*m+1) 1 = catalan m ^ 2 := by
  have e := weight_one_walks I H h (2*m)
  rw [walk_coefficient m] at e
  have h' : ((2*m+1:ℕ):ℤ) * (H (2*m+1) 1 : ℤ) =
      ((2*m+1:ℕ):ℤ) * (catalan m ^ 2 : ℕ) := by push_cast at *; linear_combination e
  exact_mod_cast mul_left_cancel₀ (show ((2*m+1:ℕ):ℤ) ≠ 0 by omega) h'

theorem count_weight_one_shift (I H : Table) (h : Recurrences I H) {n : ℕ} (hn : 1 ≤ n) :
    H (2*n-1) 1 = catalan (n-1) ^ 2 := by
  rw [show 2*n-1 = 2*(n-1)+1 by omega]
  exact count_weight_one_eq_catalan_sq I H h _

private theorem walk_parity (n : ℕ) (x y : ℤ) (h : (x+y-n)%2 ≠ 0) :
    axialWalks n x y = 0 := by
  induction n generalizing x y with
  | zero => unfold axialWalks; split_ifs <;> omega
  | succ n ih =>
    rw [axialWalks, ih (x-1) y (by omega), ih (x+1) y (by omega),
      ih x (y-1) (by omega), ih x (y+1) (by omega)]

theorem count_even_weight_one (I H : Table) (h : Recurrences I H) (m : ℕ) :
    H (2*m) 1 = 0 := by
  cases m with
  | zero => exact h.h_support 0 1 (by decide)
  | succ m =>
    have e := weight_one_walks I H h (2*m+1)
    rw [walk_parity _ _ _ (by omega), walk_parity _ _ _ (by omega)] at e
    have hz : (H (2*m+1+1) 1 : ℤ) = 0 :=
      (mul_eq_zero.mp (by simpa using e)).resolve_left (by positivity)
    simpa [Nat.mul_succ, Nat.add_assoc] using (Nat.cast_eq_zero.mp hz)

end Coefficients

end
end NabergallChordalDiagrams.Series
