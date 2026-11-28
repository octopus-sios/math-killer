import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Lift
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Centred Gaussian differences: coefficient estimates

All series here are over the integers. The height and width of a rectangle are
independent parameters. The defining denominator inverses are checked below.
-/

namespace ReinerStanton

open PowerSeries
open scoped BigOperators
noncomputable section

abbrev S := PowerSeries ℤ
private abbrev Xs : S := X

/-- The series 1/(1-X^j) for positive j. -/
def geom (j : ℕ) : S := mk fun n => if j ∣ n then 1 else 0

theorem geom_cancel {j : ℕ} (hj : 0 < j) : (1 - Xs ^ j) * geom j = 1 := by
  ext n
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one]
  simp only [geom, coeff_mk]
  by_cases h : j ≤ n
  · rw [ite_eq_left h]
    have hh : j ∣ n - j ↔ j ∣ n := by
      constructor
      · intro ha
        simpa [Nat.sub_add_cancel h] using dvd_add ha (dvd_refl j)
      · exact fun ha => Nat.dvd_sub ha (dvd_refl j)
    rw [if_congr hh rfl rfl, sub_self, ite_eq_right (by omega)]
  · rw [ite_eq_right h, sub_zero]
    by_cases hn : n = 0
    · simp [hn]
    · have nd : ¬ j ∣ n := fun hd => h (Nat.le_of_dvd (by omega) hd)
      simp [nd, hn]

def numerator : ℕ → ℕ → S
  | 0, _ => 1
  | k+1, L => (1 - Xs ^ (L+k+1)) * numerator k L

/-- Inverse denominator after cancelling the first factor 1-X:
`parts r` allows parts of sizes 2 through r+2. -/
def parts : ℕ → S
  | 0 => geom 2
  | r+1 => parts r * geom (r+3)

/-- Product-formula Gaussian polynomial of height r+2 and width L, embedded
as its formal series at zero. -/
def gaussian (r L : ℕ) : S := geom 1 * (numerator (r+2) L * parts r)

theorem gaussian_gap (r L : ℕ) :
    (1-Xs) * gaussian r L = numerator (r+2) L * parts r := by
  rw [gaussian, ← mul_assoc]
  have h := geom_cancel (j := 1) (by decide)
  simpa [pow_one] using congrArg (fun a => a * (numerator (r+2) L * parts r)) h

private def Pos (p : S) : Prop := ∀ n, 0 ≤ coeff n p

private theorem pos_mul {p q : S} (hp : Pos p) (hq : Pos q) : Pos (p*q) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg fun ij _ => mul_nonneg (hp _) (hq _)

private theorem geom_pos (j : ℕ) : Pos (geom j) := by
  intro n
  simp only [geom, coeff_mk]
  split <;> decide

private theorem pos_geom_sub_one (j : ℕ) : Pos (geom j - 1) := by
  intro n
  rw [map_sub, coeff_one]
  by_cases h : n = 0
  · simp [h, geom]
  · simpa [h] using geom_pos j n

private theorem pos_parts (r : ℕ) : Pos (parts r) := by
  induction r with
  | zero => exact geom_pos _
  | succ r ih => exact pos_mul ih (geom_pos _)

private theorem pos_raise (r : ℕ) : Pos (parts (r+1) - parts r) := by
  simpa [parts, mul_sub] using pos_mul (pos_parts r) (pos_geom_sub_one (r+3))

private theorem pos_shift (s : ℕ) {p : S} (h : Pos p) : Pos (Xs^s * p) := by
  intro n
  rw [coeff_X_pow_mul']
  split
  · exact h _
  · exact le_rfl

private theorem pos_step_two (r : ℕ) : Pos ((1-Xs^2)*parts r) := by
  induction r with
  | zero =>
    rw [parts, geom_cancel (by decide)]
    intro n
    simp only [coeff_one]
    split <;> decide
  | succ r ih => simpa only [parts, ← mul_assoc] using pos_mul ih (geom_pos (r+3))

private theorem pos_step_three (r : ℕ) : Pos ((1-Xs^3)*parts (r+1)) := by
  induction r with
  | zero =>
    change Pos ((1-Xs^3)*(parts 0 * geom 3))
    rw [mul_left_comm, geom_cancel (by decide), mul_one]
    exact pos_parts _
  | succ r ih => simpa only [parts, ← mul_assoc] using pos_mul ih (geom_pos (r+4))

private theorem pos_step_add {a b : ℕ} {p : S}
    (ha : Pos ((1-Xs^a)*p)) (hb : Pos ((1-Xs^b)*p)) :
    Pos ((1-Xs^(a+b))*p) := by
  have e : (1-Xs^(a+b))*p = (1-Xs^a)*p + Xs^a*((1-Xs^b)*p) := by rw [pow_add]; ring
  rw [e]
  intro n
  simpa using add_nonneg (ha n) (pos_shift a hb n)

private theorem pos_step (r s : ℕ) (hs : s ≠ 1) : Pos ((1-Xs^s)*parts (r+1)) := by
  induction s using Nat.strong_induction_on with
  | h s ih =>
    rcases s with _ | _ | _ | _ | t
    · intro n; simp
    · contradiction
    · exact pos_step_two _
    · exact pos_step_three _
    · exact pos_step_add (a := t+2) (b := 2) (p := parts (r+1))
        (ih (t+2) (by omega) (by omega)) (pos_step_two (r+1))

theorem numerator_edge (k L n : ℕ) (hl : n ≤ L) (p : S) :
    coeff n (numerator k L * p) = coeff n p := by
  induction k with
  | zero => simp [numerator]
  | succ k ih =>
    rw [numerator, mul_assoc, sub_mul, one_mul, map_sub, coeff_X_pow_mul', ite_eq_right (by omega),
      sub_zero, ih]

/-- Left edge of (iv). The large rectangle has height r+5, the small one r+3. -/
theorem edge (r L A s n : ℕ) (hc : (r+3)*A + 2*s = (r+5)*L)
    (hl : n ≤ L) (hs : s ≠ 1) :
    0 ≤ coeff n ((1-Xs) * (gaussian (r+3) L - Xs^s * gaussian (r+1) A)) := by
  rw [mul_sub, mul_left_comm (1-Xs) (Xs^s), gaussian_gap, gaussian_gap, map_sub,
    numerator_edge _ _ _ hl, coeff_X_pow_mul']
  by_cases hn : s ≤ n
  · rw [ite_eq_left hn]
    have hA : L ≤ A := by
      by_contra! hh
      nlinarith [Nat.mul_lt_mul_of_pos_left hh (show 0 < r+3 by omega)]
    rw [numerator_edge _ _ _ (by omega)]
    have t := pos_step r s hs n
    simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul', ite_eq_left hn] at t
    have h₁ := pos_raise (r+1) n
    have h₂ := pos_raise (r+2) n
    simp only [map_sub] at h₁ h₂
    linarith
  · rw [ite_eq_right hn, sub_zero]
    exact pos_parts _ _

/-- Coefficient growth of the restricted partition denominator, before the
numerator factors are applied. -/
theorem parts_bound (r n : ℕ) : coeff n (parts r) ≤ ((n:ℤ)+1)^r := by
  induction r generalizing n with
  | zero => simp [parts, geom]; split <;> decide
  | succ r ih =>
    rw [parts, coeff_mul]
    calc
      _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal n, ((n:ℤ)+1)^r := by
        apply Finset.sum_le_sum
        intro ij hij
        have he : ij.1 + ij.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        have hi : (ij.1 : ℤ) ≤ n := by exact_mod_cast (show ij.1 ≤ n by omega)
        have hx : coeff ij.1 (parts r) ≤ ((n:ℤ)+1)^r :=
          (ih _).trans (pow_le_pow_left₀ (by positivity) (by linarith) r)
        simp only [geom, coeff_mk]
        split
        · simpa using hx
        · simp; positivity
      _ = _ := by simp [pow_succ]; ring

private theorem numerator_bound (k L n : ℕ) (p : S) (B : ℤ)
    (hp : ∀ i ≤ n, |coeff i p| ≤ B) :
    ∀ i ≤ n, |coeff i (numerator k L * p)| ≤ 2^k * B := by
  have hB := (abs_nonneg _).trans (hp 0 (Nat.zero_le n))
  induction k with
  | zero => simpa [numerator] using hp
  | succ k ih =>
    intro i hi
    rw [numerator, mul_assoc, sub_mul, one_mul, map_sub, coeff_X_pow_mul']
    by_cases h : L+k+1 ≤ i
    · rw [ite_eq_left h]
      have ha := ih i hi
      have hb := ih (i-(L+k+1)) (by omega)
      exact (abs_sub _ _).trans (by rw [pow_succ]; linarith)
    · rw [ite_eq_right h, sub_zero]
      have hx := ih i hi
      have hy : 0 ≤ (2:ℤ)^k * B := by positivity
      rw [pow_succ]
      linarith

/-- Absolute first-difference bound, uniform in the width. -/
theorem gap_bound (r A n : ℕ) :
    |coeff n ((1-Xs)*gaussian r A)| ≤ 2^(r+2) * ((n:ℤ)+1)^r := by
  rw [gaussian_gap]
  apply numerator_bound _ _ n _ _ _ n le_rfl
  intro i hi
  rw [abs_of_nonneg (pos_parts r i)]
  exact (parts_bound r i).trans (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ hi) r)


/-! ## Product formula, reflection, and centred differences -/

/-- Coefficients extended by zero to negative integer indices. -/
def atZ (p : S) (n : ℤ) : ℤ :=
  if 0 ≤ n then coeff n.toNat p else 0

@[simp] private theorem atZ_nat (p : S) (n : ℕ) : atZ p n = coeff n p := by
  simp [atZ]

private theorem zadd (p q : S) (n : ℤ) : atZ (p+q) n = atZ p n + atZ q n := by
  simp only [atZ, map_add]; split <;> simp_all

private theorem zsub (p q : S) (n : ℤ) : atZ (p-q) n = atZ p n - atZ q n := by
  simp only [atZ, map_sub]; split <;> simp_all

private theorem zshift (a : ℕ) (p : S) (n : ℤ) :
    atZ (Xs^a * p) n = atZ p (n-a) := by
  unfold atZ
  by_cases hn : 0 ≤ n
  · rw [ite_eq_left hn, coeff_X_pow_mul']
    by_cases ha : (a:ℤ) ≤ n
    · rw [ite_eq_left (show a ≤ n.toNat by omega), ite_eq_left (by omega)]
      rw [show n.toNat - a = (n-(a:ℤ)).toNat by omega]
    · rw [ite_eq_right (show ¬ a ≤ n.toNat by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right hn, ite_eq_right (by omega)]

private theorem zΔ (p : S) (n : ℤ) : atZ ((1-Xs)*p) n = atZ p n - atZ p (n-1) := by
  calc
    _ = atZ p n - atZ (Xs^1*p) n := by rw [pow_one,sub_mul,one_mul,zsub]
    _ = _ := by rw [zshift]; norm_num

private theorem coeff_gap_succ (p : S) (i : ℕ) :
    coeff (i+1) ((1-Xs)*p) = coeff (i+1) p - coeff i p := by
  simpa only [show ((i+1:ℕ):ℤ)-1 = (i:ℤ) by omega, atZ_nat] using zΔ p (i+1:ℕ)
private theorem zone (n : ℤ) : atZ 1 n = if n = 0 then 1 else 0 := by
  simp only [atZ, coeff_one]
  split_ifs <;> omega

private def invDen : ℕ → S
  | 0 => 1
  | k+1 => geom (k+1) * invDen k

private def box (k L : ℕ) : S := numerator k L * invDen k

private theorem box_eq (r L : ℕ) : box (r+2) L = gaussian r L := by
  have hh (t : ℕ) : invDen (t+2) = geom 1 * parts t := by
    induction t with
    | zero => simp [invDen, parts, mul_comm]
    | succ t ih => change geom (t+3) * invDen (t+2) = _
                   rw [ih, parts]; ring
  rw [box, hh, gaussian]; ring

private theorem num_move (k L : ℕ) :
    numerator (k+1) L = (1-Xs^(L+1)) * numerator k (L+1) := by
  induction k with
  | zero => simp [numerator]
  | succ k ih =>
    rw [numerator, ih]
    conv_rhs => rw [numerator]
    rw [mul_left_comm, show L+(k+1)+1 = L+1+k+1 by omega]

private theorem box_width_zero (k : ℕ) : box k 0 = 1 := by
  induction k with
  | zero => simp [box, numerator, invDen]
  | succ k ih =>
    change ((1-Xs^(0+k+1))*numerator k 0) * (geom (k+1)*invDen k) = _
    rw [zero_add,mul_mul_mul_comm,geom_cancel (Nat.succ_pos k),one_mul]; exact ih

private theorem box_rec (k L : ℕ) :
    box (k+1) (L+1) = box k (L+1) + Xs^(k+1) * box (k+1) L ∧
    box (k+1) (L+1) = Xs^(L+1) * box k (L+1) + box (k+1) L := by
  let p := numerator k (L+1) * invDen (k+1)
  have h₁ : box k (L+1) = (1-Xs^(k+1)) * p := by
    unfold box p; rw [invDen]
    calc
      _ = ((1-Xs^(k+1))*geom (k+1)) * (numerator k (L+1)*invDen k) := by
        rw [geom_cancel (Nat.succ_pos k), one_mul]
      _ = _ := by ring
  have h₂ : box (k+1) L = (1-Xs^(L+1)) * p := by
    simp only [box, num_move k L, p, mul_assoc]
  have h₃ : box (k+1) (L+1) = (1-Xs^((L+1)+(k+1))) * p := by
    simp only [box, numerator, p, Nat.add_assoc, mul_assoc]
  rw [h₁,h₂,h₃,pow_add]; constructor <;> ring

/-- Reflection about d/2, on all integer indices (in particular including support). -/
def Reflects (p : S) (d : ℕ) : Prop := ∀ n : ℤ, atZ p n = atZ p ((d:ℤ)-n)

private theorem one_reflects : Reflects 1 0 := by
  intro n; simp [zone]

private theorem box_reflects (k L : ℕ) : Reflects (box k L) (k*L) := by
  induction k generalizing L with
  | zero => simpa [box, numerator, invDen] using one_reflects
  | succ k ih =>
    induction L with
    | zero => simpa [box_width_zero] using one_reflects
    | succ L ihL =>
      intro n
      conv_lhs => rw [(box_rec k L).1, zadd, zshift]
      conv_rhs => rw [(box_rec k L).2, zadd, zshift]
      rw [ih (L+1) n, ihL (n-↑(k+1))]
      push_cast; congr 2 <;> ring

theorem gaussian_reflects (r L : ℕ) : Reflects (gaussian r L) ((r+2)*L) := by
  rw [← box_eq]; exact box_reflects _ _

/-- Interval polynomial of length a (zero for a=0). -/
private def seg : ℕ → S
  | 0 => 0
  | a+1 => seg a + Xs^a

private theorem seg_add (a b : ℕ) : seg (a+b) = seg a + Xs^a * seg b := by
  induction b with
  | zero => simp [seg]
  | succ b ih =>
    change seg (a+b) + Xs^(a+b) = seg a + Xs^a * (seg b + Xs^b)
    rw [ih, pow_add]; ring

private theorem Δseg (a : ℕ) : (1-Xs)*seg a = 1-Xs^a := by
  induction a with
  | zero => simp [seg]
  | succ a ih => rw [seg, mul_add, ih, pow_succ]; ring

private theorem sym_seg_mul {p : S} {d : ℕ} (hp : Reflects p d) (a : ℕ) :
    Reflects (seg (a+1)*p) (a+d) := by
  induction a with
  | zero => simpa [seg] using hp
  | succ a ih =>
    intro n
    conv_lhs => rw [seg, add_mul, zadd, zshift]
    conv_rhs => rw [show seg (a+1+1) = 1+Xs^(1:ℕ)*seg (a+1) by
                      simpa only [show 1+(a+1) = a+1+1 by omega,
                        show seg 1 = 1 by simp [seg]] using seg_add 1 (a+1),
                    add_mul, one_mul, mul_assoc, zadd, zshift]
    rw [ih n, hp (n-↑(a+1)), add_comm]
    push_cast; congr 2 <;> ring

private theorem sym_cube (k L : ℕ) : Reflects ((seg (L+1))^k) (k*L) := by
  induction k with
  | zero => simpa using one_reflects
  | succ k ih => simpa [pow_succ', Nat.succ_mul, Nat.add_comm] using sym_seg_mul ih L

/-- The two arguments to gaussian are the height minus two and the width. -/
def centred (r L A s : ℕ) := gaussian (r+3) L - Xs^s * gaussian (r+1) A

theorem centred_reflects (r L A s : ℕ) (hc : (r+3)*A + 2*s = (r+5)*L) :
    Reflects (centred r L A s) ((r+5)*L) := by
  intro n
  simp only [centred, zsub, zshift]
  rw [gaussian_reflects (r+3) L n, gaussian_reflects (r+1) A (n-s)]
  have h : ((r:ℤ)+3)*A+2*s=((r:ℤ)+5)*L := by exact_mod_cast hc
  push_cast; congr 2; linarith


/-! ## Coefficient estimates uniform in the width

A tame multiplier is built from unit monomials of arbitrary (possibly
width-dependent) degree with a *fixed* number of ring operations. -/

private abbrev Fam := ℕ → S
private def Growth (e : ℕ) (p : Fam) := ∃ C : ℕ, ∀ L n : ℕ,
    |coeff n (p L)| ≤ (C:ℤ) * ((n:ℤ)+1)^e

private inductive Tame : Fam → Prop
  | zero : Tame (fun _ => 0)
  | one : Tame (fun _ => 1)
  | mon (j : ℕ → ℕ) : Tame (fun L => Xs^(j L))
  | add {p q} : Tame p → Tame q → Tame (fun L => p L + q L)
  | sub {p q} : Tame p → Tame q → Tame (fun L => p L - q L)
  | mul {p q} : Tame p → Tame q → Tame (fun L => p L * q L)

private theorem growth_add {p q : Fam} {e : ℕ} (hp : Growth e p) (hq : Growth e q) :
    Growth e (fun L => p L + q L) := by
  obtain ⟨C,hC⟩ := hp; obtain ⟨D,hD⟩ := hq
  refine ⟨C+D, fun L n => ?_⟩
  simp only [map_add, Nat.cast_add, add_mul]
  exact (abs_add_le ..).trans (add_le_add (hC L n) (hD L n))

private theorem growth_sub {p q : Fam} {e : ℕ} (hp : Growth e p) (hq : Growth e q) :
    Growth e (fun L => p L - q L) := by
  obtain ⟨C,hC⟩ := hp; obtain ⟨D,hD⟩ := hq
  refine ⟨C+D, fun L n => ?_⟩
  simp only [map_sub, Nat.cast_add, add_mul]
  exact (abs_sub ..).trans (add_le_add (hC L n) (hD L n))

private theorem growth_mon {p : Fam} {e : ℕ} (hp : Growth e p) (j : ℕ → ℕ) :
    Growth e (fun L => Xs^(j L)*p L) := by
  obtain ⟨C,hC⟩ := hp; refine ⟨C,fun L n => ?_⟩
  rw [coeff_X_pow_mul']
  split
  · exact (hC L _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.succ_le_succ (Nat.sub_le n (j L))) _)
      (by positivity))
  · rw [abs_zero]; positivity

private theorem tame_action {p q : Fam} {e : ℕ} (ht : Tame p) (hg : Growth e q) :
    Growth e (fun L => p L*q L) := by
  induction ht generalizing q with
  | zero => exact ⟨0,by simp⟩
  | one => simpa using hg
  | mon j => exact growth_mon hg j
  | add _ _ ih jh => simpa only [add_mul] using growth_add (ih hg) (jh hg)
  | sub _ _ ih jh => simpa only [sub_mul] using growth_sub (ih hg) (jh hg)
  | mul _ _ ih jh => simpa only [mul_assoc] using ih (jh hg)

private theorem growth_conv {p q : Fam} {e : ℕ} (hp : Growth e p) (hq : Growth 0 q) :
    Growth (e+1) (fun L => p L*q L) := by
  obtain ⟨C,hC⟩ := hp; obtain ⟨D,hD⟩ := hq
  simp only [pow_zero, mul_one] at hD
  refine ⟨C*D,fun L n => ?_⟩
  rw [coeff_mul]
  calc
    _ ≤ ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, |coeff ij.1 (p L)*coeff ij.2 (q L)| :=
      Finset.abs_sum_le_sum_abs ..
    _ ≤ ∑ _ij ∈ Finset.HasAntidiagonal.antidiagonal n, (((C:ℤ)*((n:ℤ)+1)^e)*D) := by
      apply Finset.sum_le_sum; intro ij hij; rw [abs_mul]
      have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have h : (ij.1 : ℤ) ≤ n := by exact_mod_cast (show ij.1 ≤ n by omega)
      apply mul_le_mul _ (hD L _) (abs_nonneg _) (by positivity)
      exact (hC L _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity))
    _ = _ := by simp [pow_succ]; ring

private theorem tame_num (k : ℕ) : Tame (numerator k) := by
  induction k with
  | zero => exact Tame.one
  | succ k ih => exact (Tame.one.sub (Tame.mon _)).mul ih

private theorem growth_geom (j : ℕ) : Growth 0 (fun _ => geom j) := by
  refine ⟨1,fun L n => ?_⟩
  simp only [geom, coeff_mk, pow_zero, mul_one, Nat.cast_one]
  split <;> decide

private theorem cancel_pair (j : ℕ) (hj : 0 < j) :
    (1-Xs) * geom j * geom (j+1) = geom j - Xs * geom (j+1) := by
  calc
    _ = ((1-Xs^(j+1)) - Xs*(1-Xs^j)) * geom j * geom (j+1) := by rw [pow_succ]; ring
    _ = geom j * ((1-Xs^(j+1))*geom (j+1)) -
        Xs*((1-Xs^j)*geom j)*geom (j+1) := by ring
    _ = _ := by rw [geom_cancel hj, geom_cancel (Nat.succ_pos j)]; ring

private theorem growth_triple (r : ℕ) :
    Growth (r+1) (fun L => (1-Xs)^3 * gaussian (r+3) L) := by
  have H : Growth (r+1) (fun _ => (1-Xs)^3 * invDen (r+5)) := by
    induction r with
    | zero =>
      have u (j : ℕ) : Growth 0 (fun _ => geom j - Xs*geom (j+1)) := by
        simpa only [pow_one] using growth_sub (growth_geom j)
          (growth_mon (growth_geom (j+1)) (fun _ => 1))
      have eq : (1-Xs)^3 * invDen 5 =
          (geom 2-Xs*geom 3)*(geom 4-Xs*geom 5) := by
        calc
          _ = ((1-Xs^1)*geom 1) * (((1-Xs)*geom 2*geom 3) * ((1-Xs)*geom 4*geom 5)) := by
            norm_num [invDen]; ring
          _ = _ := by rw [geom_cancel (by decide), cancel_pair 2 (by decide),
                            cancel_pair 4 (by decide), one_mul]
      simp only [eq]
      exact growth_conv (u 2) (u 4)
    | succ r ih =>
      have eq : (1-Xs)^3 * invDen (r+1+5) =
                ((1-Xs)^3 * invDen (r+5)) * geom (r+6) := by
        change (1-Xs)^3*(geom (r+6)*invDen (r+5)) = _; ring
      simp only [eq]
      exact growth_conv ih (growth_geom _)
  have HH := tame_action (tame_num (r+5)) H
  convert HH using 1
  funext L
  rw [← box_eq, box]; ring

private theorem tame_seg (b : ℕ) : Tame (fun _ => seg b) := by
  induction b with
  | zero => exact Tame.zero
  | succ b ih => exact ih.add (Tame.mon (fun _ => b))

private theorem seg_coeff (a n : ℕ) : coeff n (seg a) = if n < a then 1 else 0 := by
  induction a with
  | zero => simp [seg]
  | succ a ih =>
    rw [seg, map_add, ih, coeff_X_pow]
    split_ifs <;> omega

private theorem growth_seg (j : ℕ → ℕ) : Growth 0 (fun L => seg (j L)) := by
  refine ⟨1,fun L n => ?_⟩; rw [seg_coeff]; split <;> simp

private def denSeg : ℕ → S
  | 0 => 1
  | k+1 => seg (k+1) * denSeg k

private def numSeg : ℕ → ℕ → S
  | 0, _ => 1
  | k+1, L => seg (L+k+1) * numSeg k L

private theorem prod_interval (k L : ℕ) : denSeg k * box k L = numSeg k L := by
  induction k with
  | zero => simp [denSeg, box, numerator, invDen, numSeg]
  | succ k ih =>
    have can : seg (k+1)*(1-Xs^(L+k+1))*geom (k+1) = seg (L+k+1) := by
      calc
        _ = seg (L+k+1)*(((1-Xs)*seg (k+1))*geom (k+1)) := by rw [← Δseg (L+k+1)]; ring
        _ = _ := by rw [Δseg, geom_cancel (Nat.succ_pos k), mul_one]
    change _ = seg (L+k+1) * numSeg k L
    rw [← ih, ← can]
    simp only [denSeg, box, numerator, invDen]; ring

private theorem tame_nat (a : ℕ) : Tame (fun _ => (a:S)) := by
  induction a with
  | zero => simpa using Tame.zero
  | succ a ih => simpa only [Nat.cast_succ] using ih.add Tame.one

private theorem tame_den (k : ℕ) : Tame (fun _ => denSeg k) := by
  induction k with
  | zero => exact Tame.one
  | succ k ih => exact (tame_seg _).mul ih

private theorem seg_residue (a : ℕ) :
    ∃ E : S, Tame (fun _ => E) ∧ (a:S)-seg a = (1-Xs)*E := by
  induction a with
  | zero => exact ⟨0,Tame.zero,by simp [seg]⟩
  | succ a ih =>
    obtain ⟨E,hE,he⟩ := ih
    refine ⟨E+seg a,hE.add (tame_seg _),?_⟩
    rw [mul_add, ← he, Δseg, Nat.cast_succ, seg]; ring

private theorem den_residue (k : ℕ) :
    ∃ E : S, Tame (fun _ => E) ∧ (k.factorial:S)-denSeg k = (1-Xs)*E := by
  induction k with
  | zero => exact ⟨0,Tame.zero,by simp [denSeg]⟩
  | succ k ih =>
    obtain ⟨E,hE,he⟩ := ih
    obtain ⟨F,hF,hf⟩ := seg_residue (k+1)
    refine ⟨(↑(k+1:ℕ):S)*E + F * denSeg k, ((tame_nat _).mul hE).add (hF.mul (tame_den _)),?_⟩
    rw [Nat.factorial_succ, Nat.cast_mul, denSeg]
    calc
      _ = (↑(k+1:ℕ):S)*((k.factorial:S)-denSeg k) +
             ((↑(k+1:ℕ):S)-seg (k+1))*denSeg k := by ring
      _ = _ := by rw [he,hf]; ring


private abbrev interval (L : ℕ) : S := seg (L+1)

private theorem growth_cube (e : ℕ) : Growth e (fun L => (interval L)^(e+1)) := by
  induction e with
  | zero => simpa using growth_seg (fun L => L+1)
  | succ e ih => simpa only [pow_succ (interval _) (e+1)] using
      growth_conv ih (growth_seg (fun L => L+1))

private theorem tame_extra (a : ℕ) :
    Tame (fun L => seg (L+a+1)-interval L) := by
  convert (Tame.mon (fun L => L+1)).mul (tame_seg a) using 1
  funext L
  rw [show L+a+1=L+1+a by omega, seg_add]; ring

private theorem growth_intervals (e : ℕ) :
    Growth e (fun L => (1-Xs)^2 * (numSeg (e+4) L - (interval L)^(e+4))) := by
  have delta (a : ℕ → ℕ) : Tame (fun L => (1-Xs)*seg (a L)) := by
    simpa only [Δseg] using Tame.one.sub (Tame.mon a)
  induction e with
  | zero =>
    have term (a : ℕ) (b c d : ℕ → ℕ) : Growth 0
        (fun L => (1-Xs)^2 * ((seg (L+a+1)-interval L)*seg (b L)*seg (c L)*seg (d L))) := by
      have H := tame_action (((tame_extra a).mul (delta b)).mul (delta c)) (growth_seg d)
      convert H using 1; funext L; ring
    let u := fun L : ℕ => L+1
    have H := growth_add (growth_add (term 3 (fun L => L+2) (fun L => L+3) u)
      (term 2 (fun L => L+2) u u)) (term 1 u u u)
    convert H using 1
    funext L
    norm_num [numSeg, u, interval]
    ring
  | succ e ih =>
    have h₁ := growth_conv ih (growth_seg (fun L => L+(e+4)+1))
    have h₂ := tame_action (((tame_extra (e+4)).mul (delta (fun L => L+1))).mul
        (delta (fun L => L+1))) (growth_cube (e+1))
    convert growth_add h₁ h₂ using 1
    funext L
    change (1-Xs)^2*(seg (L+(e+4)+1)*numSeg (e+4) L - (interval L)^(e+4+1)) = _
    rw [pow_succ (interval L) (e+4)]
    simp only [interval]
    ring

private def err (k L : ℕ) : S := (k.factorial:S)*box k L - (interval L)^k

/-- The error after replacing the scaled Gaussian by the power of an interval
has second differences of order at most k-4, uniformly in the width. -/
private theorem err_growth (r : ℕ) :
    Growth (r+1) (fun L => (1-Xs)^2 * err (r+5) L) := by
  obtain ⟨E,hE,he⟩ := den_residue (r+5)
  have h₁ := tame_action hE (growth_triple r)
  have h₂ := growth_intervals (r+1)
  convert growth_add h₁ h₂ using 1
  funext L
  change (1-Xs)^2 * err (r+5) L = E*((1-Xs)^3 * gaussian (r+3) L) +
    (1-Xs)^2 * (numSeg (r+5) L - (interval L)^(r+5))
  rw [← prod_interval, ← box_eq, err]
  linear_combination (1-Xs)^2 * box (r+5) L * he

private theorem zscale (a : ℕ) (p : S) (n : ℤ) :
    atZ ((a:S)*p) n = (a:ℤ)*atZ p n := by
  induction a with
  | zero => simp [atZ]
  | succ a ih => rw [Nat.cast_succ, Nat.cast_succ, add_mul, one_mul, zadd, ih]; ring

private theorem err_sym (k L : ℕ) : Reflects (err k L) (k*L) := by
  intro n
  simp only [err, zsub, zscale]
  rw [box_reflects k L n, sym_cube k L n]

private theorem reflect_delta {p : S} {d : ℕ} (h : Reflects p d) (n : ℤ) :
    atZ ((1-Xs)*p) ((d:ℤ)+1-n) = -atZ ((1-Xs)*p) n := by
  rw [zΔ,zΔ, h ((d:ℤ)+1-n), h ((d:ℤ)+1-n-1)]
  rw [show (d:ℤ)-(d+1-n)=n-1 by ring, show (d:ℤ)-(d+1-n-1)=n by ring]; ring

/-- Telescope from n to its reflected first-difference index d+1-n. -/
private theorem reflected_bound {p : S} {d n : ℕ} (h : Reflects p d)
    (hn : 2*n ≤ d) (B : ℤ)
    (hb : ∀ t ≤ d+1, |coeff t ((1-Xs)^2*p)| ≤ B) :
    |coeff n ((1-Xs)*p)| ≤ ((d:ℤ)+1-2*n)*B := by
  let f := fun t : ℕ => coeff t ((1-Xs)*p)
  have step (j : ℕ) (hj : n+j ≤ d+1) : |f (n+j)-f n| ≤ (j:ℤ)*B := by
    induction j with
    | zero => simp
    | succ j ih =>
      have h₁ := hb (n+j+1) hj
      rw [pow_two, mul_assoc, coeff_gap_succ] at h₁
      change |f (n+(j+1))-f n| ≤ _
      calc
        _ = |(f (n+j+1)-f (n+j))+(f (n+j)-f n)| := by rw [sub_add_sub_cancel, Nat.add_assoc]
        _ ≤ _ := abs_add_le ..
        _ ≤ B + (j:ℤ)*B := add_le_add h₁ (ih (by omega))
        _ = _ := by push_cast; ring
  have hh := step (d+1-2*n) (by omega)
  have he := reflect_delta h n
  have heq : ((n+(d+1-2*n):ℕ):ℤ) = (d:ℤ)+1-n := by omega
  rw [← heq, atZ_nat, atZ_nat] at he
  change f _ = -f n at he
  rw [he, show -f n - f n = -(f n + f n) by ring, abs_neg] at hh
  have he' : ((d+1-2*n:ℕ):ℤ) = (d:ℤ)+1-2*n := by omega
  rw [he'] at hh
  change |f n| ≤ _
  rw [show f n+f n = 2*f n by ring, abs_mul, abs_of_nonneg (by decide : (0:ℤ)≤2)] at hh
  linarith [abs_nonneg (f n)]


/-! ## Growth of the first differences of a power of an interval -/

private def jump (k L : ℕ) (n : ℤ) := atZ ((1-Xs)*(interval L)^k) n

private theorem neg_index (p : S) {n : ℤ} (hn : n < 0) : atZ p n = 0 := by
  simp [atZ, not_le.mpr hn]

private theorem telescope (p : S) (a b v : ℤ) (hab : a ≤ b+1)
    (hh : ∀ t : ℤ, a ≤ t → t ≤ b → v ≤ atZ ((1-Xs)*p) t) :
    (b+1-a)*v ≤ atZ p b - atZ p (a-1) := by
  have aux (m : ℕ) (hm : a+m ≤ b+1) :
      (m:ℤ)*v ≤ atZ p (a+m-1) - atZ p (a-1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hi := ih (by omega)
      have hg := hh (a+m) (by omega) (by omega)
      rw [zΔ] at hg
      push_cast
      rw [show a+((m:ℤ)+1)-1=a+m by ring]; linarith
  have he : (((b+1-a).toNat:ℕ):ℤ)=b+1-a := by omega
  have hi := aux (b+1-a).toNat (by omega)
  rwa [he,show a+(b+1-a)-1=b by ring] at hi

private theorem jump_step (k L : ℕ) (n : ℤ) :
    jump (k+1) L n =
      atZ ((interval L)^k) (min n ((k:ℤ)*L-n)) -
      atZ ((interval L)^k) (max 0 (n-L)-1) := by
  have e : (1-Xs)*(interval L)^(k+1) =
      (interval L)^k-Xs^(L+1)*(interval L)^k := by
    rw [pow_succ', ← mul_assoc, Δseg, sub_mul, one_mul]
  rw [jump, e, zsub, zshift]
  congr 1
  · by_cases h : n ≤ (k:ℤ)*L-n
    · rw [min_eq_left h]
    · rw [min_eq_right (by omega)]
      simpa only [Nat.cast_mul] using sym_cube k L n
  · by_cases h : 0 ≤ n-L
    · rw [max_eq_right h]; push_cast; congr 1; ring
    · rw [max_eq_left (by omega), neg_index _ (by omega), neg_index _ (by omega)]

private theorem jump_nonneg (k L : ℕ) (hk : 1 ≤ k) (n : ℤ) (hn : 0 ≤ n)
    (hd : 2*n ≤ (k:ℤ)*L) : 0 ≤ jump k L n := by
  induction k, hk using Nat.le_induction generalizing n with
  | base =>
    have hh : n < (L:ℤ)+1 := by norm_num at hd; omega
    rw [jump, pow_one, Δseg, zsub]
    have hx : atZ (Xs^(L+1)) n = 0 := by
      rw [← mul_one (Xs^(L+1)), zshift, neg_index _ (by omega)]
    rw [hx,sub_zero,zone]; split <;> decide
  | succ k hk ih =>
    rw [jump_step]
    push_cast at hd
    have hkL : (L:ℤ) ≤ (k:ℤ)*L := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (show (1:ℤ) ≤ k by exact_mod_cast hk) (Int.natCast_nonneg L)
    have he : ((k:ℤ)+1)*L=(k:ℤ)*L+L := by ring
    rw [he] at hd
    have hb := telescope ((interval L)^k) (max 0 (n-L)) (min n ((k:ℤ)*L-n)) 0
      (by omega) (fun t ha hb => ih t (by omega) (by omega))
    simpa using hb

/-- Any run of consecutive lower bounds in the allowable interval gives that
many contributions. The two ends discarded from the telescope are nonnegative. -/
private theorem transfer (k L : ℕ) (hk : 1 ≤ k) (n a m v : ℤ)
    (hm : 0 < m) (ha : max 0 (n-L) ≤ a)
    (hb : a+m-1 ≤ min n ((k:ℤ)*L-n))
    (h : ∀ t : ℤ, a ≤ t → t < a+m → v ≤ jump k L t) :
    m*v ≤ jump (k+1) L n := by
  rw [jump_step]
  let l := max 0 (n-L)
  let u := min n ((k:ℤ)*L-n)
  have pos (t : ℤ) (hl : l ≤ t) (hu : t ≤ u) : 0 ≤ jump k L t :=
    jump_nonneg k L hk t (by dsimp [l] at hl; omega) (by dsimp [u] at hu; omega)
  have h₁ := telescope ((interval L)^k) l (a-1) 0 (by omega)
    (fun t ht ht' => pos t ht (by dsimp [u]; omega))
  have h₂ := telescope ((interval L)^k) a (a+m-1) v (by omega)
    (fun t ht ht' => h t ht (by omega))
  have h₃ := telescope ((interval L)^k) (a+m) u 0 (by dsimp [u]; omega)
    (fun t ht ht' => pos t (by dsimp [l]; omega) ht')
  change _ ≤ atZ _ u - atZ _ (l-1)
  rw [show a+m-1+1-a=m by ring] at h₂
  linarith

private theorem triangle (L : ℕ) (n : ℤ) (hn : 0 ≤ n) (hl : n ≤ L) :
    jump 2 L n = 1 := by
  have e : (1-Xs)*(interval L)^2 = interval L-Xs^(L+1)*interval L := by
    rw [pow_two, ← mul_assoc, Δseg, sub_mul, one_mul]
  have hn' : n - ((L+1:ℕ):ℤ) < 0 := by omega
  rw [jump,e,zsub,zshift,neg_index _ hn', sub_zero]
  lift n to ℕ using hn
  rw [atZ_nat, seg_coeff, ite_eq_left (by omega)]

/-- Discard short boundary intervals at every level; no continuous limit is needed. -/
private theorem interior (r L : ℕ) (H n : ℤ) (hH : 1 ≤ H)
    (hl : 4^(r+2)*H ≤ (L:ℤ)) (hn : 4^(r+2)*H ≤ n)
    (hs : 4^(r+2)*H ≤ ((r:ℤ)+2)*L-2*n) :
    H^r ≤ jump (r+2) L n := by
  induction r generalizing n with
  | zero =>
    rw [triangle L n (by norm_num at hn; omega) (by norm_num at hs; omega), pow_zero]
  | succ r ih =>
    let T : ℤ := 4^(r+2)*H
    have ht : H ≤ T := le_mul_of_one_le_left (by omega) (one_le_pow₀ (by decide))
    have eq : (4:ℤ)^(r+1+2)*H=4*T := by dsimp [T]; rw [pow_succ (4:ℤ) (r+2)]; ring
    rw [eq] at hl hn hs
    push_cast at hs
    let a := max (n-L) T
    have hrL : 2*(L:ℤ) ≤ ((r:ℤ)+2)*L := by nlinarith [mul_nonneg (Int.natCast_nonneg r) (Int.natCast_nonneg L)]
    have he : ((r:ℤ)+1+2)*L=((r:ℤ)+2)*L+L := by ring
    rw [he] at hs
    have hi := transfer (r+2) L (by omega) n a H (H^r) (by omega)
      (by dsimp [a]; omega)
      (by dsimp [a]; omega)
      (by intro t h₁ h₂
          apply ih t (by omega) (by dsimp [a] at h₁; omega)
          dsimp [a] at h₂; omega)
    simpa only [pow_succ', Nat.succ_add] using hi

/-- A uniform bound with the correct multiplicity right up to the central
coefficient. H is a mesh size comparable to L. -/
private theorem cube_lower (r L : ℕ) (H n : ℤ) (hH : 1 ≤ H)
    (hl : 2*4^(r+5)*H ≤ (L:ℤ)) (hu : (L:ℤ) ≤ 4*4^(r+5)*H)
    (hn : (L:ℤ) ≤ n) (hs : 2*n ≤ ((r:ℤ)+5)*L) :
    (((r:ℤ)+5)*(4*4^(r+5))+1) * jump (r+5) L n ≥
      (((r:ℤ)+5)*L-2*n+1)*H^(r+2) := by
  let t : ℤ := 4^(r+4)*H
  have et : (4:ℤ)^(r+5)*H=4*t := by dsimp [t]; rw [pow_succ (4:ℤ) (r+4)]; ring
  have ht : 0 < t := by dsimp [t]; positivity
  have h8 : 8*t ≤ (L:ℤ) := by linarith only [hl,et]
  let w := ((r:ℤ)+5)*L-2*n+1
  have hw : 0 < w := by dsimp [w]; omega
  let c := ((r:ℤ)+5)*(4*4^(r+5))+1
  have hc : 1 ≤ c := by
    have hc₀ : 0 ≤ ((r:ℤ)+5)*(4*4^(r+5)) := by positivity
    dsimp only [c]; omega
  change w*H^(r+2) ≤ c*jump (r+5) L n
  by_cases hfar : 4*t ≤ ((r:ℤ)+5)*L-2*n
  · have h := interior (r+3) L H n hH (by rw [et]; omega) (by rw [et]; omega)
        (by change 4^(r+5)*H ≤ (((r+3:ℕ):ℤ)+2)*L-2*n
            rw [et]; push_cast; linarith only [hfar])
    have hw' : w ≤ c*H := by
      have hh := mul_le_mul_of_nonneg_left hu (show 0 ≤ (r:ℤ)+5 by positivity)
      dsimp [w,c]; nlinarith
    calc
      w*H^(r+2) ≤ (c*H)*H^(r+2) := mul_le_mul_of_nonneg_right hw' (by positivity)
      _ = c*H^(r+3) := by rw [pow_succ (H) (r+2)]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h (by omega)
  · have he : ((r:ℤ)+5)*L=((r:ℤ)+4)*L+L := by ring
    have h4 : 4*(L:ℤ) ≤ ((r:ℤ)+4)*L := by nlinarith [mul_nonneg (Int.natCast_nonneg r) (Int.natCast_nonneg L)]
    have h := transfer (r+4) L (by omega) n (n-L) w (H^(r+2)) hw
      (by omega)
      (by dsimp [w]; omega)
      (by intro j hj hje
          apply interior (r+2) L H j hH (by change t ≤ _; omega)
          · change t ≤ j; omega
          · change t ≤ ((r:ℤ)+2+2)*L-2*j
            rw [show (r:ℤ)+2+2=r+4 by ring]
            dsimp [w] at hje; omega)
    exact h.trans (le_mul_of_one_le_left
      (jump_nonneg (r+5) L (by omega) n (by omega) (by simpa using hs)) hc)


private theorem major_pow {n K H e : ℕ} (h : n+1 ≤ K*H) :
    ((n:ℤ)+1)^e ≤ (K:ℤ)^e*(H:ℤ)^e := by
  rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); exact_mod_cast h

private theorem bulk (r : ℕ) :
    ∃ M : ℕ, ∀ L ≥ M, ∀ (A s n : ℕ), L ≤ n → 2*n ≤ (r+5)*L →
      0 ≤ coeff n ((1-Xs)*centred r L A s) := by
  obtain ⟨C,hC⟩ := err_growth r
  let k := r+5
  let P := 2*4^k
  let K := k*(2*P)+2
  let c := k*(2*P)+1
  let E := C*K^(r+1)
  let V := k.factorial
  let B := 2^(r+3)*K^(r+1)
  let R := c*(E+V*B)+1
  refine ⟨P*R,fun L hL A s n hn hd => ?_⟩
  let H := L/P
  have hp : 0 < P := by dsimp [P]; positivity
  have hr : R ≤ H := (Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using hL)
  have hH : 1 ≤ H := (by dsimp [R]; omega : 1 ≤ R) |>.trans hr
  have hlo : P*H ≤ L := Nat.mul_div_le L P
  have hup : L ≤ (2*P)*H := by
    have hh : L < (H+1)*P := by
      by_contra! h
      exact (by omega : ¬ H+1 ≤ H) ((Nat.le_div_iff_mul_le hp).mpr h)
    have h₁ := Nat.mul_le_mul_left P hH
    nlinarith
  have hd' : k*L+2 ≤ K*H := by
    have h₁ := Nat.mul_le_mul_left k hup
    dsimp [K]; nlinarith
  let w : ℤ := (k*L:ℕ)+1-2*(n:ℤ)
  have hdZ : (2:ℤ)*n ≤ ((k*L:ℕ):ℤ) := by exact_mod_cast hd
  have hw : 1 ≤ w := by dsimp only [w]; linarith only [hdZ]
  have err_abs : |coeff n ((1-Xs)*err k L)| ≤ w*((E:ℤ)*(H:ℤ)^(r+1)) := by
    apply reflected_bound (err_sym k L) hd _
    intro t ht
    have ht' : t+1 ≤ K*H := by omega
    calc
      _ ≤ _ := hC L t
      _ ≤ (C:ℤ)*((K:ℤ)^(r+1)*(H:ℤ)^(r+1)) :=
        mul_le_mul_of_nonneg_left (major_pow ht') (by positivity)
      _ = _ := by dsimp [E]; ring
  let small := coeff n (Xs^s * ((1-Xs)*gaussian (r+1) A))
  have sb : small ≤ (B:ℤ)*(H:ℤ)^(r+1) := by
    dsimp [small]
    rw [coeff_X_pow_mul']
    split
    · have ht' : (n-s)+1 ≤ K*H := by dsimp [k] at hd'; omega
      calc
        _ ≤ _ := le_abs_self _
        _ ≤ _ := gap_bound (r+1) A (n-s)
        _ ≤ (2:ℤ)^(r+3)*((K:ℤ)^(r+1)*(H:ℤ)^(r+1)) :=
          mul_le_mul_of_nonneg_left (major_pow ht') (by positivity)
        _ = _ := by dsimp [B]; ring
    · positivity
  have low := cube_lower r L (H:ℤ) (n:ℤ) (by exact_mod_cast hH)
      (by exact_mod_cast hlo) (by convert (show (L:ℤ) ≤ (2*(P:ℤ))*(H:ℤ) by exact_mod_cast hup) using 1
                                  dsimp [P,k]; ring)
      (by exact_mod_cast hn) (by exact_mod_cast hd)
  have low' : w*(H:ℤ)^(r+2) ≤ (c:ℤ)*jump k L n := by
    dsimp only [w,k,c,P] at *
    push_cast
    convert low using 1 <;> ring
  have hready : (c:ℤ)*((E:ℤ)+(V:ℤ)*B) ≤ H := by
    exact_mod_cast (show c*(E+V*B) ≤ H by dsimp [R] at hr; omega)
  have hc : 0 < (c:ℤ) := by dsimp [c]; positivity
  have hu : w*((E:ℤ)+(V:ℤ)*B)*(H:ℤ)^(r+1) ≤ jump k L n := by
    apply le_of_mul_le_mul_left _ hc
    calc
      _ = w*((c:ℤ)*((E:ℤ)+(V:ℤ)*B))*(H:ℤ)^(r+1) := by ring
      _ ≤ w*H*(H:ℤ)^(r+1) := by gcongr
      _ = _ := by rw [pow_succ (H:ℤ) (r+1)]; ring
      _ ≤ _ := low'
  let big := coeff n ((1-Xs)*box k L)
  have hid : coeff n ((1-Xs)*err k L) = (V:ℤ)*big - jump k L n := by
    unfold err; rw [mul_sub, mul_left_comm, map_sub]
    simpa only [atZ_nat, jump, V, big] using congrArg
      (fun a : ℤ => a-jump k L n) (zscale V ((1-Xs)*box k L) n)
  rw [hid] at err_abs
  have he := (abs_le.mp err_abs).1
  have hwB : (V:ℤ)*B*(H:ℤ)^(r+1) ≤ w*((V:ℤ)*B*(H:ℤ)^(r+1)) :=
    le_mul_of_one_le_left (by positivity) hw
  have hvs := mul_le_mul_of_nonneg_left sb (show 0 ≤ (V:ℤ) by positivity)
  have hbig : small ≤ big := by
    apply le_of_mul_le_mul_left _ (show 0 < (V:ℤ) by exact_mod_cast Nat.factorial_pos k)
    linarith only [hu, he, hvs, hwB]
  rw [centred, mul_sub,mul_left_comm (1-Xs) (Xs^s),map_sub, ← box_eq]
  exact sub_nonneg.mpr hbig

/-- Unimodality in the ordinary peak sense, with coefficients zero beyond the support. -/
def Unimodal (p : S) : Prop := ∃ t : ℕ,
    (∀ i < t, coeff i p ≤ coeff (i+1) p) ∧ (∀ i ≥ t, coeff (i+1) p ≤ coeff i p)

def Nonnegative (p : S) : Prop := ∀ n, 0 ≤ coeff n p

private theorem from_left {p : S} {d : ℕ} (h : Reflects p d)
    (hl : ∀ n : ℕ, 2*n ≤ d → 0 ≤ coeff n ((1-Xs)*p)) :
    Nonnegative p ∧ Unimodal p := by
  have left (n : ℤ) (hn : 2*n ≤ d) : 0 ≤ atZ ((1-Xs)*p) n := by
    by_cases ha : 0 ≤ n
    · lift n to ℕ using ha; rw [atZ_nat]; apply hl; omega
    · rw [neg_index _ (by omega)]
  have pos (n : ℤ) (hn : 2*n ≤ d) : 0 ≤ atZ p n := by
    by_cases ha : 0 ≤ n
    · have hh := telescope p 0 n 0 (by omega) (fun t _ ht => left t (by omega))
      simpa only [zero_sub, neg_index p (by decide : (-1:ℤ)<0), mul_zero, sub_zero] using hh
    · rw [neg_index _ (by omega)]
  constructor
  · intro n; rw [← atZ_nat]
    by_cases hh : 2*(n:ℤ) ≤ d
    · exact pos _ hh
    · rw [h]; apply pos; omega
  · refine ⟨d/2,fun i hi => ?_,fun i hi => ?_⟩
    · have hh := left ((i+1:ℕ):ℤ) (by omega)
      rw [zΔ, atZ_nat, show ((i+1:ℕ):ℤ)-1=i by omega, atZ_nat] at hh
      omega
    · have hgap : atZ ((1-Xs)*p) ((i+1:ℕ):ℤ) ≤ 0 := by
        have hh := reflect_delta h (i+1:ℕ)
        by_cases hl' : 2*((d:ℤ)+1-((i+1:ℕ):ℤ)) ≤ d
        · have hleft := left _ hl'
          omega
        · rw [show (d:ℤ)+1-((i+1:ℕ):ℤ)=((i+1:ℕ):ℤ) by omega] at hh
          omega
      rw [atZ_nat, coeff_gap_succ] at hgap
      omega

private theorem parts_tiny (r n : ℕ) (hn : n ≤ 2) :
    coeff n (parts r) = if 2 ∣ n then 1 else 0 := by
  induction r with
  | zero => simp [parts,geom]
  | succ r ih =>
    have e : (1-Xs^(r+3))*parts (r+1) = parts r := by
      rw [parts,mul_left_comm,geom_cancel (by omega),mul_one]
    have h := congrArg (coeff n) e
    rwa [sub_mul,one_mul,map_sub,coeff_X_pow_mul',ite_eq_right (by omega),sub_zero,ih] at h

theorem shift_one_not_unimodal (r L A : ℕ) (hc : (r+3)*A+2 = (r+5)*L)
    (hl : 2 ≤ L) : ¬ Unimodal (centred r L A 1) := by
  have hA : 1 ≤ A := by
    by_contra! h; have hh : A=0 := by omega
    rw [hh] at hc; nlinarith
  let p := centred r L A 1
  have h (n : ℕ) (hh : n ≤ 2) (hh' : 1 ≤ n) :
      coeff n ((1-Xs)*p) = (if 2 ∣ n then 1 else 0) - (if 2 ∣ n-1 then 1 else 0) := by
    dsimp [p,centred]; rw [mul_sub,mul_left_comm (1-Xs) (Xs^1),gaussian_gap,gaussian_gap,map_sub,
      numerator_edge _ _ _ (by omega),coeff_X_pow_mul',ite_eq_left hh',numerator_edge _ _ _ (by omega),
      parts_tiny _ _ hh,parts_tiny _ _ (by omega)]
  have first := h 1 (by decide) (by decide)
  have second := h 2 (by decide) (by decide)
  norm_num at first second
  rw [coeff_gap_succ p 0] at first
  rw [coeff_gap_succ p 1] at second
  rintro ⟨t,h₁,h₂⟩
  by_cases ht : t=0
  · have hh := h₂ 1 (by omega); dsimp only [p] at *; omega
  · have hh := h₁ 0 (by omega); dsimp only [p] at *; omega

/-- Rectangle form: the threshold depends only on the height r+5. -/
theorem eventual_centred (r : ℕ) :
    ∃ M : ℕ, ∀ L ≥ M, ∀ A s, (r+3)*A+2*s=(r+5)*L →
      (Nonnegative (centred r L A s) ∧ Unimodal (centred r L A s) ↔ s ≠ 1) := by
  obtain ⟨M,hM⟩ := bulk r
  refine ⟨max M 2,fun L hl A s hc => ⟨?_,?_⟩⟩
  · intro h hs; subst s
    exact shift_one_not_unimodal r L A (by simpa using hc) (by omega) h.2
  · intro hs
    apply from_left (centred_reflects r L A s hc)
    intro n hn
    by_cases he : n ≤ L
    · exact edge r L A s n hc he hs
    · exact hM L (by omega) A s n (by omega) hn


/-- The source polynomial, written with integral rectangle widths. The division
in the shift is exact under the admissibility hypotheses of stanley_zanello_iv. -/
def sourcePolynomial (k m b : ℕ) : S :=
  let L := m-k
  let h := k-2
  let A := b-h
  gaussian (k-2) L - X^((k*L-h*A)/2) * gaussian (k-4) A

/-- Stanley--Zanello 1.1(iv). Cross multiplication states the upper bound and
exception without rounding; the parity condition uses signed subtraction. -/
theorem stanley_zanello_iv (k : ℕ) (hk : 5 ≤ k) :
    ∃ M : ℕ, ∀ m ≥ M, ∀ b : ℕ, k ≤ m → k-2 ≤ b →
      ((k:ℤ)-2)*b ≤ (k:ℤ)*m-4*k+4 → Even ((k:ℤ)*((m:ℤ)-b)) →
      (Nonnegative (sourcePolynomial k m b) ∧ Unimodal (sourcePolynomial k m b) ↔
        ((k:ℤ)-2)*b ≠ (k:ℤ)*m-4*k+2) := by
  obtain ⟨r,rfl⟩ : ∃ r, k = r+5 := ⟨k-5,by omega⟩
  obtain ⟨M,hM⟩ := eventual_centred r
  refine ⟨M+(r+5),fun m hm b hkm hb hu ⟨x,hx⟩ => ?_⟩
  let L := m-(r+5)
  let A := b-(r+3)
  let s := ((r+5)*L-(r+3)*A)/2
  have hL : (L:ℤ) = (m:ℤ)-(r+5:ℕ) := by dsimp [L]; omega
  have hA : (A:ℤ) = (b:ℤ)-(r+3:ℕ) := by dsimp [A]; omega
  have e : (((r+5)*L:ℕ):ℤ)-(((r+3)*A:ℕ):ℤ) =
      ((r:ℤ)+5)*m-4*((r:ℤ)+5)+4-((r:ℤ)+5-2)*b := by
    push_cast; rw [hL,hA]; push_cast; ring
  push_cast at hu hx ⊢
  have he : (((r+5)*L:ℕ):ℤ)-(((r+3)*A:ℕ):ℤ) =
      2*(x+(b:ℤ)-2*((r:ℤ)+5)+2) := by linarith only [e,hx]
  have hc : (r+3)*A+2*s=(r+5)*L := by dsimp [s]; omega
  have hpoly : sourcePolynomial (r+5) m b = centred r L A s := by
    simp only [sourcePolynomial,centred,L,A,s,show r+5-2=r+3 by omega,
      show r+5-4=r+1 by omega]
  rw [hpoly,hM L (by dsimp [L]; omega) A s hc]
  have hcast : (((r+5)*L:ℕ):ℤ)-(((r+3)*A:ℕ):ℤ) = 2*s := by omega
  constructor <;> intro h hbad <;> apply h <;> omega

end
end ReinerStanton
