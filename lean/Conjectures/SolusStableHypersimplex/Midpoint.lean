import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Zify

/-!
# Rounded midpoint inequality in finite integer boxes

The integer-weighted, half-way case of the discrete four-functions inequality of
Halikias, Klartag and Slomka (arXiv:1911.04392). The one-dimensional proof
compares sums on each antidiagonal. Inside an interval it either discards one
endpoint or compares both endpoints at once, then recurses on the interior.
Summing out one coordinate at a time gives the box version.
-/

namespace SolusStableHypersimplex.Midpoint

open Finset

/-- Floor of the midpoint of two bounded integers. -/
def lo {M : ℕ} (a b : Fin (M+1)) : Fin (M+1) :=
  ⟨(a.val+b.val)/2, by have := a.isLt; have := b.isLt; omega⟩

/-- Ceiling of the midpoint of two bounded integers. -/
def hi {M : ℕ} (a b : Fin (M+1)) : Fin (M+1) :=
  ⟨(a.val+b.val+1)/2, by have := a.isLt; have := b.isLt; omega⟩

private def block (f : ℕ → ℕ) (a : ℕ) (m : ℕ) := ∑ i ∈ range m, f (a+i)

private theorem back (f : ℕ → ℕ) (a m : ℕ) :
    block f a (m+1) = block f a m + f (a+m) := by
  simp [block, sum_range_succ]

private theorem front (f : ℕ → ℕ) (a m : ℕ) :
    block f a (m+1) = f a + block f (a+1) m := by
  simp [block, sum_range_succ', Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem pair_sum {a b c d : ℕ} (p : a*b ≤ c*d) (h₁ : c<a) (h₂ : c<b) :
    a+b ≤ c+d := by
  zify at *
  by_contra! h
  have hc : (0:ℤ) ≤ (c:ℤ) := by omega
  have hs : (0:ℤ) ≤ (a:ℤ)+b-c-d := by omega
  nlinarith only [p, mul_pos (sub_pos.mpr h₁) (sub_pos.mpr h₂), mul_nonneg hc hs]

/-- The lower and upper output indices of the two crossed endpoint pairs
are exactly the endpoints of the centered comparison interval. -/
private theorem segment (z : ℕ) (F H : ℕ → ℕ)
    (single : ∀ i ≤ z, F i ≤ H (z/2))
    (cross : ∀ i d, i+d ≤ z →
      F i * F (i+d) ≤ H ((z-d)/2) * H ((z+d)/2)) :
    ∀ m i, i+m ≤ z+1 → block F i m ≤ block H ((z-(m-1))/2) m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro i bound
    rcases m with _|m
    · simp [block]
    rcases m with _|d
    · simpa [block] using single i (by omega)
    let e := (z-(d+1))/2
    have er : (z+(d+1))/2 = e+(d+1) := by dsimp [e]; omega
    have en : (z-d)/2 = e ∨ (z-d)/2 = e+1 := by dsimp [e]; omega
    change block F i (d+2) ≤ block H e (d+2)
    have trim (v : ℕ) (vl : v ≤ H e) (vr : v ≤ H (e+(d+1))) :
        block H ((z-d)/2) (d+1) + v ≤ block H e (d+2) := by
      rcases en with he|he
      · rw [he, back H e (d+1)]; omega
      · rw [he, front H e (d+1)]; omega
    by_cases left : F i ≤ min (H e) (H (e+(d+1)))
    · have h := ih (d+1) (by omega) (i+1) (by omega)
      simp only [Nat.add_sub_cancel] at h
      have t := trim (F i) (left.trans (min_le_left ..)) (left.trans (min_le_right ..))
      rw [front F i (d+1)]; omega
    by_cases right : F (i+(d+1)) ≤ min (H e) (H (e+(d+1)))
    · have h := ih (d+1) (by omega) i (by omega)
      simp only [Nat.add_sub_cancel] at h
      have t := trim _ (right.trans (min_le_left ..)) (right.trans (min_le_right ..))
      rw [back F i (d+1)]; omega
    have p := cross i (d+1) (by omega)
    rw [er] at p
    have ends : F i + F (i+(d+1)) ≤ H e + H (e+(d+1)) := by
      by_cases c : H e ≤ H (e+(d+1))
      · rw [min_eq_left c] at left right
        exact pair_sum p (by omega) (by omega)
      · rw [min_eq_right (by omega)] at left right
        rw [Nat.mul_comm (H e)] at p
        rw [Nat.add_comm (H e)]
        exact pair_sum p (by omega) (by omega)
    have inside : block F (i+1) d ≤ block H (e+1) d := by
      cases d with
      | zero => simp [block]
      | succ t =>
        have h := ih (t+1) (by omega) (i+1) (by omega)
        have he : (z-(t+1-1))/2 = e+1 := by dsimp [e]; omega
        rwa [he] at h
    rw [back F i (d+1), front F i d, back H e (d+1), front H e d]
    omega

private def pad {M : ℕ} (f : Fin (M+1) → ℕ) (i : ℕ) :=
  if hi : i<M+1 then f ⟨i,hi⟩ else 0

private theorem pad_hyp {M : ℕ} {f g h k : Fin (M+1) → ℕ}
    (hyp : ∀ i j, f i*g j ≤ h (lo i j)*k (hi i j)) (i j : ℕ) :
    pad f i * pad g j ≤ pad h ((i+j)/2) * pad k ((i+j+1)/2) := by
  by_cases a : i<M+1 <;> by_cases b : j<M+1
  · simpa [pad, a, b, show (i+j)/2<M+1 by omega, show (i+j+1)/2<M+1 by omega,
      lo, hi] using hyp ⟨i,a⟩ ⟨j,b⟩
  all_goals simp [pad, a, b]

private theorem diagonal {M : ℕ} {f g h k : Fin (M+1) → ℕ}
    (hyp : ∀ i j, f i*g j ≤ h (lo i j)*k (hi i j))
    (z a m : ℕ) (ha : a+m ≤ z+1) :
    block (fun i => pad f i*pad g (z-i)) a m ≤
      block (fun i => pad h i*pad k (z-i)) ((z-(m-1))/2) m := by
  apply segment z _ _ _ _ m a ha
  · intro i bound
    convert pad_hyp hyp i (z-i) using 1 <;>
      congr 2 <;> omega
  · intro i d bound
    have A := pad_hyp hyp i (z-(i+d))
    have B := pad_hyp hyp (i+d) (z-i)
    have C := Nat.mul_le_mul A B
    have e₁ : (i+(z-(i+d)))/2 = (z-d)/2 := by omega
    have e₂ : (i+d+(z-i))/2 = (z+d)/2 := by omega
    have e₃ : (i+(z-(i+d))+1)/2 = z-(z+d)/2 := by omega
    have e₄ : (i+d+(z-i)+1)/2 = z-(z-d)/2 := by omega
    rw [e₁,e₂,e₃,e₄] at C
    simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using C

private def totalIdx {M : ℕ} (p : Fin (M+1) × Fin (M+1)) : Fin (2*M+1) :=
  ⟨p.1.val+p.2.val, by have := p.1.isLt; have := p.2.isLt; omega⟩

private def mass {M : ℕ} (f g : Fin (M+1) → ℕ) (z : Fin (2*M+1)) :=
  ∑ p ∈ (univ.filter fun p => totalIdx p = z), f p.1*g p.2

private theorem mass_eq {M : ℕ} (f g : Fin (M+1) → ℕ) (z : Fin (2*M+1)) :
    mass f g z = block (fun i => pad f i * pad g (z.val-i)) (z.val-M)
        (min z.val M - (z.val-M) + 1) := by
  unfold mass block
  have hz := z.isLt
  apply sum_bij (fun (p : Fin (M+1) × Fin (M+1)) _ => p.1.val-(z.val-M))
  · intro p hp
    have eq := congrArg Fin.val (mem_filter.mp hp).2
    change p.1.val+p.2.val=z.val at eq
    have := p.1.isLt; have := p.2.isLt
    simp only [mem_range]; omega
  · intro p hp q hq h
    have ep := congrArg Fin.val (mem_filter.mp hp).2
    have eq := congrArg Fin.val (mem_filter.mp hq).2
    change p.1.val+p.2.val=z.val at ep
    change q.1.val+q.2.val=z.val at eq
    have := p.2.isLt; have := q.2.isLt
    exact Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega))
  · intro t ht
    simp only [mem_range] at ht
    let i := z.val-M+t
    have bi : i<M+1 := by dsimp [i]; omega
    have bj : z.val-i<M+1 := by dsimp [i]; omega
    refine ⟨(⟨i,bi⟩,⟨z.val-i,bj⟩), ?_, ?_⟩
    · apply mem_filter.mpr; refine ⟨mem_univ _, Fin.ext ?_⟩
      change i+(z.val-i)=z.val; dsimp [i]; omega
    · change i-(z.val-M)=t; dsimp [i]; omega
  · intro p hp
    have ep := congrArg Fin.val (mem_filter.mp hp).2
    change p.1.val+p.2.val=z.val at ep
    have := p.2.isLt
    have e : z.val-M + (p.1.val-(z.val-M))=p.1.val := by omega
    simp [e, show z.val-p.1.val=p.2.val by omega, pad]

private theorem sum_mass {M : ℕ} (f g : Fin (M+1) → ℕ) :
    (∑ z, mass f g z) = (∑ i, f i)*(∑ i, g i) := by
  unfold mass
  simp_rw [sum_filter]
  rw [sum_comm]
  simp [Fintype.sum_prod_type, sum_mul, mul_sum]

/-- One-dimensional rounded-midpoint four-functions inequality. -/
theorem line_four_functions {M : ℕ} (f g h k : Fin (M+1) → ℕ)
    (hyp : ∀ i j, f i*g j ≤ h (lo i j)*k (hi i j)) :
    (∑ i, f i)*(∑ i, g i) ≤ (∑ i, h i)*(∑ i, k i) := by
  rw [← sum_mass, ← sum_mass]
  apply sum_le_sum
  intro z _
  rw [mass_eq, mass_eq]
  have := z.isLt
  let a := z.val-M
  let m := min z.val M - a + 1
  have b : a+m ≤ z.val+1 := by dsimp [m,a]; omega
  have e : (z.val-(m-1))/2 = a := by dsimp [m,a]; omega
  exact e ▸ diagonal hyp z.val a m b

private theorem split_sum {n M : ℕ} (f : (Fin (n+1) → Fin (M+1)) → ℕ) :
    (∑ p, f p) = ∑ i, ∑ q : Fin n → Fin (M+1), f (Fin.cons i q) := by
  classical
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => Fin (M+1))).sum_comp f]
  exact Fintype.sum_prod_type _

/-- Discrete Brunn–Minkowski, four-functions form for natural weights on
an arbitrary finite integer box. Taking indicator functions gives the
cardinality inequality for simultaneous lower and upper midpoint closure. -/
theorem box_four_functions {n M : ℕ} (f g h k : (Fin n → Fin (M+1)) → ℕ)
    (hyp : ∀ x y, f x*g y ≤ h (fun i => lo (x i) (y i))*k (fun i => hi (x i) (y i))) :
    (∑ x, f x)*(∑ x, g x) ≤ (∑ x, h x)*(∑ x, k x) := by
  classical
  induction n with
  | zero =>
    simpa [Fintype.sum_unique] using hyp default default
  | succ n ih =>
    rw [split_sum f, split_sum g, split_sum h, split_sum k]
    apply line_four_functions
    intro i j
    apply ih
    intro a b
    have hL : (fun t => lo ((Fin.cons i a) t) ((Fin.cons j b) t)) =
        Fin.cons (lo i j) (fun t => lo (a t) (b t)) := by
      funext t; refine Fin.cases ?_ (fun s => ?_) t <;> simp
    have hU : (fun t => hi ((Fin.cons i a) t) ((Fin.cons j b) t)) =
        Fin.cons (hi i j) (fun t => hi (a t) (b t)) := by
      funext t; refine Fin.cases ?_ (fun s => ?_) t <;> simp
    simpa only [hL,hU] using hyp (Fin.cons i a) (Fin.cons j b)

end SolusStableHypersimplex.Midpoint
