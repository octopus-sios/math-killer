import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ManickamMiklosSinghi.SevenK

variable {ι : Type*}

/-- Elementary positive-moment interpolation, with arbitrary nonnegative finite weights.
The proof sums the tangency certificate y(y+2a)(y-a)^2. -/
theorem interp_124 (s : Finset ι) (w y : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hy : ∀ i ∈ s, 0 ≤ y i) :
    (∑ i ∈ s, w i * (y i)^2)^3 ≤
    (∑ i ∈ s, w i * y i)^2 * (∑ i ∈ s, w i * (y i)^4) := by
  classical
  let M := ∑ i ∈ s, w i * y i
  let V := ∑ i ∈ s, w i * (y i)^2
  let F := ∑ i ∈ s, w i * (y i)^4
  change V^3 ≤ M^2 * F
  have hm : 0 ≤ M := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (hy i hi))
  have hv : 0 ≤ V := Finset.sum_nonneg (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  rcases hm.eq_or_lt with hm | hm
  · have hzero : ∀ i ∈ s, w i * y i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun i hi => mul_nonneg (hw i hi) (hy i hi))).mp hm.symm
    have hv0 : V = 0 := Finset.sum_eq_zero (fun i hi => by
      change w i * y i ^ 2 = 0
      rw [pow_two, ← mul_assoc, hzero i hi, zero_mul])
    rw [hv0, ← hm]
    norm_num
  let a := V / M
  have ha : 0 ≤ a := div_nonneg hv hm.le
  have hsum : 0 ≤ ∑ i ∈ s,
        (w i * (y i)^4 + (2*a^3) * (w i * y i) - (3*a^2) * (w i * (y i)^2)) := by
    apply Finset.sum_nonneg
    intro i hi
    have hp := mul_nonneg (mul_nonneg (mul_nonneg (hw i hi) (hy i hi))
      (add_nonneg (hy i hi) (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) ha))) (sq_nonneg (y i-a))
    nlinarith only [hp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  change 0 ≤ F + (2*a^3)*M - (3*a^2)*V at hsum
  dsimp only [a] at hsum
  field_simp [ne_of_gt hm] at hsum
  nlinarith only [hsum]

end ManickamMiklosSinghi.SevenK
