import Mathlib

namespace ManickamMiklosSinghi.SevenK

/-- Pointwise sign minorant. The upper bound on the nonnegative half-line follows
by factoring the error as a square times a quadratic with positive coefficients. -/
theorem quartic_minorant (z u s : ℝ) (hz : 0 < z) (hu : 0 ≤ u) :
    let d := 2*z*(2*z+u)/(3*z+u)
    let c := (3*z+u)/(z^2*(z+u)^3)
    c*s*(s+u)^2*(d-s) ≤ (if 0 ≤ s then (1:ℝ) else 0) := by
  dsimp only
  have hz' : 0 < 3*z+u := by positivity
  have ht : 0 < z+u := by positivity
  have hc : 0 < z^2*(z+u)^3 := by positivity
  by_cases hs : 0 ≤ s
  · rw [ite_eq_left hs]
    have he : 1 - (3*z+u)/(z^2*(z+u)^3)*s*(s+u)^2*
          (2*z*(2*z+u)/(3*z+u)-s) =
        (s-z)^2 * ((3*z+u)*s^2 + (2*u^2 + 6*u*z + 2*z^2)*s + (z+u)^3) /
          (z^2*(z+u)^3) := by
      field_simp [ne_of_gt hz', ne_of_gt ht, ne_of_gt hz]; ring
    apply sub_nonneg.mp
    rw [he]
    positivity
  · rw [ite_eq_right hs]
    have hsn : s ≤ 0 := le_of_lt (lt_of_not_ge hs)
    have hd : 0 ≤ 2*z*(2*z+u)/(3*z+u) := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
        (by positivity) hsn) (sq_nonneg _)) (by linarith)

end ManickamMiklosSinghi.SevenK
