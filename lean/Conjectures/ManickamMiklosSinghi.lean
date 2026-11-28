import Conjectures.ManickamMiklosSinghi.Foundation
import Conjectures.ManickamMiklosSinghi.BernoulliOneSeventh
import Conjectures.ManickamMiklosSinghi.SevenKFinal

/-!
# Manickam–Miklós–Singhi Conjecture (Flagship Formalization)

Umbrella module exporting:
- `ManickamMiklosSinghi.Foundation`: core MMS definitions (`MMSHolds`), Chowdhury's
  inductive step `mms_add_k`, divisible case `mms_of_dvd`, exact `k = 8` counterexample
  `not_mms_25_8` / `threshold_eight_ge` (`f(8) ≥ 26`), and rational Farkas / branch-and-cut
  soundness (`Certificate.mms_of_tree`).
- `ManickamMiklosSinghi.BernoulliOneSeventh`: unconditional analytic proofs of the
  Milojević–Sudakov Conjecture 1 exceedance inequality `p ≤ exceedance w p` for all
  `p ∈ [0, 1/7]` and all unit fractions `p = 1/q` (`q ≥ 3`, including the sharp endpoint `p = 1/3`).
- `ManickamMiklosSinghi.SevenKFinal`: unconditional universal linear theorem
  `ManickamMiklosSinghi.mms_seven_k : ∀ n k, 0 < k → 7 * k ≤ n → MMSHolds n k`,
  along with the intermediate density bounds `centered_five_k`, `centered_six_k`,
  and `centered_seven_k`.
-/
