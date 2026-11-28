import Mathlib.Tactic.NormNum

/-! # The four-column obstruction in the FC equality classification

This file verifies the counting core, not the classification of Coxeter heaps.
After the first median turn the first two steps cannot both be increments.
In a connected strip the third layer then has states 0,1,2. The fourth layer
has positive continuation counts at 1 and 2, and may be truncated at 0 or 3.
The counts below sum actual four-step paths, with arbitrary continuation
weights. In particular the mass of the balanced fourth cut is not a hypothesis.
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
