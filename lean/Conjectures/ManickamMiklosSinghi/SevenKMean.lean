import Mathlib

namespace ManickamMiklosSinghi.SevenK
open Finset

variable {ι : Type*}

/-- Uniform mean; the denominator is used only on nonempty supports. -/
noncomputable def av (s : Finset ι) (f : ι → ℝ) := (∑ i ∈ s, f i) / s.card

theorem av_congr {s : Finset ι} {f g : ι → ℝ} (h : ∀ i ∈ s, f i = g i) :
    av s f = av s g := by rw [av,av,sum_congr rfl h]

theorem av_mono {s : Finset ι} {f g : ι → ℝ} (h : ∀ i ∈ s, f i ≤ g i) :
    av s f ≤ av s g := div_le_div_of_nonneg_right (sum_le_sum h) (Nat.cast_nonneg _)

theorem av_const {s : Finset ι} (h : s.Nonempty) (c : ℝ) : av s (fun _ => c) = c := by
  have hn : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (card_pos.mpr h).ne'
  simp [av,nsmul_eq_mul,hn]

theorem av_sub (s : Finset ι) (f g : ι → ℝ) :
    av s (fun i => f i - g i) = av s f - av s g := by simp [av,sum_sub_distrib,sub_div]

theorem av_scale (s : Finset ι) (c : ℝ) (f : ι → ℝ) :
    av s (fun i => c*f i) = c*av s f := by simp [av,← mul_sum,mul_div_assoc]

theorem av_cs (s : Finset ι) (f g : ι → ℝ) :
    (av s (fun i => f i*g i))^2 ≤ av s (fun i => (f i)^2)*av s (fun i => (g i)^2) := by
  simpa only [av,div_pow,div_mul_div_comm,pow_two] using
    (div_le_div_of_nonneg_right (sum_mul_sq_le_sq_mul_sq s f g) (sq_nonneg (s.card : ℝ)))

noncomputable def variance (s : Finset ι) (f : ι → ℝ) :=
  av s (fun i => (f i)^2) - (av s f)^2

theorem av_centered_sq {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ) :
    av s (fun i => (f i-av s f)^2) = variance s f := by
  have H := av_congr (s:=s) (f:=fun i => (f i-av s f)^2)
    (g:=fun i => ((f i)^2-(2*av s f)*f i) - (-(av s f)^2)) (fun i _ => by ring)
  rw [H,av_sub,av_sub,av_scale,av_const hs]
  unfold variance
  ring

theorem slice_ne {α} (U : Finset α) {b : ℕ} (hb : b ≤ U.card) :
    (U.powersetCard b).Nonempty := by
  apply card_pos.mp
  simpa only [card_powersetCard] using Nat.choose_pos hb

end ManickamMiklosSinghi.SevenK
