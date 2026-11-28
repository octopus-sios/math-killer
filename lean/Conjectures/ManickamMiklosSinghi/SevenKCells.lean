import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Exact real interval certification of the four rows and seven quartic cells.
No endpoint maximum assumption: after writing h as b X + a Y, X+Y=1, the
homogenized quartic is a polynomial in X,Y with nonnegative rational coefficients. -/

namespace ManickamMiklosSinghi.SevenK

structure Band where
  lo : ℝ
  P : ℝ
  rc : ℝ
  r : ℝ
  beta : ℝ
  D : ℝ
  H : ℝ

structure Cell where
  left : ℝ
  right : ℝ
  z : ℝ
  u : ℝ

namespace Band
noncomputable def W (b : Band) := b.P*(1-b.P)
noncomputable def gLo (b : Band) := 1-2*b.P
noncomputable def gHi (b : Band) := (1-2*b.lo)/(1-b.lo)
noncomputable def T (b : Band) := b.P/(1-b.P)
noncomputable def y (b : Band) := b.beta + b.r - 1
noncomputable def zeta (b : Band) := b.y / b.beta

structure Admissible (b : Band) : Prop where
  lo_nonneg : 0 ≤ b.lo
  lo_lt : b.lo < b.P
  P_le : b.P ≤ 1/5
  r_pos : 0 < b.r
  r_le : b.r ≤ 1
  beta_pos : 0 < b.beta
  beta_lt : b.beta < 1
  y_nonneg : 0 ≤ b.y
  y_lt : b.y < b.rc
  mono_mix : b.T*b.zeta ≤ 4*(1-b.beta)
  strict_mix : b.T*(1-b.beta)*b.zeta < (b.rc-b.y)^2
  D_nonneg : 0 ≤ b.D
  D_cap : b.P*(1-b.beta) ≤ b.D^2*((1-b.P)*b.beta+b.P*(1-b.beta))
  H_pos : 0 < b.H
  H_le : b.H ≤ 1
  H_cap : b.r ≤ b.H^2*(1-b.P)*(1+b.r)
  D_sq : b.D^2 ≤ 1/2

end Band

namespace Cell
noncomputable def d (c : Cell) := 2*c.z*(2*c.z+c.u)/(3*c.z+c.u)
noncomputable def coef (c : Cell) := (3*c.z+c.u)/(c.z^2*(c.z+c.u)^3)
noncomputable def lam (c : Cell) := 2*c.u-c.d
noncomputable def I (c : Cell) := 2*c.u*c.d-c.u^2
noncomputable def plus (c : Cell) (b : Band) :=
  3*b.W + (1-6*b.W)*b.D^2+c.lam*b.gHi*b.D
noncomputable def threshold (c : Cell) (b : Band) := c.I - b.r/((1-b.P)*c.coef)
end Cell

/-- Nonnegativity on a closed interval, not just a sample or its endpoints. -/
noncomputable def PolyOn (a b d₀ d₁ d₂ d₃ d₄ : ℝ) : Prop :=
  ∀ h : ℝ, a ≤ h → h ≤ b → 0 ≤ d₀+d₁*h+d₂*h^2+d₃*h^3+d₄*h^4

private theorem polyOn_of_homogeneous (a b d₀ d₁ d₂ d₃ d₄ : ℝ) (hab : a < b)
    (cert : ∀ X Y : ℝ, 0 ≤ X → 0 ≤ Y →
      0 ≤ d₀*(X+Y)^4 + d₁*(b*X+a*Y)*(X+Y)^3 + d₂*(b*X+a*Y)^2*(X+Y)^2
        + d₃*(b*X+a*Y)^3*(X+Y) + d₄*(b*X+a*Y)^4) :
    PolyOn a b d₀ d₁ d₂ d₃ d₄ := by
  intro h hl hr
  have hh : 0 < b-a := sub_pos.mpr hab
  let X := (h-a)/(b-a)
  let Y := (b-h)/(b-a)
  have hX : 0 ≤ X := div_nonneg (sub_nonneg.mpr hl) hh.le
  have hY : 0 ≤ Y := div_nonneg (sub_nonneg.mpr hr) hh.le
  have hsum : X+Y=1 := by dsimp [X,Y]; field_simp [hh.ne']; ring
  have hpos : b*X+a*Y=h := by dsimp [X,Y]; field_simp [hh.ne']; ring
  simpa [hsum,hpos] using cert X Y hX hY

private theorem polyOn_of_bernstein4 (a b d₀ d₁ d₂ d₃ d₄ : ℝ) (hab : a < b)
    (h0 : 0 ≤ d₀+d₁*b+d₂*b^2+d₃*b^3+d₄*b^4)
    (h1 : 0 ≤ 4*d₀+d₁*(3*b+a)+2*d₂*b*(b+a)+d₃*b^2*(b+3*a)+4*d₄*b^3*a)
    (h2 : 0 ≤ 6*d₀+3*d₁*(b+a)+d₂*(b^2+4*b*a+a^2)+3*d₃*b*a*(b+a)+6*d₄*b^2*a^2)
    (h3 : 0 ≤ 4*d₀+d₁*(b+3*a)+2*d₂*a*(b+a)+d₃*a^2*(3*b+a)+4*d₄*b*a^3)
    (h4 : 0 ≤ d₀+d₁*a+d₂*a^2+d₃*a^3+d₄*a^4) :
    PolyOn a b d₀ d₁ d₂ d₃ d₄ := by
  apply polyOn_of_homogeneous _ _ _ _ _ _ _ hab
  intro X Y hX hY
  have he : d₀*(X+Y)^4 + d₁*(b*X+a*Y)*(X+Y)^3 + d₂*(b*X+a*Y)^2*(X+Y)^2
        + d₃*(b*X+a*Y)^3*(X+Y) + d₄*(b*X+a*Y)^4 =
       (d₀+d₁*b+d₂*b^2+d₃*b^3+d₄*b^4)*X^4*Y^0 +
       (4*d₀+d₁*(3*b+a)+2*d₂*b*(b+a)+d₃*b^2*(b+3*a)+4*d₄*b^3*a)*X^3*Y^1 +
       (6*d₀+3*d₁*(b+a)+d₂*(b^2+4*b*a+a^2)+3*d₃*b*a*(b+a)+6*d₄*b^2*a^2)*X^2*Y^2 +
       (4*d₀+d₁*(b+3*a)+2*d₂*a*(b+a)+d₃*a^2*(3*b+a)+4*d₄*b*a^3)*X^1*Y^3 +
       (d₀+d₁*a+d₂*a^2+d₃*a^3+d₄*a^4)*X^0*Y^4 := by ring
  rw [he]
  positivity

noncomputable def Cell.Bounds (c : Cell) (b : Band) (θ : ℝ) : Prop :=
  PolyOn c.left c.right (c.threshold b-3*θ) (c.lam*b.gLo) (6*θ-1) 0 0 ∧
  PolyOn c.left c.right (c.threshold b-c.plus b) 0 (c.plus b-3*θ)
    (c.lam*b.gLo) (6*θ-1)

structure Cell.Admissible (c : Cell) (b : Band) : Prop where
  z_pos : 0 < c.z
  u_pos : 0 < c.u
  lam_nonneg : 0 ≤ c.lam
  zero_bound : c.Bounds b 0
  W_bound : c.Bounds b b.W

noncomputable def row1 : Band := ⟨0, (1/7), 0.69, 0.87, 0.588, 0.324, 0.737⟩
noncomputable def row2 : Band := ⟨(1/7), (1/6), 0.69, 0.87, 0.560, 0.369, 0.748⟩
noncomputable def row3 : Band := ⟨0, (1/8), 0.87, 1, 0.644, 0.271, 0.756⟩
noncomputable def row4 : Band := ⟨(1/8), (1/7), 0.87, 1, 0.6175, 0.306, 0.764⟩
noncomputable def cell1 : Cell := ⟨0, 0.737, 0.69, 0.6⟩
noncomputable def cell2 : Cell := ⟨0, 0.54, 0.75, 0.57⟩
noncomputable def cell3 : Cell := ⟨0.54, 0.748, 0.7, 0.64⟩
noncomputable def cell4 : Cell := ⟨0, 0.756, 0.67, 0.63⟩
noncomputable def cell5 : Cell := ⟨0, 0.459, 0.7, 0.54⟩
noncomputable def cell6 : Cell := ⟨0.459, 0.604, 0.68, 0.58⟩
noncomputable def cell7 : Cell := ⟨0.604, 0.764, 0.64, 0.68⟩

theorem row1_valid : row1.Admissible := by
  constructor <;> norm_num [row1, Band.W, Band.gLo, Band.gHi, Band.y, Band.T, Band.zeta]

theorem row2_valid : row2.Admissible := by
  constructor <;> norm_num [row2, Band.W, Band.gLo, Band.gHi, Band.y, Band.T, Band.zeta]

theorem row3_valid : row3.Admissible := by
  constructor <;> norm_num [row3, Band.W, Band.gLo, Band.gHi, Band.y, Band.T, Band.zeta]

theorem row4_valid : row4.Admissible := by
  constructor <;> norm_num [row4, Band.W, Band.gLo, Band.gHi, Band.y, Band.T, Band.zeta]

theorem cell1_valid : cell1.Admissible row1 := by
  constructor
  · norm_num [cell1, row1, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell1, row1, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell1, row1, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  all_goals
    constructor <;> apply polyOn_of_bernstein4
    all_goals norm_num [Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi, row1, row2, row3, row4,
      cell1, cell2, cell3, cell4, cell5, cell6, cell7]

theorem cell2_valid : cell2.Admissible row2 := by
  constructor
  · norm_num [cell2, row2, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell2, row2, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell2, row2, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  all_goals
    constructor <;> apply polyOn_of_bernstein4
    all_goals norm_num [Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi, row1, row2, row3, row4,
      cell1, cell2, cell3, cell4, cell5, cell6, cell7]

theorem cell3_valid : cell3.Admissible row2 := by
  constructor
  · norm_num [cell3, row2, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell3, row2, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell3, row2, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  all_goals
    constructor <;> apply polyOn_of_bernstein4
    all_goals norm_num [Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi, row1, row2, row3, row4,
      cell1, cell2, cell3, cell4, cell5, cell6, cell7]

theorem cell4_valid : cell4.Admissible row3 := by
  constructor
  · norm_num [cell4, row3, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell4, row3, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell4, row3, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  all_goals
    constructor <;> apply polyOn_of_bernstein4
    all_goals norm_num [Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi, row1, row2, row3, row4,
      cell1, cell2, cell3, cell4, cell5, cell6, cell7]

theorem cell5_valid : cell5.Admissible row4 := by
  constructor
  · norm_num [cell5, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell5, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell5, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  all_goals
    constructor <;> apply polyOn_of_bernstein4
    all_goals norm_num [Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi, row1, row2, row3, row4,
      cell1, cell2, cell3, cell4, cell5, cell6, cell7]

theorem cell6_valid : cell6.Admissible row4 := by
  constructor
  · norm_num [cell6, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell6, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell6, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  all_goals
    constructor <;> apply polyOn_of_bernstein4
    all_goals norm_num [Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi, row1, row2, row3, row4,
      cell1, cell2, cell3, cell4, cell5, cell6, cell7]

theorem cell7_valid : cell7.Admissible row4 := by
  constructor
  · norm_num [cell7, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell7, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  · norm_num [cell7, row4, Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi]
  all_goals
    constructor <;> apply polyOn_of_bernstein4
    all_goals norm_num [Cell.Bounds, Cell.threshold, Cell.plus, Cell.I, Cell.lam,
      Cell.d, Cell.coef, Band.W, Band.gLo, Band.gHi, row1, row2, row3, row4,
      cell1, cell2, cell3, cell4, cell5, cell6, cell7]

/-- At any allowed negative coordinate magnitude the appropriate row supplies a
certified quartic with that magnitude inside its interval. -/
theorem rows_certified (b : Band)
    (hb : b = row1 ∨ b = row2 ∨ b = row3 ∨ b = row4) :
    b.Admissible ∧ ∀ h : ℝ, 0 ≤ h → h ≤ b.H →
      ∃ c : Cell, c.Admissible b ∧ c.left ≤ h ∧ h ≤ c.right := by
  rcases hb with rfl | rfl | rfl | rfl
  · exact ⟨row1_valid, fun h hl hr => ⟨cell1, cell1_valid, hl, hr⟩⟩
  · refine ⟨row2_valid, ?_⟩
    intro h hl hr
    by_cases hh : h ≤ 0.54
    · exact ⟨cell2, cell2_valid, hl, hh⟩
    · exact ⟨cell3, cell3_valid, (lt_of_not_ge hh).le, hr⟩
  · exact ⟨row3_valid, fun h hl hr => ⟨cell4, cell4_valid, hl, hr⟩⟩
  · refine ⟨row4_valid, ?_⟩
    intro h hl hr
    by_cases hh : h ≤ 0.459
    · exact ⟨cell5, cell5_valid, hl, hh⟩
    · by_cases hk : h ≤ 0.604
      · exact ⟨cell6, cell6_valid, (lt_of_not_ge hh).le, hk⟩
      · exact ⟨cell7, cell7_valid, (lt_of_not_ge hk).le, hr⟩

end ManickamMiklosSinghi.SevenK
