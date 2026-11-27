import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A degree-four Koszul class for the 15-point Sylvester matroid

We certify the linear-algebra obstruction, not the identification of the polynomial
presentation with the graded Möbius algebra. Points 0,...,7 are affine; 7+h is
the direction h. The zero product of equal points is not a line. A 2-chain
is recorded by its evaluations on alternating 2-cochains. The first map is
tested against arbitrary rational functionals on the degree-four 1-chains.
-/

namespace FouliSylvesterMatroids

abbrev Point := Fin 15

/-- The third constructor stores two affine endpoints in increasing order.
Only actual pair-lines are produced by the differential. -/
inductive Row where
  | zeroProduct
  | infinity
  | secant (x y : Nat)
deriving DecidableEq

private def sec (x y : Nat) := Row.secant (min x y) (max x y)

/-- Flat multiplication of two degree-one generators. -/
def through (t a : Point) : Row :=
  if t = a then .zeroProduct
  else if t.val < 8 then
    if a.val < 8 then sec t.val a.val
    else sec t.val (Nat.xor t.val (a.val - 7))
  else if a.val < 8 then sec a.val (Nat.xor a.val (t.val - 7))
  else .infinity

/-- Coefficient of the top flat after multiplication by a point. -/
def outside : Row → Point → ℤ
  | .zeroProduct, _ => 0
  | .infinity, i => if i.val < 8 then 1 else 0
  | .secant x y, i =>
    if i.val = x ∨ i.val = y ∨ i.val = 7 + Nat.xor x y then 0 else 1

private def inT (i : Point) : Prop := i.val < 4 ∨ (8 ≤ i.val ∧ i.val ≤ 10)
private instance (i : Point) : Decidable (inT i) := by unfold inT; infer_instance

private def u (i : Point) : ℤ := if i.val < 4 then 1 else 0

/-- Indicator of T minus L for the six unaltered lines, zero otherwise. -/
private def r : Row → Point → ℤ
  | .secant x y, i =>
    if x < 4 ∧ y < 4 ∧ inT i then outside (.secant x y) i else 0
  | _, _ => 0

private def det2 (L : Row) (a b : Point) : ℤ := r L a * u b - r L b * u a

/-- The restriction has one additional line: the three internal directions. -/
private def exceptional (t a : Point) : ℤ :=
  if t ≠ a ∧ 8 ≤ t.val ∧ t.val ≤ 10 ∧ 8 ≤ a.val ∧ a.val ≤ 10 then 1 else 0

private def tr (t a b : Point) : ℤ :=
  r (through t a) b + exceptional t a * u b

-- Only this three-point incidence check is enumerated. Cancellation on
-- four points and separation from every rational combination are symbolic.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 4000000 in
private theorem tr_symm : ∀ (t a b : Point), tr t a b = tr t b a := by decide +kernel

private theorem det_through (t a b c : Point) :
    det2 (through t a) b c = tr t a b * u c - tr t a c * u b := by
  unfold det2 tr
  ring

private theorem cancellation (t a b c : Point) :
    det2 (through t a) b c - det2 (through t b) a c + det2 (through t c) a b = 0 := by
  rw [det_through, det_through, det_through, tr_symm t b a, tr_symm t c a,
    tr_symm t c b]
  ring

/-- An alternating functional on line ⊗ wedge-pair symbols; the zero
product must contribute nothing. Superfluous secant labels are never used. -/
structure Test where
  coeff : Row → Point → Point → ℚ
  swap : ∀ L a b, coeff L a b = -coeff L b a
  zeroRow : ∀ a b, coeff .zeroProduct a b = 0

private def alt (s : Row → Point → ℚ) (h : Point → ℚ)
    (hs : ∀ a, s .zeroProduct a = 0) : Test where
  coeff L a b := s L a * h b - s L b * h a
  swap := by intros; ring
  zeroRow := by intro a b; simp [hs]

/-- Pull back an arbitrary functional on the 1-chain (top flat, point)
along the Koszul differential d₂. -/
def d2Pull (g : Point → ℚ) : Test :=
  alt (fun L a => (outside L a : ℚ)) g (by intro a; rfl)

def separator : Test :=
  alt (fun L a => (r L a : ℚ)) (fun b => (u b : ℚ)) (by intro a; rfl)

private theorem separator_coeff (L : Row) (a b : Point) :
    separator.coeff L a b = (det2 L a b : ℚ) := by
  simp [separator, alt, det2]

/-- Evaluation of a column of d₃ against an arbitrary 2-cochain. -/
def face (t a b c : Point) (f : Test) : ℚ :=
  f.coeff (through t a) b c - f.coeff (through t b) a c + f.coeff (through t c) a b

theorem separator_kills_column (t a b c : Point) : face t a b c separator = 0 := by
  calc
    _ = ((det2 (through t a) b c - det2 (through t b) a c +
          det2 (through t c) a b : ℤ) : ℚ) := by simp [face, separator_coeff]
    _ = 0 := by simp [cancellation]

def cycle (f : Test) : ℚ :=
  f.coeff (through 0 1) 9 2 - f.coeff (through 4 5) 9 2

theorem cycle_closed (g : Point → ℚ) : cycle (d2Pull g) = 0 := by
  change ((1 : ℚ) * g 2 - 1 * g 9) - (1 * g 2 - 1 * g 9) = 0
  exact sub_self _

theorem unit_pairing : cycle separator = 1 := by
  have first : det2 (through 0 1) 9 2 = 1 := by decide +kernel
  have second : det2 (through 4 5) 9 2 = 0 := by decide +kernel
  simp [cycle, separator_coeff, first, second]

/-- A finite rational linear combination of the actual signed d₃ columns;
allowing all wedge orders does not restrict the span. -/
def boundary : List (ℚ × Point × Point × Point × Point) → Test → ℚ
  | [], _ => 0
  | (q, t, a, b, c) :: rest, f => q * face t a b c f + boundary rest f

private theorem boundary_zero (s) : boundary s separator = 0 := by
  induction s with
  | nil => rfl
  | cons v rest ih =>
    rcases v with ⟨q, t, a, b, c⟩
    simp [boundary, separator_kills_column, ih]

theorem cycle_not_boundary (s) : boundary s ≠ cycle := by
  intro h
  have e := congrFun h separator
  rw [boundary_zero, unit_pairing] at e
  norm_num at e

end FouliSylvesterMatroids
