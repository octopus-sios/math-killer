module

public import Mathlib.RingTheory.PowerSeries.Catalan
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# The lattice coefficient in the connected chordal diagram enumeration

This module verifies the unrestricted axial-walk coefficient calculation in
Section 5 of the written proof. It does not assume any diagram count.
-/

namespace NabergallChordalDiagrams

/-- Number of cardinal-direction walks from the origin to `(x,y)` in `n` steps. -/
def axialWalks : ℕ → ℤ → ℤ → ℕ
  | 0, x, y => if x = 0 ∧ y = 0 then 1 else 0
  | n+1, x, y =>
    axialWalks n (x-1) y + axialWalks n (x+1) y +
    axialWalks n x (y-1) + axialWalks n x (y+1)

/-- Binomial coefficient extended by zero to negative lower arguments. -/
def zChoose (n : ℕ) (k : ℤ) : ℕ :=
  if 0 ≤ k then n.choose k.toNat else 0

private theorem zChoose_zero (k : ℤ) : zChoose 0 k = if k = 0 then 1 else 0 := by
  cases k with
  | ofNat k =>
    cases k with
    | zero => simp [zChoose]
    | succ k => simp [zChoose]; omega
  | negSucc k => simp [zChoose]

private theorem zChoose_succ (n : ℕ) (k : ℤ) :
    zChoose (n+1) k = zChoose n (k-1) + zChoose n k := by
  cases k with
  | negSucc k => simp [zChoose]
  | ofNat k =>
    cases k with
    | zero => simp [zChoose]
    | succ k =>
      have h : 0 ≤ (k : ℤ) + 1 := by omega
      simp [zChoose, Nat.choose_succ_succ, h]

/-- Rotating coordinates converts each step into two independent signs. -/
theorem axialWalks_rotated (n : ℕ) (k l : ℤ) :
    axialWalks n (k+l-n) (k-l) = zChoose n k * zChoose n l := by
  induction n generalizing k l with
  | zero =>
    simp only [axialWalks, Nat.cast_zero, sub_zero, zChoose_zero]
    split_ifs <;> omega
  | succ n ih =>
    rw [axialWalks, zChoose_succ, zChoose_succ]
    have step (i j x y : ℤ) (hx : x = i+j-n) (hy : y = i-j) :
        axialWalks n x y = zChoose n i * zChoose n j := hx ▸ hy ▸ ih i j
    rw [step (k-1) (l-1) _ _ (by push_cast; ring) (by ring),
        step k l _ _ (by push_cast; ring) rfl,
        step (k-1) l _ _ (by push_cast; ring) (by ring),
        step k (l-1) _ _ (by push_cast; ring) (by ring)]
    ring

/-- The origin-minus-two walk coefficient extracted from the kernel,
written without truncated subtraction. -/
theorem walk_coefficient (m : ℕ) :
    axialWalks (2*m) 0 0 = axialWalks (2*m) 2 0 + (2*m+1) * catalan m ^ 2 := by
  have h0 := axialWalks_rotated (2*m) (m : ℤ) (m : ℤ)
  have h2 := axialWalks_rotated (2*m) ((m+1 : ℕ) : ℤ) ((m+1 : ℕ) : ℤ)
  have c0 : ((m : ℤ)+m-(2*m : ℕ)) = 0 := by push_cast; ring
  have c2 : (((m+1 : ℕ) : ℤ)+(m+1 : ℕ)-(2*m : ℕ)) = 2 := by push_cast; ring
  simp only [c0, sub_self] at h0
  simp only [c2, sub_self] at h2
  rw [h0, h2]
  simp only [zChoose, Int.natCast_nonneg, ite_true, Int.toNat_natCast]
  have b0 : (2*m).choose m = (m+1) * catalan m :=
    (succ_mul_catalan_eq_centralBinom m).symm
  have b2 : (2*m).choose (m+1) = m * catalan m := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_succ m)
    rw [Nat.choose_succ_right_eq, b0, show 2*m-m=m by omega]
    simp only [Nat.succ_eq_add_one]
    ring
  rw [b0, b2]
  ring

end NabergallChordalDiagrams
