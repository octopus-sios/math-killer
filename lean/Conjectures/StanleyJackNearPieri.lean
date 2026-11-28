import Mathlib.Tactic.Ring

/-! Algebraic certificates for two infinite subfamilies of the near-Pieri
Jack calculation. The Pieri reduction that identifies their left sides
is in the accompanying proof; this file does not define Jack functions. -/

namespace StanleyJackNearPieri

/-- Reduced kernel for two occupied columns of arbitrary positive heights
`h`, `k`. The three inputs `b,c,w` stand for the two excess heights and
the excess inter-column spacing. The result uses only semiring operations. -/
def twoCore {R : Type*} [CommSemiring R] (a b c w : R) : R :=
  (b+1)*(c+1)*(a+b+c+w+2)*(a+w)*(2*a+b+c)

theorem twoColumnIdentity {R : Type*} [CommRing R] (a b c w : R) :
    let h := b+1
    let k := c+1
    let u := a+b
    let v := a+c
    let x := v+1+w
    (a-1+h+k) * (h*v*(x+u)*(x-k)*(x-a+1) +
                 k*u*(x-v)*(x+h)*(x+a-1)) -
      (h+k)*x*u*v*(x-v)*(x+u) = x * twoCore a b c w := by
  dsimp [twoCore]
  ring

/-- Subtraction-free polynomial for three singleton columns.
Here `s` and `p` are the sum and product of the two excess spacings. -/
def rookCore {R : Type*} [CommSemiring R] (a s p : R) : R :=
    6*a*(a+2)*(2*a+1)*(2*a^2+11*a+2)
  + s*(12*(a^5+1)+174*a*(a^3+1)+570*a^2*(a+1))
  + s^2*(22*(a^4+1)+216*a*(a^2+1)+424*a^2)
  + s^3*(12*(a^3+1)+96*a*(a+1)) + s^4*(2*(a^2+1)+14*a)
  + p*(68*(a^4+1)+234*a*(a^2+1)+296*a^2)
  + s*p*(120*(a^3+1)+300*a*(a+1)) + s^2*p*(68*(a^2+1)+116*a)
  + s^3*p*(12*a+12) + p^2*(20*(a^2+1)+50*a)
  + s*p^2*(24*a+24) + 6*s^2*p^2

private def early {R : Type*} [CommRing R] (a x : R) : R :=
  (x+a)*(x-1)*(x-a+1)

private def late {R : Type*} [CommRing R] (a x : R) : R :=
  (x-a)*(x+1)*(x+a-1)

private def idle {R : Type*} [CommRing R] (a x : R) : R :=
  x*(x-a)*(x+a)

/-- Polynomial identity after Vandermonde clearing, with the singleton
top hooks left in the bulk. The variables can themselves be polynomials. -/
theorem threeRookIdentity {R : Type*} [CommRing R] (a b c : R) :
    let x := a+1+b
    let y := a+1+c
    let z := x+y
    (a+2)*(early a x*early a z*idle a y +
           late a x*early a y*idle a z + late a y*late a z*idle a x)
      - 3*a*idle a x*idle a y*idle a z =
      x*y*z*rookCore a (b+c) (b*c) := by
  dsimp [early, late, idle, rookCore]
  ring

/-- Integral interpretation of one printed window diagram. A true flag
selects a lower hook in the original fraction, so on the last six boxes
it selects the *upper* hook after clearing the norm. -/
private def diagram {R : Type*} [CommRing R] (a x y : R)
    (i j k l m n o p q r s t : Bool) : R :=
    (if i then y-a else y-1) * (if j then x+y-a else x+y-1) *
    (if k then x-a else x-1) * (if l then 1 else a) *
    (if m then a+2 else 2*a+1) * (if n then 1 else a) *
    (if o then a else 1) * (if p then y+a else y+1) *
    (if q then a else 1) * (if r then x+y+a else x+y+1) *
    (if s then x+a else x+1) * (if t then a else 1)

/-- Mickler, arXiv:2401.01582v3, Conjecture 3.3. Hook assignments
in the source's array order; no fit to numerical coefficient values. -/
def windowSum {R : Type*} [CommRing R] (a x y : R) : R :=
  let D := diagram a x y
  let U := false
  let L := true
  7 * (D U U U U U U U U L U U L)
  - 2 * (D U U U U U U U U U U U L)
  + 1 * (D U L U U U U U U U U U L +
        D U U U U L U U U U U U L +
        D U U U U U U U U U L U L)
  - 2 * (D L U U U U U U U L U U L +
        D U U L U U U U U L U U L +
        D U U U L U U U U L U U L +
        D U U U U U L L U L U U U +
        D U U U U U U U L L U U L +
        D U U U U U U U U L U L L)
  - 2 * (D U L U U U U U U L U U L +
        D U U U U L U U U L U U L +
        D U U U U U U U U L L U L)
  + 1 * (D L L U U U U U U L U U L +
        D U L L U U U U U L U U L +
        D U U U L L U U U L U U L +
        D U U U U L L L U L U U U +
        D U U U U U U U L L L U L +
        D U U U U U U U U L L L L)
  + 1 * (D L U U U U L L U L U U U +
        D U U L L U U U U L U U L +
        D L U U U U U U U L U L L +
        D U U L U U U U L L U U L +
        D U U U L U U U U L U L L +
        D U U U U U L L L L U U U)

/-- Multiply the windowed integral expression by the three content
differences. It is exactly the Pieri numerator, with three corner hooks. -/
theorem micklerWindowIdentity {R : Type*} [CommRing R] (a x y : R) :
    let z := x+y
    x*y*z*windowSum a x y = a^3 *
      ((a+2)*(early a x*early a z*idle a y +
             late a x*early a y*idle a z + late a y*late a z*idle a x)
       - 3*a*idle a x*idle a y*idle a z) := by
  dsimp [windowSum, diagram, early, late, idle]
  ring

end StanleyJackNearPieri
