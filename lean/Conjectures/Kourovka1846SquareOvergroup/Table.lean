module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Tactic

/-!
# Finite test for the marked kernel

The two fields of a normalized law describe conjugation by the outside generator
and its square. For each root action triple, the test looks for seven cosets
separated by their actions on the kernel and, when known, their squares.
-/

@[expose] public section

namespace Kourovka1846.D8.Marked

abbrev D := DihedralGroup 4
abbrev r : D := .r 1
abbrev s : D := .sr 0
abbrev E := D × Bool
abbrev e : E := (1, false)
abbrev R : E := (r, false)
abbrev S : E := (s, false)
abbrev V : E := (.sr 1, false)
abbrev T : E := (1, true)

structure Law where
  shift : Bool
  carry : D
  deriving DecidableEq

def twist (k : Bool) : D → D
  | .r i => .r i
  | .sr i => if k then .sr (1 + i) else .sr i

def Law.mul (L : Law) (u v : E) : E :=
  let w := u.1 * (if u.2 then twist L.shift v.1 else v.1)
  (if u.2 && v.2 then w * L.carry else w, xor u.2 v.2)

def Law.allowed (L : Law) : Bool :=
  (twist L.shift L.carry == L.carry) &&
  (twist L.shift (twist L.shift r) * L.carry == L.carry * r) &&
  (twist L.shift (twist L.shift s) * L.carry == L.carry * s)

/-- Evaluation of a normal form in marked generators. -/
def rotWord {A : Type*} (m : A → A → A) (o p : A) (i : ZMod 4) : A :=
  match i.val with
  | 0 => o
  | 1 => p
  | 2 => m p p
  | _ => m (m p p) p

def word {A : Type*} (m : A → A → A) (o p q x : A) (u : E) : A :=
  let d := match u.1 with
    | .r i => rotWord m o p i
    | .sr i => m q (rotWord m o p i)
  if u.2 then m d x else d

abbrev Images := E × E × E

def transform (L : Law) (v : Images) : E → E := word L.mul e v.1 v.2.1 v.2.2

def elements : List E :=
  [(1,false), (.r 1,false), (.r 2,false), (.r 3,false),
   (.sr 0,false), (.sr 1,false), (.sr 2,false), (.sr 3,false),
   (1,true), (.r 1,true), (.r 2,true), (.r 3,true),
   (.sr 0,true), (.sr 1,true), (.sr 2,true), (.sr 3,true)]

theorem exhaustive (u : E) : u ∈ elements := (by decide : ∀ u : E, u ∈ elements) u

def gens : List E := [R,S,T]

inductive Mark | rot | flip | third deriving DecidableEq

def Mark.pt : Mark → E | .rot => R | .flip => S | .third => V

def quick (L : Law) (g : Mark) (p q : E) : Bool :=
  match g with
  | .rot => p == R
  | .flip => q == S
  | .third => L.mul q p == V

/-- Conjugation by a square root fixes its square and its second iterate
is conjugation by that square. Multiplicativity is tested on right
multiplication by the three marked generators. -/
def feasible (L : Law) (g : Mark) (v : Images) : Bool :=
  let f := transform L v
  gens.all (fun i => L.mul (f (f i)) g.pt == L.mul g.pt i) &&
    elements.all (fun i => gens.all (fun j => f (L.mul i j) == L.mul (f i) (f j)))

def candidates (L : Law) (g : Mark) : List Images :=
  elements.flatMap fun p => elements.flatMap fun q =>
    if quick L g p q then
      (elements.filter fun t => feasible L g (p,q,t)).map fun t => (p,q,t)
    else []

inductive W | id | a | b | c | ab | ba | ac | bc | bab deriving DecidableEq

structure Sample where
  act : E → E
  square : Option E

def sample (f g h : E → E) : W → Sample
  | .id => ⟨id, some e⟩
  | .a => ⟨f, some R⟩
  | .b => ⟨g, some S⟩
  | .c => ⟨h, some V⟩
  | .ab => ⟨f ∘ g, none⟩
  | .ba => ⟨g ∘ f, none⟩
  | .ac => ⟨f ∘ h, none⟩
  | .bc => ⟨g ∘ h, none⟩
  | .bab => ⟨g ∘ f ∘ g ∘ g ∘ g, some (g R)⟩

def compatible (L : Law) (u v : Sample) (k : E) : Bool :=
  (gens.all fun j => L.mul (u.act j) k == L.mul k (v.act j)) &&
  match u.square, v.square with
  | some l, some r => l == L.mul (L.mul k (v.act k)) r
  | _, _ => true

def apart (L : Law) (u v : Sample) : Bool :=
  !(elements.any (compatible L u v))

def menus : List (List W) :=
  [[.id,.a,.b,.c,.ab,.ba,.bc], [.id,.a,.b,.c,.ab,.ac,.bc],
   [.id,.a,.b,.c,.ab,.ba,.bab]]

def passes (L : Law) (f g h : Images) : Bool :=
  let w := sample (transform L f) (transform L g) (transform L h)
  menus.any fun ws => decide (ws.Pairwise (fun i j => apart L (w i) (w j) = true))

def test (L : Law) : Bool :=
  !L.allowed ||
  let A := candidates L .rot
  let B := candidates L .flip
  let C := candidates L .third
  B.all fun g => C.all fun h => A.all fun f => passes L f g h

end Kourovka1846.D8.Marked

namespace Kourovka1846.D8.Marked


-- The only four carries compatible with the normalized conjugation actions.
private theorem allowed_laws (L : Law) (h : L.allowed = true) :
    L = ⟨false, .r 0⟩ ∨ L = ⟨false, .r 2⟩ ∨ L = ⟨true, .r 1⟩ ∨ L = ⟨true, .r 3⟩ := by
  obtain ⟨k,a⟩ := L
  exact (by decide : ∀ (k : Bool) (a : D), (Law.mk k a).allowed = true →
    Law.mk k a = ⟨false, .r 0⟩ ∨ Law.mk k a = ⟨false, .r 2⟩ ∨
    Law.mk k a = ⟨true, .r 1⟩ ∨ Law.mk k a = ⟨true, .r 3⟩) k a h

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000

private theorem test_false_0 : test ⟨false, .r 0⟩ = true := by decide +kernel

private theorem test_false_2 : test ⟨false, .r 2⟩ = true := by decide +kernel

private theorem test_true_1 : test ⟨true, .r 1⟩ = true := by decide +kernel

private theorem test_true_3 : test ⟨true, .r 3⟩ = true := by decide +kernel

/-- For every allowed marked kernel and triple of root actions, one of
the tested lists consists of seven pairwise incompatible cosets. -/
theorem table_check (L : Law) : test L = true := by
  cases h : L.allowed with
  | false => simp [test, h]
  | true =>
    rcases allowed_laws L h with rfl | rfl | rfl | rfl
    · exact test_false_0
    · exact test_false_2
    · exact test_true_1
    · exact test_true_3

end Kourovka1846.D8.Marked
