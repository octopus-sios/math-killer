import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Refutation of Gaetz–Gao's Strong Hull Property Conjecture (`arXiv:2012.06841`)

Conjecture 1.2 of Gaetz and Gao (*The hull metric on Coxeter groups*, `arXiv:2012.06841`)
asserts that for every Coxeter group `(W, S)`, the undirected right Cayley graph
`Cay(W, S)` has the **strong hull property**: for all `u, v, w ∈ W`,
`|Conv(u, v)| * |Conv(v, w)| ≥ |Conv(u, v, w)|`.
In particular, this would imply the **hull property**
`|Conv(u, v)| * |Conv(v, w)| ≥ |Conv(u, w)|` (equivalently, that
`log |Conv(-, -)|` is a metric on `W`).

We refute both the strong hull property and the ordinary hull property unconditionally
for the affine Coxeter group `W(A₃~)` of rank 4 (`A3TildeMatrix.toCoxeterSystem`).
-/

namespace YiboGaoCoxeterGeodesicHull

open SimpleGraph

/-! ### 1. Geodesic convexity and (strong) hull property on graphs -/

section GraphHull

variable {V : Type*}

/-- A vertex subset `C` of a graph `G` is geodesically convex if every vertex lying on a
shortest path between two vertices of `C` belongs to `C`. -/
def IsConvex (G : SimpleGraph V) (C : Set V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, ∀ w : V, G.dist u w + G.dist w v = G.dist u v → w ∈ C

/-- The geodesic convex hull of `X ⊆ V` in `G`: the intersection of all convex subsets
containing `X`. -/
def convexHull (G : SimpleGraph V) (X : Set V) : Set V :=
  ⋂₀ {C : Set V | X ⊆ C ∧ IsConvex G C}

/-- A graph `G` has the hull property if `|Conv(u, w)| ≤ |Conv(u, v)| * |Conv(v, w)|`
for all `u, v, w ∈ V`. -/
def HasHullProperty (G : SimpleGraph V) : Prop :=
  ∀ u v w : V,
    (convexHull G {u, w}).encard ≤
      (convexHull G {u, v}).encard * (convexHull G {v, w}).encard

/-- A graph `G` has the strong hull property if `|Conv(u, v, w)| ≤ |Conv(u, v)| * |Conv(v, w)|`
for all `u, v, w ∈ V`. -/
def HasStrongHullProperty (G : SimpleGraph V) : Prop :=
  ∀ u v w : V,
    (convexHull G {u, v, w}).encard ≤
      (convexHull G {u, v}).encard * (convexHull G {v, w}).encard

theorem subset_convexHull (G : SimpleGraph V) (X : Set V) : X ⊆ convexHull G X := by
  intro x hx C hC
  exact hC.1 hx

theorem convexHull_subset {G : SimpleGraph V} {X C : Set V}
    (hXC : X ⊆ C) (hC : IsConvex G C) : convexHull G X ⊆ C := by
  intro x hx
  exact hx C ⟨hXC, hC⟩

theorem isConvex_convexHull (G : SimpleGraph V) (X : Set V) : IsConvex G (convexHull G X) := by
  intro u hu v hv w hdist C hC
  exact hC.2 u (hu C hC) v (hv C hC) w hdist

theorem convexHull_mono (G : SimpleGraph V) {X Y : Set V} (hXY : X ⊆ Y) :
    convexHull G X ⊆ convexHull G Y :=
  convexHull_subset (hXY.trans (subset_convexHull G Y)) (isConvex_convexHull G Y)

theorem isConvex_inter {G : SimpleGraph V} {C₁ C₂ : Set V}
    (h₁ : IsConvex G C₁) (h₂ : IsConvex G C₂) : IsConvex G (C₁ ∩ C₂) := by
  intro u hu v hv w hdist
  exact ⟨h₁ u hu.1 v hv.1 w hdist, h₂ u hu.2 v hv.2 w hdist⟩

theorem mem_convexHull_pair_of_dist (G : SimpleGraph V) {u v w : V}
    (hdist : G.dist u w + G.dist w v = G.dist u v) : w ∈ convexHull G {u, v} :=
  isConvex_convexHull G {u, v} u (subset_convexHull G {u, v} (by simp))
    v (subset_convexHull G {u, v} (by simp)) w hdist

theorem hasHullProperty_of_hasStrongHullProperty {G : SimpleGraph V}
    (h : HasStrongHullProperty G) : HasHullProperty G := by
  intro u v w
  have hsub : convexHull G {u, w} ⊆ convexHull G {u, v, w} :=
    convexHull_mono G (by intro x hx; simp at hx ⊢; tauto)
  exact (Set.encard_le_encard hsub).trans (h u v w)

end GraphHull

/-! ### 2. Undirected right Cayley graph of a Coxeter system -/

section CoxeterCayley

variable {B W : Type*} [Group W] {M : CoxeterMatrix B}

/-- The undirected right Cayley graph of a Coxeter system `(W, S)` with edges
`u ~ u * s_i` for `i : B`. -/
def cayleyGraph (cs : CoxeterSystem M W) : SimpleGraph W where
  Adj u v := ∃ i : B, v = u * cs.simple i
  symm := ⟨fun u v h => by
    rcases h with ⟨i, rfl⟩
    exact ⟨i, by simp [mul_assoc]⟩⟩
  loopless := ⟨fun u h => by
    rcases h with ⟨i, h⟩
    have h1 : cs.simple i = 1 := by
      have := congrArg (u⁻¹ * ·) h
      simpa [mul_assoc] using this.symm
    have hlen := cs.length_simple i
    rw [h1, cs.length_one] at hlen
    omega⟩

private def walkOfWord (cs : CoxeterSystem M W) (u : W) :
    (ω : List B) → (cayleyGraph cs).Walk u (u * cs.wordProd ω)
  | [] => SimpleGraph.Walk.nil.copy rfl (by simp)
  | i :: ω =>
    have hadj : (cayleyGraph cs).Adj u (u * cs.simple i) := ⟨i, rfl⟩
    have hrest := walkOfWord cs (u * cs.simple i) ω
    (SimpleGraph.Walk.cons hadj hrest).copy rfl (by simp [CoxeterSystem.wordProd_cons, mul_assoc])

private theorem length_walkOfWord (cs : CoxeterSystem M W) (u : W) (ω : List B) :
    (walkOfWord cs u ω).length = ω.length := by
  induction ω generalizing u with
  | nil =>
    simp [walkOfWord]
  | cons i ω ih =>
    simpa [walkOfWord, SimpleGraph.Walk.length] using ih (u * cs.simple i)

private theorem exists_word_of_walk (cs : CoxeterSystem M W) {u v : W}
    (p : (cayleyGraph cs).Walk u v) :
    ∃ ω : List B, ω.length = p.length ∧ v = u * cs.wordProd ω := by
  induction p with
  | nil => exact ⟨[], rfl, by simp⟩
  | @cons a b c hadj p ih =>
    rcases hadj with ⟨i, rfl⟩
    rcases ih with ⟨ω, hlen, hv⟩
    refine ⟨i :: ω, ?_, ?_⟩
    · change ω.length + 1 = p.length + 1
      omega
    simpa [CoxeterSystem.wordProd_cons, mul_assoc] using hv

theorem cayleyGraph_connected (cs : CoxeterSystem M W) : (cayleyGraph cs).Connected := by
  refine ⟨fun u v => ?_⟩
  obtain ⟨ω, _, hω⟩ := cs.exists_isReduced (u⁻¹ * v)
  have hv : u * cs.wordProd ω = v := by
    rw [← hω]
    exact mul_inv_cancel_left u v
  exact ⟨(walkOfWord cs u ω).copy rfl hv⟩

theorem cayleyGraph_dist (cs : CoxeterSystem M W) (u v : W) :
    (cayleyGraph cs).dist u v = cs.length (u⁻¹ * v) := by
  apply le_antisymm
  · obtain ⟨ω, hred, hω⟩ := cs.exists_isReduced (u⁻¹ * v)
    have hv : u * cs.wordProd ω = v := by
      rw [← hω]
      exact mul_inv_cancel_left u v
    let p : (cayleyGraph cs).Walk u v := (walkOfWord cs u ω).copy rfl hv
    have hle := (cayleyGraph cs).dist_le p
    have hplen : p.length = ω.length := by
      simp [p, length_walkOfWord]
    rw [hplen, ← hred.eq, ← hω] at hle
    exact hle
  · obtain ⟨p, hp⟩ := (cayleyGraph_connected cs).exists_path_of_dist u v
    obtain ⟨ω, hlen, hv⟩ := exists_word_of_walk cs p
    have huv : u⁻¹ * v = cs.wordProd ω := by
      rw [hv]
      exact inv_mul_cancel_left u (cs.wordProd ω)
    calc
      cs.length (u⁻¹ * v) = cs.length (cs.wordProd ω) := by rw [huv]
      _ ≤ ω.length := cs.length_wordProd_le ω
      _ = (cayleyGraph cs).dist u v := by rw [hlen, hp.2]

end CoxeterCayley

/-! ### 3. The affine Coxeter group `W(A₃~)` and its affine permutation model `AffPerm4` -/

/-- Coxeter matrix of affine type `A₃~` (a 4-cycle of edges labeled 3, opposite edges labeled 2). -/
def A3TildeMatrix : CoxeterMatrix (Fin 4) where
  M := !![1, 3, 2, 3;
          3, 1, 3, 2;
          2, 3, 1, 3;
          3, 2, 3, 1]
  diagonal := by
    intro i
    fin_cases i <;> rfl
  off_diagonal := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

abbrev W3 := A3TildeMatrix.Group
abbrev cs3 : CoxeterSystem A3TildeMatrix W3 := A3TildeMatrix.toCoxeterSystem

/-- Affine permutations of period 4 and zero net shift, represented in semidirect-product
coordinates `(a, σ) ∈ Q(A₃) ⋊ S₄`. -/
@[ext]
structure AffPerm4 where
  a : Fin 4 → ℤ
  sum_eq : a 0 + a 1 + a 2 + a 3 = 0
  σ : Equiv.Perm (Fin 4)

namespace AffPerm4

instance : One AffPerm4 where
  one := ⟨fun _ => 0, by simp, 1⟩

instance : Mul AffPerm4 where
  mul f g :=
    { a := fun i => f.a i + g.a (f.σ⁻¹ i)
      sum_eq := by
        have hperm :
            g.a (f.σ⁻¹ 0) + g.a (f.σ⁻¹ 1) + g.a (f.σ⁻¹ 2) + g.a (f.σ⁻¹ 3) =
            g.a 0 + g.a 1 + g.a 2 + g.a 3 := by
          have hsum := Equiv.sum_comp f.σ⁻¹ g.a
          simpa [Fin.sum_univ_four] using hsum
        linarith [f.sum_eq, g.sum_eq, hperm]
      σ := f.σ * g.σ }

instance : Inv AffPerm4 where
  inv f :=
    { a := fun i => -f.a (f.σ i)
      sum_eq := by
        have hperm :
            f.a (f.σ 0) + f.a (f.σ 1) + f.a (f.σ 2) + f.a (f.σ 3) =
            f.a 0 + f.a 1 + f.a 2 + f.a 3 := by
          have hsum := Equiv.sum_comp f.σ f.a
          simpa [Fin.sum_univ_four] using hsum
        linarith [f.sum_eq, hperm]
      σ := f.σ⁻¹ }

instance : Group AffPerm4 where
  mul_assoc f g h := by
    refine AffPerm4.ext (funext fun i => ?_) (mul_assoc f.σ g.σ h.σ)
    change f.a i + g.a (f.σ⁻¹ i) + h.a ((f.σ * g.σ)⁻¹ i) =
      f.a i + (g.a (f.σ⁻¹ i) + h.a (g.σ⁻¹ (f.σ⁻¹ i)))
    simp [mul_inv_rev, add_assoc]
  one_mul f := by
    refine AffPerm4.ext (funext fun i => ?_) (one_mul f.σ)
    change 0 + f.a ((1 : Equiv.Perm (Fin 4))⁻¹ i) = f.a i
    simp
  mul_one f := by
    refine AffPerm4.ext (funext fun i => ?_) (mul_one f.σ)
    change f.a i + 0 = f.a i
    simp
  inv_mul_cancel f := by
    refine AffPerm4.ext (funext fun i => ?_) (inv_mul_cancel f.σ)
    change -f.a (f.σ i) + f.a ((f.σ⁻¹)⁻¹ i) = 0
    simp

@[simp] theorem one_a (i : Fin 4) : (1 : AffPerm4).a i = 0 := rfl
@[simp] theorem one_σ : (1 : AffPerm4).σ = 1 := rfl
@[simp] theorem mul_a (f g : AffPerm4) (i : Fin 4) :
    (f * g).a i = f.a i + g.a (f.σ⁻¹ i) := rfl
@[simp] theorem mul_σ (f g : AffPerm4) : (f * g).σ = f.σ * g.σ := rfl
@[simp] theorem inv_a (f : AffPerm4) (i : Fin 4) : (f⁻¹).a i = -f.a (f.σ i) := rfl
@[simp] theorem inv_σ (f : AffPerm4) : (f⁻¹).σ = f.σ⁻¹ := rfl

/-- Pure translation `t_a` by `a ∈ Q(A₃)`. -/
def trans (a : Fin 4 → ℤ) (ha : a 0 + a 1 + a 2 + a 3 = 0) : AffPerm4 :=
  ⟨a, ha, 1⟩

/-- Remainder in `Fin 4` of an integer modulo 4. -/
def mod4 (x : ℤ) : Fin 4 :=
  ⟨(x % 4).toNat, by omega⟩

theorem val_mod4 (x : ℤ) : ((mod4 x : Fin 4) : ℤ) = x % 4 := by
  dsimp [mod4]
  omega

theorem mod4_add_mul_four (r : Fin 4) (q : ℤ) : mod4 ((r : ℤ) + 4 * q) = r := by
  ext
  change (((r : ℤ) + 4 * q) % 4).toNat = (r : ℕ)
  omega

theorem div4_add_mul_four (r : Fin 4) (q : ℤ) : ((r : ℤ) + 4 * q) / 4 = q := by
  omega

theorem decomp_four (x : ℤ) : (mod4 x : ℤ) + 4 * (x / 4) = x := by
  rw [val_mod4]
  omega

/-- Action of `f : AffPerm4` on `ℤ`: `f(x) = σ(x mod 4) + 4 * (a(σ(x mod 4)) + x / 4)`. -/
def eval (f : AffPerm4) (x : ℤ) : ℤ :=
  (f.σ (mod4 x) : ℤ) + 4 * (f.a (f.σ (mod4 x)) + x / 4)

/-- Action of `f⁻¹` on `ℤ`: `f⁻¹(y) = σ⁻¹(y mod 4) + 4 * (y / 4 - a(y mod 4))`. -/
def evalInv (f : AffPerm4) (y : ℤ) : ℤ :=
  (f.σ⁻¹ (mod4 y) : ℤ) + 4 * (y / 4 - f.a (mod4 y))

theorem eval_add_mul_four (f : AffPerm4) (x k : ℤ) : f.eval (x + 4 * k) = f.eval x + 4 * k := by
  have hm : mod4 (x + 4 * k) = mod4 x := by
    ext; change ((x + 4 * k) % 4).toNat = (x % 4).toNat; omega
  have hd : (x + 4 * k) / 4 = x / 4 + k := by omega
  simp only [eval, hm, hd]
  ring

theorem evalInv_add_mul_four (f : AffPerm4) (y k : ℤ) :
    f.evalInv (y + 4 * k) = f.evalInv y + 4 * k := by
  have hm : mod4 (y + 4 * k) = mod4 y := by
    ext; change ((y + 4 * k) % 4).toNat = (y % 4).toNat; omega
  have hd : (y + 4 * k) / 4 = y / 4 + k := by omega
  simp only [evalInv, hm, hd]
  ring

theorem eval_one (x : ℤ) : (1 : AffPerm4).eval x = x := by
  simp only [eval, one_σ, one_a, Equiv.Perm.one_apply, zero_add]
  exact decomp_four x

theorem eval_mul (f g : AffPerm4) (x : ℤ) : (f * g).eval x = f.eval (g.eval x) := by
  simp only [eval, mul_σ, mul_a, Equiv.Perm.mul_apply, mod4_add_mul_four, div4_add_mul_four]
  have h1 : f.σ⁻¹ (f.σ (g.σ (mod4 x))) = g.σ (mod4 x) := by simp
  rw [h1]
  ring

theorem evalInv_eq_eval_inv (f : AffPerm4) (y : ℤ) : f.evalInv y = (f⁻¹).eval y := by
  simp only [evalInv, eval, inv_σ, inv_a]
  have h1 : f.σ (f.σ⁻¹ (mod4 y)) = mod4 y := by simp
  rw [h1]
  ring

theorem eval_evalInv (f : AffPerm4) (y : ℤ) : f.eval (f.evalInv y) = y := by
  rw [evalInv_eq_eval_inv, ← eval_mul, mul_inv_cancel, eval_one]

theorem evalInv_eval (f : AffPerm4) (x : ℤ) : f.evalInv (f.eval x) = x := by
  rw [evalInv_eq_eval_inv, ← eval_mul, inv_mul_cancel, eval_one]

theorem evalInv_fin (f : AffPerm4) (j : Fin 4) :
    f.evalInv (j : ℤ) = (f.σ⁻¹ j : ℤ) - 4 * f.a j := by
  have hm : mod4 (j : ℤ) = j := by ext; change ((j : ℤ) % 4).toNat = (j : ℕ); omega
  have hd : (j : ℤ) / 4 = 0 := by omega
  simp only [evalInv, hm, hd]
  ring

theorem eval_fin (f : AffPerm4) (j : Fin 4) :
    f.eval (j : ℤ) = (f.σ j : ℤ) + 4 * f.a (f.σ j) := by
  have hm : mod4 (j : ℤ) = j := by ext; change ((j : ℤ) % 4).toNat = (j : ℕ); omega
  have hd : (j : ℤ) / 4 = 0 := by omega
  simp only [eval, hm, hd]
  ring

theorem eval_injective (f : AffPerm4) : Function.Injective f.eval :=
  Function.LeftInverse.injective (evalInv_eval f)

theorem evalInv_injective (f : AffPerm4) : Function.Injective f.evalInv :=
  Function.LeftInverse.injective (eval_evalInv f)

theorem eval_mod4_ne (f : AffPerm4) {x y : ℤ} (h : x % 4 ≠ y % 4) :
    f.eval x % 4 ≠ f.eval y % 4 := by
  have hmod : mod4 x ≠ mod4 y := by
    intro heq
    have := congrArg (fun r : Fin 4 => (r : ℤ)) heq
    rw [val_mod4, val_mod4] at this
    exact h this
  have hσ : f.σ (mod4 x) ≠ f.σ (mod4 y) := f.σ.injective.ne hmod
  simp only [eval]
  intro heq
  apply hσ
  ext
  omega

theorem evalInv_mod4_ne (f : AffPerm4) {x y : ℤ} (h : x % 4 ≠ y % 4) :
    f.evalInv x % 4 ≠ f.evalInv y % 4 := by
  rw [evalInv_eq_eval_inv, evalInv_eq_eval_inv]
  exact eval_mod4_ne f⁻¹ h

/-- Simple reflection generators `gen i : AffPerm4` for `i : Fin 4`:
`gen 0` swaps `-1 ↔ 0` (mod 4), `gen 1` swaps `0 ↔ 1`, `gen 2` swaps `1 ↔ 2`, `gen 3` swaps `2 ↔ 3`. -/
def gen : Fin 4 → AffPerm4
  | 0 => ⟨![1, 0, 0, -1], by decide, Equiv.swap 0 3⟩
  | 1 => ⟨fun _ => 0, by simp, Equiv.swap 0 1⟩
  | 2 => ⟨fun _ => 0, by simp, Equiv.swap 1 2⟩
  | 3 => ⟨fun _ => 0, by simp, Equiv.swap 2 3⟩

theorem gen_coxeter (i j : Fin 4) : (gen i * gen j) ^ (A3TildeMatrix i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    refine AffPerm4.ext (funext fun k => ?_) (Equiv.ext fun k => ?_) <;>
    fin_cases k <;> decide

/-- The canonical Coxeter homomorphism `ρ : W(A₃~) →* AffPerm4`. -/
def rho : W3 →* AffPerm4 :=
  cs3.lift ⟨gen, gen_coxeter⟩

theorem rho_simple (i : Fin 4) : rho (cs3.simple i) = gen i :=
  cs3.lift_apply_simple _ i

/-! ### 4. Inverse homomorphism `ψ : AffPerm4 →* W(A₃~)` proving `ρ` is injective -/

private theorem s_sq (i : Fin 4) : cs3.simple i * cs3.simple i = 1 :=
  cs3.simple_mul_simple_self i

private theorem s_sq' (i : Fin 4) : A3TildeMatrix.simple i * A3TildeMatrix.simple i = 1 :=
  cs3.simple_mul_simple_self i

private theorem s_comm (i j : Fin 4) (h : A3TildeMatrix i j = 2) :
    cs3.simple i * cs3.simple j = cs3.simple j * cs3.simple i := by
  have hrel := cs3.simple_mul_simple_pow i j
  rw [h, pow_two] at hrel
  calc
    cs3.simple i * cs3.simple j
      = cs3.simple i * (cs3.simple j * (cs3.simple i * ((cs3.simple j * cs3.simple j) * cs3.simple i))) := by
          rw [s_sq j, one_mul, s_sq i, mul_one]
    _ = ((cs3.simple i * cs3.simple j) * (cs3.simple i * cs3.simple j)) * (cs3.simple j * cs3.simple i) := by
          simp only [mul_assoc]
    _ = cs3.simple j * cs3.simple i := by rw [hrel, one_mul]

private theorem s_braid (i j : Fin 4) (h : A3TildeMatrix i j = 3) :
    cs3.simple i * cs3.simple j * cs3.simple i =
      cs3.simple j * cs3.simple i * cs3.simple j := by
  have hrel := cs3.simple_mul_simple_pow i j
  rw [h, pow_three] at hrel
  have h1 : (cs3.simple i * cs3.simple j * cs3.simple i) *
      (cs3.simple j * cs3.simple i * cs3.simple j) = 1 := by
    simpa [mul_assoc] using hrel
  have h2 : (cs3.simple j * cs3.simple i * cs3.simple j) *
      (cs3.simple j * cs3.simple i * cs3.simple j) = 1 := by
    calc
      (cs3.simple j * cs3.simple i * cs3.simple j) * (cs3.simple j * cs3.simple i * cs3.simple j)
        = cs3.simple j * cs3.simple i * (cs3.simple j * cs3.simple j) * cs3.simple i * cs3.simple j := by
            simp only [mul_assoc]
      _ = cs3.simple j * (cs3.simple i * cs3.simple i) * cs3.simple j := by
            rw [s_sq j, mul_one]; simp only [mul_assoc]
      _ = cs3.simple j * cs3.simple j := by rw [s_sq i, mul_one]
      _ = 1 := s_sq j
  exact mul_right_cancel (h1.trans h2.symm)

private def isCommPair (a b : Fin 4) : Bool :=
  (a == 0 && b == 2) || (a == 2 && b == 0) || (a == 1 && b == 3) || (a == 3 && b == 1)

private def isBraidPair (a b : Fin 4) : Bool :=
  (a == 0 && b == 1) || (a == 1 && b == 0) ||
  (a == 1 && b == 2) || (a == 2 && b == 1) ||
  (a == 2 && b == 3) || (a == 3 && b == 2) ||
  (a == 3 && b == 0) || (a == 0 && b == 3)

private theorem s_comm_of_bool {a b : Fin 4} (h : isCommPair a b = true) :
    cs3.simple a * cs3.simple b = cs3.simple b * cs3.simple a := by
  apply s_comm
  fin_cases a <;> fin_cases b <;> simp_all [isCommPair, A3TildeMatrix]

private theorem s_braid_of_bool {a b : Fin 4} (h : isBraidPair a b = true) :
    cs3.simple a * cs3.simple b * cs3.simple a =
      cs3.simple b * cs3.simple a * cs3.simple b := by
  apply s_braid
  fin_cases a <;> fin_cases b <;> simp_all [isBraidPair, A3TildeMatrix]

/-- Elementary Coxeter-relation rewrite steps on words in `Fin 4`. -/
private inductive RewriteStep
  | cancel (k : ℕ)
  | insert (k : ℕ) (a : Fin 4)
  | comm (k : ℕ)
  | braid (k : ℕ)

private def applyStep : List (Fin 4) → RewriteStep → List (Fin 4)
  | w, .cancel k =>
    match w.drop k with
    | a :: b :: rest => if a == b then w.take k ++ rest else w
    | _ => w
  | w, .insert k a => w.take k ++ (a :: a :: w.drop k)
  | w, .comm k =>
    match w.drop k with
    | a :: b :: rest => if isCommPair a b then w.take k ++ (b :: a :: rest) else w
    | _ => w
  | w, .braid k =>
    match w.drop k with
    | a :: b :: c :: rest =>
      if a == c && isBraidPair a b then w.take k ++ (b :: a :: b :: rest) else w
    | _ => w

private def applySteps (w : List (Fin 4)) (steps : List RewriteStep) : List (Fin 4) :=
  steps.foldl applyStep w

private theorem wordProd_applyStep (w : List (Fin 4)) (st : RewriteStep) :
    cs3.wordProd (applyStep w st) = cs3.wordProd w := by
  cases st with
  | cancel k =>
    dsimp [applyStep]
    generalize hd : w.drop k = d
    cases d with
    | nil => rfl
    | cons a d₁ =>
      cases d₁ with
      | nil => rfl
      | cons b rest =>
        by_cases hab : (a == b) = true
        · simp only [hab, ↓reduceIte]
          have hEq : a = b := beq_iff_eq.mp hab
          subst hEq
          have hw : w = w.take k ++ (a :: a :: rest) := by
            rw [← hd, List.take_append_drop]
          conv_rhs => rw [hw]
          simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
          rw [← mul_assoc (cs3.simple a), s_sq a, one_mul]
        · simp [hab]
  | insert k a =>
    dsimp [applyStep]
    have hw : w = w.take k ++ w.drop k := (List.take_append_drop k w).symm
    conv_rhs => rw [hw]
    simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
    rw [← mul_assoc (cs3.simple a), s_sq a, one_mul]
  | comm k =>
    dsimp [applyStep]
    generalize hd : w.drop k = d
    cases d with
    | nil => rfl
    | cons a d₁ =>
      cases d₁ with
      | nil => rfl
      | cons b rest =>
        by_cases hc : isCommPair a b = true
        · simp only [hc, ↓reduceIte]
          have hw : w = w.take k ++ (a :: b :: rest) := by
            rw [← hd, List.take_append_drop]
          conv_rhs => rw [hw]
          simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
          have hcom := s_comm_of_bool hc
          calc
            cs3.wordProd (w.take k) * (cs3.simple b * (cs3.simple a * cs3.wordProd rest))
              = cs3.wordProd (w.take k) * ((cs3.simple b * cs3.simple a) * cs3.wordProd rest) := by
                  simp only [mul_assoc]
            _ = cs3.wordProd (w.take k) * ((cs3.simple a * cs3.simple b) * cs3.wordProd rest) := by
                  rw [hcom]
            _ = cs3.wordProd (w.take k) * (cs3.simple a * (cs3.simple b * cs3.wordProd rest)) := by
                  simp only [mul_assoc]
        · simp [hc]
  | braid k =>
    dsimp [applyStep]
    generalize hd : w.drop k = d
    cases d with
    | nil => rfl
    | cons a d₁ =>
      cases d₁ with
      | nil => rfl
      | cons b d₂ =>
        cases d₂ with
        | nil => rfl
        | cons c rest =>
          by_cases hb : ((a == c) && isBraidPair a b) = true
          · simp only [hb, ↓reduceIte]
            have hac : a = c := beq_iff_eq.mp (Bool.and_eq_true_iff.mp hb).1
            have hbr : isBraidPair a b = true := (Bool.and_eq_true_iff.mp hb).2
            subst hac
            have hw : w = w.take k ++ (a :: b :: a :: rest) := by
              rw [← hd, List.take_append_drop]
            conv_rhs => rw [hw]
            simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
            have hrel := s_braid_of_bool hbr
            calc
              cs3.wordProd (w.take k) * (cs3.simple b * (cs3.simple a * (cs3.simple b * cs3.wordProd rest)))
                = cs3.wordProd (w.take k) * ((cs3.simple b * cs3.simple a * cs3.simple b) * cs3.wordProd rest) := by
                    simp only [mul_assoc]
              _ = cs3.wordProd (w.take k) * ((cs3.simple a * cs3.simple b * cs3.simple a) * cs3.wordProd rest) := by
                    rw [hrel]
              _ = cs3.wordProd (w.take k) * (cs3.simple a * (cs3.simple b * (cs3.simple a * cs3.wordProd rest))) := by
                    simp only [mul_assoc]
          · simp [hb]

private theorem wordProd_applySteps (w : List (Fin 4)) (steps : List RewriteStep) :
    cs3.wordProd (applySteps w steps) = cs3.wordProd w := by
  induction steps generalizing w with
  | nil => rfl
  | cons st rest ih =>
    change cs3.wordProd (applySteps (applyStep w st) rest) = cs3.wordProd w
    rw [ih (applyStep w st), wordProd_applyStep]

private theorem wordProd_eq_of_steps {w₁ w₂ : List (Fin 4)} (steps : List RewriteStep)
    (h : applySteps w₁ steps = w₂) : cs3.wordProd w₁ = cs3.wordProd w₂ := by
  rw [← h, wordProd_applySteps]

private def wT1 : List (Fin 4) := [0, 2, 3, 0, 2, 1]
private def wT2 : List (Fin 4) := [1, 0, 3, 0, 1, 2]
private def wT3 : List (Fin 4) := [0, 1, 2, 1, 0, 3]
private def wTth : List (Fin 4) := [0, 1, 2, 3, 2, 1]

private def T1 : W3 := cs3.wordProd wT1
private def T2 : W3 := cs3.wordProd wT2
private def T3 : W3 := cs3.wordProd wT3
private def Tth : W3 := cs3.wordProd wTth

private theorem inv_wordProd_eq (w : List (Fin 4)) :
    (cs3.wordProd w)⁻¹ = cs3.wordProd w.reverse := by
  exact (cs3.wordProd_reverse w).symm

private theorem wordProd_conj_simple (i : Fin 4) (w : List (Fin 4)) :
    cs3.wordProd ([i] ++ w ++ [i]) = cs3.simple i * cs3.wordProd w * cs3.simple i := by
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
      CoxeterSystem.wordProd_singleton]

private theorem s1_T1_s1 : cs3.simple 1 * T1 * cs3.simple 1 = T1⁻¹ := by
  have h : cs3.wordProd ([1] ++ wT1 ++ [1]) = cs3.wordProd wT1.reverse :=
    wordProd_eq_of_steps [.cancel 6, .comm 4, .comm 1] rfl
  rw [wordProd_conj_simple, ← inv_wordProd_eq] at h
  exact h

private theorem s1_T3_s1 : cs3.simple 1 * T3 * cs3.simple 1 = T3 := by
  have h : cs3.wordProd ([1] ++ wT3 ++ [1]) = cs3.wordProd wT3 :=
    wordProd_eq_of_steps [.comm 6, .braid 0, .comm 2, .braid 3, .cancel 5] rfl
  rw [wordProd_conj_simple] at h
  exact h

private theorem s2_T2_s2 : cs3.simple 2 * T2 * cs3.simple 2 = T2⁻¹ := by
  have h : cs3.wordProd ([2] ++ wT2 ++ [2]) = cs3.wordProd wT2.reverse :=
    wordProd_eq_of_steps [.cancel 6] rfl
  rw [wordProd_conj_simple, ← inv_wordProd_eq] at h
  exact h

private theorem s3_T1_s3 : cs3.simple 3 * T1 * cs3.simple 3 = T1 := by
  have h : cs3.wordProd ([3] ++ wT1 ++ [3]) = cs3.wordProd wT1 :=
    wordProd_eq_of_steps [.comm 1, .comm 6, .braid 2, .braid 0, .comm 2, .braid 3, .cancel 5, .braid 1, .comm 0] rfl
  rw [wordProd_conj_simple] at h
  exact h

private theorem s3_T3_s3 : cs3.simple 3 * T3 * cs3.simple 3 = T3⁻¹ := by
  have h : cs3.wordProd ([3] ++ wT3 ++ [3]) = cs3.wordProd wT3.reverse :=
    wordProd_eq_of_steps [.cancel 6] rfl
  rw [wordProd_conj_simple, ← inv_wordProd_eq] at h
  exact h

private theorem s1_T2_s1 : cs3.simple 1 * T2 * cs3.simple 1 = T1 * T2 := by
  have h : cs3.wordProd ([1] ++ wT2 ++ [1]) = cs3.wordProd (wT1 ++ wT2) :=
    wordProd_eq_of_steps [.cancel 0, .braid 3, .comm 2, .insert 3 3, .braid 1, .insert 4 0, .comm 3, .insert 5 1] rfl
  rw [wordProd_conj_simple, CoxeterSystem.wordProd_append] at h
  exact h

private theorem s2_T1_s2 : cs3.simple 2 * T1 * cs3.simple 2 = T1 * T2 := by
  have h : cs3.wordProd ([2] ++ wT1 ++ [2]) = cs3.wordProd (wT1 ++ wT2) :=
    wordProd_eq_of_steps [.comm 0, .comm 4, .braid 2, .insert 4 0, .comm 3, .insert 5 1] rfl
  rw [wordProd_conj_simple, CoxeterSystem.wordProd_append] at h
  exact h

private theorem s2_T3_s2 : cs3.simple 2 * T3 * cs3.simple 2 = T2 * T3 := by
  have h : cs3.wordProd ([2] ++ wT3 ++ [2]) = cs3.wordProd (wT2 ++ wT3) :=
    wordProd_eq_of_steps [.comm 0, .braid 1, .cancel 3, .comm 2, .braid 0, .braid 3, .comm 2, .insert 5 0, .comm 4, .insert 6 1, .insert 7 2, .braid 5, .braid 3, .comm 5] rfl
  rw [wordProd_conj_simple, CoxeterSystem.wordProd_append] at h
  exact h

private theorem s3_T2_s3 : cs3.simple 3 * T2 * cs3.simple 3 = T2 * T3 := by
  have h : cs3.wordProd ([3] ++ wT2 ++ [3]) = cs3.wordProd (wT2 ++ wT3) :=
    wordProd_eq_of_steps [.comm 0, .braid 1, .insert 6 0, .braid 4, .comm 7, .insert 8 1, .braid 6, .comm 5] rfl
  rw [wordProd_conj_simple, CoxeterSystem.wordProd_append] at h
  exact h

private theorem T1_T2_comm : Commute T1 T2 := by
  have h : cs3.wordProd (wT1 ++ wT2) = cs3.wordProd (wT2 ++ wT1) :=
    wordProd_eq_of_steps [.cancel 5, .comm 3, .cancel 4, .braid 1, .cancel 3, .comm 2, .braid 0, .braid 3, .comm 2, .insert 4 0, .insert 5 3, .braid 3, .braid 1, .comm 3, .comm 0, .braid 1, .insert 6 2, .comm 5] rfl
  simpa [Commute, SemiconjBy, T1, T2, CoxeterSystem.wordProd_append] using h

private theorem T1_T3_comm : Commute T1 T3 := by
  have h : cs3.wordProd (wT1 ++ wT3) = cs3.wordProd (wT3 ++ wT1) :=
    wordProd_eq_of_steps [.comm 3, .braid 4, .cancel 6, .comm 5, .braid 3, .comm 2, .braid 5, .cancel 7, .comm 6, .insert 7 0, .braid 5, .braid 3, .comm 5, .insert 8 2, .braid 6, .braid 4, .braid 1, .comm 9] rfl
  simpa [Commute, SemiconjBy, T1, T3, CoxeterSystem.wordProd_append] using h

private theorem T2_T3_comm : Commute T2 T3 := by
  have h : cs3.wordProd (wT2 ++ wT3) = cs3.wordProd (wT3 ++ wT2) :=
    wordProd_eq_of_steps [.comm 5, .braid 3, .comm 2, .braid 0, .braid 5, .cancel 7, .cancel 6, .comm 4, .cancel 5, .braid 3, .comm 2, .insert 5 1, .comm 4, .insert 6 0, .insert 7 3, .braid 5, .braid 3, .comm 5] rfl
  simpa [Commute, SemiconjBy, T2, T3, CoxeterSystem.wordProd_append] using h

private theorem T1_T2_T3_eq_Tth : T1 * T2 * T3 = Tth := by
  have h : cs3.wordProd (wT1 ++ wT2 ++ wT3) = cs3.wordProd wTth :=
    wordProd_eq_of_steps [.cancel 5, .comm 3, .cancel 4, .comm 7, .braid 1, .cancel 3, .braid 3, .braid 5, .cancel 7, .cancel 6, .comm 4, .cancel 5, .braid 2, .comm 4, .comm 1, .braid 2] rfl
  simpa [T1, T2, T3, Tth, CoxeterSystem.wordProd_append, mul_assoc] using h

/-! Embedding `S₄ →* W(A₃~)` via the 24-element coset normal form `a * b * c`. -/

private def cWord : Fin 4 → List (Fin 4)
  | 0 => [3, 2, 1]
  | 1 => [3, 2]
  | 2 => [3]
  | 3 => []

private def bWord : Fin 3 → List (Fin 4)
  | 0 => [2, 1]
  | 1 => [2]
  | 2 => []

private def aWord : Fin 2 → List (Fin 4)
  | 0 => [1]
  | 1 => []

private def swapOf : Fin 4 → Equiv.Perm (Fin 4)
  | 0 => 1
  | 1 => Equiv.swap 0 1
  | 2 => Equiv.swap 1 2
  | 3 => Equiv.swap 2 3

private def permOfWord : List (Fin 4) → Equiv.Perm (Fin 4)
  | [] => 1
  | i :: rest => swapOf i * permOfWord rest

private theorem permOfWord_append (w₁ w₂ : List (Fin 4)) :
    permOfWord (w₁ ++ w₂) = permOfWord w₁ * permOfWord w₂ := by
  induction w₁ with
  | nil => simp [permOfWord]
  | cons i rest ih => simp [permOfWord, ih, mul_assoc]

private def s4Word (σ : Equiv.Perm (Fin 4)) : List (Fin 4) :=
  let k3 : Fin 4 := σ⁻¹ 3
  let σ₁ : Equiv.Perm (Fin 4) := σ * (permOfWord (cWord k3))⁻¹
  let k2 : Fin 3 := ⟨(σ₁⁻¹ 2 : ℕ) % 3, Nat.mod_lt _ (by decide)⟩
  let σ₂ : Equiv.Perm (Fin 4) := σ₁ * (permOfWord (bWord k2))⁻¹
  let k1 : Fin 2 := ⟨(σ₂⁻¹ 1 : ℕ) % 2, Nat.mod_lt _ (by decide)⟩
  aWord k1 ++ bWord k2 ++ cWord k3

private theorem permOfWord_s4Word (σ : Equiv.Perm (Fin 4)) : permOfWord (s4Word σ) = σ := by
  revert σ
  decide

private def nfWord (k1 : Fin 2) (k2 : Fin 3) (k3 : Fin 4) : List (Fin 4) :=
  aWord k1 ++ bWord k2 ++ cWord k3

private def s4Coords (σ : Equiv.Perm (Fin 4)) : Fin 2 × Fin 3 × Fin 4 :=
  let k3 : Fin 4 := σ⁻¹ 3
  let σ₁ : Equiv.Perm (Fin 4) := σ * (permOfWord (cWord k3))⁻¹
  let k2 : Fin 3 := ⟨(σ₁⁻¹ 2 : ℕ) % 3, Nat.mod_lt _ (by decide)⟩
  let σ₂ : Equiv.Perm (Fin 4) := σ₁ * (permOfWord (bWord k2))⁻¹
  let k1 : Fin 2 := ⟨(σ₂⁻¹ 1 : ℕ) % 2, Nat.mod_lt _ (by decide)⟩
  (k1, k2, k3)

private theorem s4Word_eq_nfWord (σ : Equiv.Perm (Fin 4)) :
    s4Word σ = nfWord (s4Coords σ).1 (s4Coords σ).2.1 (s4Coords σ).2.2 := rfl

private theorem s4Coords_permOfWord (k1 : Fin 2) (k2 : Fin 3) (k3 : Fin 4) :
    s4Coords (permOfWord (nfWord k1 k2 k3)) = (k1, k2, k3) := by
  fin_cases k1 <;> fin_cases k2 <;> fin_cases k3 <;> decide

private theorem cStep (k3 : Fin 4) (i : Fin 4) (hi : i ≠ 0) :
    ∃ (j : Option (Fin 4)) (k3' : Fin 4),
      (∀ x : Fin 4, j = some x → x = 1 ∨ x = 2) ∧
      permOfWord (cWord k3) * swapOf i = permOfWord j.toList * permOfWord (cWord k3') ∧
      cs3.wordProd (cWord k3) * cs3.simple i =
        cs3.wordProd j.toList * cs3.wordProd (cWord k3') := by
  have h13 : cs3.simple 1 * cs3.simple 3 = cs3.simple 3 * cs3.simple 1 := s_comm 1 3 (by decide)
  have h232 : cs3.simple 2 * cs3.simple 3 * cs3.simple 2 =
      cs3.simple 3 * cs3.simple 2 * cs3.simple 3 := s_braid 2 3 (by decide)
  have h121 : cs3.simple 1 * cs3.simple 2 * cs3.simple 1 =
      cs3.simple 2 * cs3.simple 1 * cs3.simple 2 := s_braid 1 2 (by decide)
  fin_cases i
  · exact absurd rfl hi
  · fin_cases k3
    · refine ⟨none, 1, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons, mul_assoc, s_sq']
    · refine ⟨none, 0, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons, mul_assoc]
    · refine ⟨some 1, 2, by simp, by decide, ?_⟩
      have h13' : A3TildeMatrix.simple 3 * A3TildeMatrix.simple 1 =
          A3TildeMatrix.simple 1 * A3TildeMatrix.simple 3 := h13.symm
      simp [cWord, CoxeterSystem.wordProd_cons, h13']
    · refine ⟨some 1, 3, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons]
  · fin_cases k3
    · refine ⟨some 1, 0, by simp, by decide, ?_⟩
      simp only [cWord, Option.toList_some, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one]
      calc
        cs3.simple 3 * (cs3.simple 2 * cs3.simple 1) * cs3.simple 2
          = cs3.simple 3 * (cs3.simple 2 * cs3.simple 1 * cs3.simple 2) := by simp only [mul_assoc]
        _ = cs3.simple 3 * (cs3.simple 1 * cs3.simple 2 * cs3.simple 1) := by rw [← h121]
        _ = (cs3.simple 3 * cs3.simple 1) * (cs3.simple 2 * cs3.simple 1) := by simp only [mul_assoc]
        _ = (cs3.simple 1 * cs3.simple 3) * (cs3.simple 2 * cs3.simple 1) := by rw [h13]
        _ = cs3.simple 1 * (cs3.simple 3 * (cs3.simple 2 * cs3.simple 1)) := by simp only [mul_assoc]
    · refine ⟨none, 2, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons, mul_assoc, s_sq']
    · refine ⟨none, 1, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons]
    · refine ⟨some 2, 3, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons]
  · fin_cases k3
    · refine ⟨some 2, 0, by simp, by decide, ?_⟩
      simp only [cWord, Option.toList_some, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one]
      calc
        cs3.simple 3 * (cs3.simple 2 * cs3.simple 1) * cs3.simple 3
          = cs3.simple 3 * cs3.simple 2 * (cs3.simple 1 * cs3.simple 3) := by simp only [mul_assoc]
        _ = cs3.simple 3 * cs3.simple 2 * (cs3.simple 3 * cs3.simple 1) := by rw [h13]
        _ = (cs3.simple 3 * cs3.simple 2 * cs3.simple 3) * cs3.simple 1 := by simp only [mul_assoc]
        _ = (cs3.simple 2 * cs3.simple 3 * cs3.simple 2) * cs3.simple 1 := by rw [← h232]
        _ = cs3.simple 2 * (cs3.simple 3 * (cs3.simple 2 * cs3.simple 1)) := by simp only [mul_assoc]
    · refine ⟨some 2, 1, by simp, by decide, ?_⟩
      simp only [cWord, Option.toList_some, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one]
      simpa [mul_assoc] using h232.symm
    · refine ⟨none, 3, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons, s_sq']
    · refine ⟨none, 2, by simp, by decide, ?_⟩
      simp [cWord, CoxeterSystem.wordProd_cons]

private theorem bStep (k2 : Fin 3) (j : Fin 4) (hj : j = 1 ∨ j = 2) :
    ∃ (l : Option (Fin 4)) (k2' : Fin 3),
      (∀ x : Fin 4, l = some x → x = 1) ∧
      permOfWord (bWord k2) * swapOf j = permOfWord l.toList * permOfWord (bWord k2') ∧
      cs3.wordProd (bWord k2) * cs3.simple j =
        cs3.wordProd l.toList * cs3.wordProd (bWord k2') := by
  have h121 : cs3.simple 1 * cs3.simple 2 * cs3.simple 1 =
      cs3.simple 2 * cs3.simple 1 * cs3.simple 2 := s_braid 1 2 (by decide)
  rcases hj with rfl | rfl
  · fin_cases k2
    · refine ⟨none, 1, by simp, by decide, ?_⟩
      simp [bWord, CoxeterSystem.wordProd_cons, mul_assoc, s_sq']
    · refine ⟨none, 0, by simp, by decide, ?_⟩
      simp [bWord, CoxeterSystem.wordProd_cons]
    · refine ⟨some 1, 2, by simp, by decide, ?_⟩
      simp [bWord, CoxeterSystem.wordProd_cons]
  · fin_cases k2
    · refine ⟨some 1, 0, by simp, by decide, ?_⟩
      simp only [bWord, Option.toList_some, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one]
      simpa [mul_assoc] using h121.symm
    · refine ⟨none, 2, by simp, by decide, ?_⟩
      simp [bWord, CoxeterSystem.wordProd_cons, s_sq']
    · refine ⟨none, 1, by simp, by decide, ?_⟩
      simp [bWord, CoxeterSystem.wordProd_cons]

private theorem aStep (k1 : Fin 2) :
    ∃ k1' : Fin 2,
      permOfWord (aWord k1) * swapOf 1 = permOfWord (aWord k1') ∧
      cs3.wordProd (aWord k1) * cs3.simple 1 = cs3.wordProd (aWord k1') := by
  fin_cases k1
  · exact ⟨1, by decide, by simp [aWord, CoxeterSystem.wordProd_cons, s_sq']⟩
  · exact ⟨0, by decide, by simp [aWord, CoxeterSystem.wordProd_cons]⟩

private theorem s4Word_mul_gen (σ : Equiv.Perm (Fin 4)) (i : Fin 4) (hi : i ≠ 0) :
    cs3.wordProd (s4Word (σ * swapOf i)) = cs3.wordProd (s4Word σ) * cs3.simple i := by
  rcases hco : s4Coords σ with ⟨k1, k2, k3⟩
  have hσ : σ = permOfWord (nfWord k1 k2 k3) := by
    rw [← permOfWord_s4Word σ, s4Word_eq_nfWord, hco]
  have hs4 : s4Word σ = nfWord k1 k2 k3 := by rw [s4Word_eq_nfWord, hco]
  rw [hs4]
  obtain ⟨j, k3', hj_ok, hj_perm, hj_w⟩ := cStep k3 i hi
  cases j with
  | none =>
    have hprod_perm : σ * swapOf i = permOfWord (nfWord k1 k2 k3') := by
      rw [hσ]
      simp only [nfWord, permOfWord_append, mul_assoc]
      rw [hj_perm]
      simp [permOfWord]
    have hco' : s4Coords (σ * swapOf i) = (k1, k2, k3') := by
      rw [hprod_perm, s4Coords_permOfWord]
    rw [s4Word_eq_nfWord, hco']
    simp only [nfWord, CoxeterSystem.wordProd_append, mul_assoc]
    rw [hj_w]
    simp
  | some j =>
    obtain ⟨l, k2', hl_ok, hl_perm, hl_w⟩ := bStep k2 j (hj_ok j rfl)
    cases l with
    | none =>
      have hprod_perm : σ * swapOf i = permOfWord (nfWord k1 k2' k3') := by
        rw [hσ]
        simp only [nfWord, permOfWord_append, mul_assoc]
        rw [hj_perm]
        simp only [Option.toList_some, permOfWord, mul_one, ← mul_assoc]
        rw [mul_assoc (permOfWord (aWord k1)), hl_perm]
        simp [permOfWord, mul_assoc]
      have hco' : s4Coords (σ * swapOf i) = (k1, k2', k3') := by
        rw [hprod_perm, s4Coords_permOfWord]
      rw [s4Word_eq_nfWord, hco']
      simp only [nfWord, CoxeterSystem.wordProd_append, mul_assoc]
      rw [hj_w]
      simp only [Option.toList_some, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one]
      rw [← mul_assoc (cs3.wordProd (bWord k2)), hl_w]
      simp
    | some l =>
      have hl1 : l = 1 := hl_ok l rfl
      subst hl1
      obtain ⟨k1', ha_perm, ha_w⟩ := aStep k1
      have hprod_perm : σ * swapOf i = permOfWord (nfWord k1' k2' k3') := by
        rw [hσ]
        simp only [nfWord, permOfWord_append, mul_assoc]
        rw [hj_perm]
        simp only [Option.toList_some, permOfWord, mul_one, ← mul_assoc]
        rw [mul_assoc (permOfWord (aWord k1)), hl_perm]
        simp only [Option.toList_some, permOfWord, mul_one]
        rw [← mul_assoc (permOfWord (aWord k1))]
        rw [ha_perm]
      have hco' : s4Coords (σ * swapOf i) = (k1', k2', k3') := by
        rw [hprod_perm, s4Coords_permOfWord]
      rw [s4Word_eq_nfWord, hco']
      simp only [nfWord, CoxeterSystem.wordProd_append, mul_assoc]
      rw [hj_w]
      simp only [Option.toList_some, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one]
      rw [← mul_assoc (cs3.wordProd (bWord k2)), hl_w]
      simp only [Option.toList_some, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil,
        mul_one]
      rw [← mul_assoc (cs3.wordProd (aWord k1)), ← mul_assoc (cs3.wordProd (aWord k1)), ha_w]
      simp [mul_assoc]

private theorem s4Word_nonzero (σ : Equiv.Perm (Fin 4)) :
    ∀ i ∈ s4Word σ, i ≠ 0 := by
  revert σ
  decide

private theorem s4Word_mul_word (σ : Equiv.Perm (Fin 4)) (w : List (Fin 4))
    (hw : ∀ i ∈ w, i ≠ 0) :
    cs3.wordProd (s4Word (σ * permOfWord w)) = cs3.wordProd (s4Word σ) * cs3.wordProd w := by
  induction w generalizing σ with
  | nil => simp [permOfWord]
  | cons i rest ih =>
    have hi : i ≠ 0 := hw i (by simp)
    have hrest : ∀ j ∈ rest, j ≠ 0 := fun j hj => hw j (by simp [hj])
    simp only [permOfWord, CoxeterSystem.wordProd_cons, ← mul_assoc]
    rw [ih (σ * swapOf i) hrest, s4Word_mul_gen σ i hi]

/-- Group homomorphism `φS4 : S₄ →* W(A₃~)` sending `(0 1) ↦ s₁`, `(1 2) ↦ s₂`, `(2 3) ↦ s₃`. -/
private def phiS4 : Equiv.Perm (Fin 4) →* W3 where
  toFun σ := cs3.wordProd (s4Word σ)
  map_one' := by
    have h : s4Word 1 = [] := by decide
    simp [h]
  map_mul' σ τ := by
    have hτ := permOfWord_s4Word τ
    have hnz := s4Word_nonzero τ
    conv_lhs => rw [← hτ]
    exact s4Word_mul_word σ (s4Word τ) hnz

private theorem phiS4_swap (i : Fin 4) (hi : i ≠ 0) : phiS4 (swapOf i) = cs3.simple i := by
  have h := s4Word_mul_gen 1 i hi
  have h1 : s4Word 1 = [] := by decide
  simpa [phiS4, h1] using h

/-- Translation homomorphism `ψTrans : Q(A₃) → W(A₃~)` defined on `a : Fin 4 → ℤ`
by `T₁^(a 0) * T₂^(a 0 + a 1) * T₃^(a 0 + a 1 + a 2)`. -/
private def psiTrans (a : Fin 4 → ℤ) : W3 :=
  T1 ^ (a 0) * T2 ^ (a 0 + a 1) * T3 ^ (a 0 + a 1 + a 2)

private theorem psiTrans_zero : psiTrans (fun _ => 0) = 1 := by
  simp [psiTrans]

private theorem psiTrans_add (a b : Fin 4 → ℤ) :
    psiTrans (fun i => a i + b i) = psiTrans a * psiTrans b := by
  have h12 : Commute (T1 ^ (b 0)) (T2 ^ (a 0 + a 1)) :=
    (T1_T2_comm.zpow_left _).zpow_right _
  have h13 : Commute (T1 ^ (b 0)) (T3 ^ (a 0 + a 1 + a 2)) :=
    (T1_T3_comm.zpow_left _).zpow_right _
  have h23 : Commute (T2 ^ (b 0 + b 1)) (T3 ^ (a 0 + a 1 + a 2)) :=
    (T2_T3_comm.zpow_left _).zpow_right _
  have e1 : a 0 + b 0 = a 0 + b 0 := rfl
  have e2 : (a 0 + b 0) + (a 1 + b 1) = (a 0 + a 1) + (b 0 + b 1) := by ring
  have e3 : (a 0 + b 0) + (a 1 + b 1) + (a 2 + b 2) =
      (a 0 + a 1 + a 2) + (b 0 + b 1 + b 2) := by ring
  dsimp only [psiTrans]
  rw [e3, e2, zpow_add T1 (a 0) (b 0), zpow_add T2 (a 0 + a 1) (b 0 + b 1),
      zpow_add T3 (a 0 + a 1 + a 2) (b 0 + b 1 + b 2)]
  calc
    T1 ^ a 0 * T1 ^ b 0 * (T2 ^ (a 0 + a 1) * T2 ^ (b 0 + b 1)) *
        (T3 ^ (a 0 + a 1 + a 2) * T3 ^ (b 0 + b 1 + b 2))
      = T1 ^ a 0 * (T1 ^ b 0 * T2 ^ (a 0 + a 1)) * T2 ^ (b 0 + b 1) *
          T3 ^ (a 0 + a 1 + a 2) * T3 ^ (b 0 + b 1 + b 2) := by simp only [mul_assoc]
    _ = T1 ^ a 0 * (T2 ^ (a 0 + a 1) * T1 ^ b 0) * (T2 ^ (b 0 + b 1) *
          T3 ^ (a 0 + a 1 + a 2)) * T3 ^ (b 0 + b 1 + b 2) := by
          rw [h12.eq]; simp only [mul_assoc]
    _ = T1 ^ a 0 * T2 ^ (a 0 + a 1) * (T1 ^ b 0 * T3 ^ (a 0 + a 1 + a 2)) *
          T2 ^ (b 0 + b 1) * T3 ^ (b 0 + b 1 + b 2) := by
          rw [h23.eq]; simp only [mul_assoc]
    _ = T1 ^ a 0 * T2 ^ (a 0 + a 1) * (T3 ^ (a 0 + a 1 + a 2) * T1 ^ b 0) *
          T2 ^ (b 0 + b 1) * T3 ^ (b 0 + b 1 + b 2) := by
          rw [h13.eq]
    _ = T1 ^ a 0 * T2 ^ (a 0 + a 1) * T3 ^ (a 0 + a 1 + a 2) *
          (T1 ^ b 0 * T2 ^ (b 0 + b 1) * T3 ^ (b 0 + b 1 + b 2)) := by simp only [mul_assoc]

private theorem conj_zpow {G : Type*} [Group G] (g x : G) (n : ℤ) :
    g * x ^ n * g⁻¹ = (g * x * g⁻¹) ^ n := by
  simp

private theorem conj_simple_zpow (i : Fin 4) (x : W3) (n : ℤ) :
    cs3.simple i * x ^ n * cs3.simple i = (cs3.simple i * x * cs3.simple i) ^ n := by
  have hinv : (cs3.simple i)⁻¹ = cs3.simple i := cs3.inv_simple i
  have h := conj_zpow (cs3.simple i) x n
  rwa [hinv] at h

private theorem conj_psiTrans_simple (i : Fin 4) (hi : i ≠ 0) (a : Fin 4 → ℤ)
    (ha : a 0 + a 1 + a 2 + a 3 = 0) :
    cs3.simple i * psiTrans a * cs3.simple i = psiTrans (fun k => a (swapOf i k)) := by
  have split3 : ∀ x y z : W3,
      cs3.simple i * (x * y * z) * cs3.simple i =
        (cs3.simple i * x * cs3.simple i) *
        (cs3.simple i * y * cs3.simple i) *
        (cs3.simple i * z * cs3.simple i) := by
    intro x y z
    simp only [mul_assoc]
    rw [← mul_assoc (cs3.simple i) (cs3.simple i), s_sq, one_mul]
    rw [← mul_assoc (cs3.simple i) (cs3.simple i), s_sq, one_mul]
  match i with
  | 0 => exact absurd rfl hi
  | 1 =>
    have h12 : Commute T1 T2 := T1_T2_comm
    simp only [psiTrans]
    rw [split3, conj_simple_zpow, conj_simple_zpow, conj_simple_zpow,
        s1_T1_s1, s1_T2_s1, s1_T3_s1, inv_zpow, ← zpow_neg, h12.mul_zpow]
    have hswap0 : swapOf 1 0 = 1 := by decide
    have hswap1 : swapOf 1 1 = 0 := by decide
    have hswap2 : swapOf 1 2 = 2 := by decide
    rw [hswap0, hswap1, hswap2]
    have e1 : -a 0 + (a 0 + a 1) = a 1 := by ring
    have e2 : a 0 + a 1 = a 1 + a 0 := by ring
    rw [← mul_assoc, ← zpow_add, e1, e2]
  | 2 =>
    have h12 : Commute T1 T2 := T1_T2_comm
    have h23 : Commute T2 T3 := T2_T3_comm
    have h13 : Commute T1 T3 := T1_T3_comm
    simp only [psiTrans]
    rw [split3, conj_simple_zpow, conj_simple_zpow, conj_simple_zpow,
        s2_T1_s2, s2_T2_s2, s2_T3_s2, inv_zpow, ← zpow_neg, h12.mul_zpow, h23.mul_zpow]
    have hswap0 : swapOf 2 0 = 0 := by decide
    have hswap1 : swapOf 2 1 = 2 := by decide
    have hswap2 : swapOf 2 2 = 1 := by decide
    rw [hswap0, hswap1, hswap2]
    have hcomm : Commute (T2 ^ (a 0 + a 1 + a 2)) (T2 ^ (-(a 0 + a 1))) := Commute.zpow_zpow_self _ _ _
    have e2 : a 0 + -(a 0 + a 1) + (a 0 + a 1 + a 2) = a 0 + a 2 := by ring
    have e3 : a 0 + a 1 + a 2 = a 0 + a 2 + a 1 := by ring
    calc
      T1 ^ a 0 * T2 ^ a 0 * T2 ^ (-(a 0 + a 1)) * (T2 ^ (a 0 + a 1 + a 2) * T3 ^ (a 0 + a 1 + a 2))
        = T1 ^ a 0 * (T2 ^ a 0 * T2 ^ (-(a 0 + a 1)) * T2 ^ (a 0 + a 1 + a 2)) * T3 ^ (a 0 + a 1 + a 2) := by
            simp only [mul_assoc]
      _ = T1 ^ a 0 * T2 ^ (a 0 + -(a 0 + a 1) + (a 0 + a 1 + a 2)) * T3 ^ (a 0 + a 1 + a 2) := by
            rw [← zpow_add, ← zpow_add]
      _ = T1 ^ a 0 * T2 ^ (a 0 + a 2) * T3 ^ (a 0 + a 2 + a 1) := by rw [e2, e3]
  | 3 =>
    have h23 : Commute T2 T3 := T2_T3_comm
    simp only [psiTrans]
    rw [split3, conj_simple_zpow, conj_simple_zpow, conj_simple_zpow,
        s3_T1_s3, s3_T2_s3, s3_T3_s3, inv_zpow, ← zpow_neg, h23.mul_zpow]
    have hswap0 : swapOf 3 0 = 0 := by decide
    have hswap1 : swapOf 3 1 = 1 := by decide
    have hswap2 : swapOf 3 2 = 3 := by decide
    rw [hswap0, hswap1, hswap2]
    have e3 : (a 0 + a 1) + -(a 0 + a 1 + a 2) = a 0 + a 1 + a 3 := by linarith
    calc
      T1 ^ a 0 * (T2 ^ (a 0 + a 1) * T3 ^ (a 0 + a 1)) * T3 ^ (-(a 0 + a 1 + a 2))
        = T1 ^ a 0 * T2 ^ (a 0 + a 1) * (T3 ^ (a 0 + a 1) * T3 ^ (-(a 0 + a 1 + a 2))) := by
            simp only [mul_assoc]
      _ = T1 ^ a 0 * T2 ^ (a 0 + a 1) * T3 ^ ((a 0 + a 1) + -(a 0 + a 1 + a 2)) := by
            rw [← zpow_add]
      _ = T1 ^ a 0 * T2 ^ (a 0 + a 1) * T3 ^ (a 0 + a 1 + a 3) := by rw [e3]

private theorem conj_psiTrans_perm (σ : Equiv.Perm (Fin 4)) (a : Fin 4 → ℤ)
    (ha : a 0 + a 1 + a 2 + a 3 = 0) :
    phiS4 σ * psiTrans a * (phiS4 σ)⁻¹ = psiTrans (fun k => a (σ⁻¹ k)) := by
  -- Prove by induction on `w = s4Word σ`!
  have hword : ∀ (w : List (Fin 4)), (∀ i ∈ w, i ≠ 0) →
      ∀ (b : Fin 4 → ℤ), (b 0 + b 1 + b 2 + b 3 = 0) →
        cs3.wordProd w * psiTrans b * (cs3.wordProd w)⁻¹ =
          psiTrans (fun k => b ((permOfWord w)⁻¹ k)) := by
    intro w hw
    induction w with
    | nil =>
      intro b _
      simp [permOfWord]
    | cons i rest ih =>
      intro b hb
      have hi : i ≠ 0 := hw i (by simp)
      have hrest : ∀ j ∈ rest, j ≠ 0 := fun j hj => hw j (by simp [hj])
      have hinv_s : (cs3.simple i)⁻¹ = cs3.simple i := cs3.inv_simple i
      have hswap_inv : (swapOf i)⁻¹ = swapOf i := by
        fin_cases i <;> decide
      have hb' : b ((permOfWord rest)⁻¹ 0) + b ((permOfWord rest)⁻¹ 1) +
          b ((permOfWord rest)⁻¹ 2) + b ((permOfWord rest)⁻¹ 3) = 0 := by
        have hsum := Equiv.sum_comp (permOfWord rest)⁻¹ b
        simp only [Fin.sum_univ_four] at hsum
        linarith
      calc
        cs3.wordProd (i :: rest) * psiTrans b * (cs3.wordProd (i :: rest))⁻¹
          = cs3.simple i * (cs3.wordProd rest * psiTrans b * (cs3.wordProd rest)⁻¹) * cs3.simple i := by
              simp only [CoxeterSystem.wordProd_cons, mul_inv_rev, hinv_s, mul_assoc]
        _ = cs3.simple i * psiTrans (fun k => b ((permOfWord rest)⁻¹ k)) * cs3.simple i := by
              rw [ih hrest b hb]
        _ = psiTrans (fun k => b ((permOfWord rest)⁻¹ (swapOf i k))) := by
              exact conj_psiTrans_simple i hi (fun k => b ((permOfWord rest)⁻¹ k)) hb'
        _ = psiTrans (fun k => b ((permOfWord (i :: rest))⁻¹ k)) := by
              simp [permOfWord, mul_inv_rev, hswap_inv]
  have hres := hword (s4Word σ) (s4Word_nonzero σ) a ha
  rwa [permOfWord_s4Word] at hres

/-- Inverse group homomorphism `ψ : AffPerm4 →* W(A₃~)`. -/
def psi : AffPerm4 →* W3 where
  toFun f := psiTrans f.a * phiS4 f.σ
  map_one' := by
    change psiTrans (fun _ => 0) * phiS4 1 = 1
    rw [psiTrans_zero, map_one, one_mul]
  map_mul' f g := by
    change psiTrans (fun i => f.a i + g.a (f.σ⁻¹ i)) * phiS4 (f.σ * g.σ) =
      (psiTrans f.a * phiS4 f.σ) * (psiTrans g.a * phiS4 g.σ)
    rw [psiTrans_add, map_mul, ← conj_psiTrans_perm f.σ g.a g.sum_eq]
    simp only [mul_assoc, inv_mul_cancel_left]

theorem psi_rho_simple (i : Fin 4) : psi (rho (cs3.simple i)) = cs3.simple i := by
  rw [rho_simple]
  match i with
  | 0 =>
    change psiTrans ![1, 0, 0, -1] * phiS4 (Equiv.swap 0 3) = cs3.simple 0
    have htrans : psiTrans ![1, 0, 0, -1] = Tth := by
      have h1 : psiTrans ![1, 0, 0, -1] = T1 * T2 * T3 := by
        simp [psiTrans]
      rw [h1, T1_T2_T3_eq_Tth]
    have hswap : s4Word (Equiv.swap (0 : Fin 4) 3) = [1, 2, 3, 2, 1] := by decide
    rw [htrans]
    change cs3.wordProd [0, 1, 2, 3, 2, 1] * cs3.wordProd (s4Word (Equiv.swap 0 3)) = cs3.simple 0
    rw [hswap]
    simp only [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, mul_one, mul_assoc]
    rw [← mul_assoc (cs3.simple 1) (cs3.simple 1), s_sq, one_mul]
    rw [← mul_assoc (cs3.simple 2) (cs3.simple 2), s_sq, one_mul]
    rw [← mul_assoc (cs3.simple 3) (cs3.simple 3), s_sq, one_mul]
    rw [← mul_assoc (cs3.simple 2) (cs3.simple 2), s_sq, one_mul]
    rw [s_sq, mul_one]
  | 1 =>
    change psiTrans (fun _ => 0) * phiS4 (swapOf 1) = cs3.simple 1
    rw [psiTrans_zero, one_mul]
    exact phiS4_swap 1 (by decide)
  | 2 =>
    change psiTrans (fun _ => 0) * phiS4 (swapOf 2) = cs3.simple 2
    rw [psiTrans_zero, one_mul]
    exact phiS4_swap 2 (by decide)
  | 3 =>
    change psiTrans (fun _ => 0) * phiS4 (swapOf 3) = cs3.simple 3
    rw [psiTrans_zero, one_mul]
    exact phiS4_swap 3 (by decide)

theorem psi_rho (w : W3) : psi (rho w) = w := by
  obtain ⟨ω, rfl⟩ := cs3.wordProd_surjective w
  induction ω with
  | nil => simp
  | cons i rest ih =>
    simp only [CoxeterSystem.wordProd_cons, map_mul, psi_rho_simple, ih]

theorem rho_injective : Function.Injective rho :=
  Function.LeftInverse.injective psi_rho

theorem rho_psi (f : AffPerm4) : rho (psi f) = f := by
  -- Check on T1, T2, T3 and phiS4!
  have hT1 : rho T1 = trans ![1, -1, 0, 0] (by decide) := by
    simp only [T1, wT1, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, map_mul,
      rho_simple, mul_one]
    refine AffPerm4.ext (funext fun k => ?_) (Equiv.ext fun k => ?_) <;> fin_cases k <;> decide
  have hT2 : rho T2 = trans ![0, 1, -1, 0] (by decide) := by
    simp only [T2, wT2, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, map_mul,
      rho_simple, mul_one]
    refine AffPerm4.ext (funext fun k => ?_) (Equiv.ext fun k => ?_) <;> fin_cases k <;> decide
  have hT3 : rho T3 = trans ![0, 0, 1, -1] (by decide) := by
    simp only [T3, wT3, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_nil, map_mul,
      rho_simple, mul_one]
    refine AffPerm4.ext (funext fun k => ?_) (Equiv.ext fun k => ?_) <;> fin_cases k <;> decide
  have htrans_zpow : ∀ (a : Fin 4 → ℤ) (ha : a 0 + a 1 + a 2 + a 3 = 0) (n : ℤ),
      (trans a ha) ^ n = trans (fun k => n * a k)
        (by have : n * a 0 + n * a 1 + n * a 2 + n * a 3 = n * (a 0 + a 1 + a 2 + a 3) := by ring
            rw [this, ha, mul_zero]) := by
    intro a ha n
    induction n using Int.induction_on with
    | zero => ext k <;> simp [trans]
    | succ k ih =>
      rw [zpow_add_one, ih]
      ext j
      · simp [trans]; ring
      · simp [trans]
    | pred k ih =>
      rw [zpow_sub_one, ih]
      ext j
      · simp [trans]; ring
      · simp [trans]
  have hpsiTrans : rho (psiTrans f.a) = trans f.a f.sum_eq := by
    simp only [psiTrans, map_mul, map_zpow, hT1, hT2, hT3, htrans_zpow]
    ext k
    · fin_cases k <;> simp [trans] <;> linarith [f.sum_eq]
    · simp [trans]
  have hphiS4 : ∀ (w : List (Fin 4)), (∀ i ∈ w, i ≠ 0) →
      rho (cs3.wordProd w) = ⟨fun _ => 0, by simp, permOfWord w⟩ := by
    intro w hw
    induction w with
    | nil => ext k <;> simp [permOfWord]
    | cons i rest ih =>
      have hi : i ≠ 0 := hw i (by simp)
      have hrest : ∀ j ∈ rest, j ≠ 0 := fun j hj => hw j (by simp [hj])
      rw [CoxeterSystem.wordProd_cons, map_mul, rho_simple, ih hrest]
      fin_cases i
      · exact absurd rfl hi
      · ext k <;> simp [gen, permOfWord, swapOf]
      · ext k <;> simp [gen, permOfWord, swapOf]
      · ext k <;> simp [gen, permOfWord, swapOf]
  have hS4 : rho (phiS4 f.σ) = ⟨fun _ => 0, by simp, f.σ⟩ := by
    change rho (cs3.wordProd (s4Word f.σ)) = ⟨fun _ => 0, by simp, f.σ⟩
    rw [hphiS4 (s4Word f.σ) (s4Word_nonzero f.σ), permOfWord_s4Word]
  change rho (psiTrans f.a * phiS4 f.σ) = f
  rw [map_mul, hpsiTrans, hS4]
  ext k <;> simp [trans]

/-! ### 5. Exact `ℓ₁` distance formula and counterexample in `W(A₃~)` -/

/-- For `i, j : Fin 4`, the hyperplane-threshold coordinate
`Φ_{ij}(f) = ⌊(f⁻¹(i) - f⁻¹(j)) / 4⌋`. -/
def phiCoord (f : AffPerm4) (i j : Fin 4) : ℤ :=
  (f.evalInv (i : ℤ) - f.evalInv (j : ℤ)) / 4

/-- The `ℓ₁` distance in `ℤ⁶` between `Φ(f)` and `Φ(g)`. -/
def l1Dist (f g : AffPerm4) : ℕ :=
  (phiCoord f 0 1 - phiCoord g 0 1).natAbs +
  (phiCoord f 0 2 - phiCoord g 0 2).natAbs +
  (phiCoord f 0 3 - phiCoord g 0 3).natAbs +
  (phiCoord f 1 2 - phiCoord g 1 2).natAbs +
  (phiCoord f 1 3 - phiCoord g 1 3).natAbs +
  (phiCoord f 2 3 - phiCoord g 2 3).natAbs

theorem phiCoord_eq_lt (f : AffPerm4) {i j : Fin 4} (h : f.σ⁻¹ i < f.σ⁻¹ j) :
    phiCoord f i j = f.a j - f.a i - 1 := by
  dsimp [phiCoord]
  rw [evalInv_fin, evalInv_fin]
  have hlt : ((f.σ⁻¹ i : Fin 4) : ℤ) < ((f.σ⁻¹ j : Fin 4) : ℤ) := by exact_mod_cast h
  have hi0 : 0 ≤ ((f.σ⁻¹ i : Fin 4) : ℤ) := by positivity
  have hj4 : ((f.σ⁻¹ j : Fin 4) : ℤ) < 4 := by exact_mod_cast (f.σ⁻¹ j).isLt
  omega

theorem phiCoord_eq_gt (f : AffPerm4) {i j : Fin 4} (h : f.σ⁻¹ j < f.σ⁻¹ i) :
    phiCoord f i j = f.a j - f.a i := by
  dsimp [phiCoord]
  rw [evalInv_fin, evalInv_fin]
  have hlt : ((f.σ⁻¹ j : Fin 4) : ℤ) < ((f.σ⁻¹ i : Fin 4) : ℤ) := by exact_mod_cast h
  have hj0 : 0 ≤ ((f.σ⁻¹ j : Fin 4) : ℤ) := by positivity
  have hi4 : ((f.σ⁻¹ i : Fin 4) : ℤ) < 4 := by exact_mod_cast (f.σ⁻¹ i).isLt
  omega

theorem phiCoord_bounds (f : AffPerm4) {i j : Fin 4} (h : i ≠ j) :
    f.a j - f.a i - 1 ≤ phiCoord f i j ∧ phiCoord f i j ≤ f.a j - f.a i := by
  have hne : f.σ⁻¹ i ≠ f.σ⁻¹ j := f.σ⁻¹.injective.ne h
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [phiCoord_eq_lt f hlt]; omega
  · rw [phiCoord_eq_gt f hgt]; omega

theorem phiCoord_trans (a : Fin 4 → ℤ) (ha : a 0 + a 1 + a 2 + a 3 = 0)
    {i j : Fin 4} (hij : i < j) :
    phiCoord (trans a ha) i j = a j - a i - 1 := by
  apply phiCoord_eq_lt
  simpa [trans] using hij

theorem phiCoord_one {i j : Fin 4} (hij : i < j) :
    phiCoord 1 i j = -1 := by
  apply phiCoord_eq_lt
  simpa using hij

theorem l1Dist_self (f : AffPerm4) : l1Dist f f = 0 := by
  simp [l1Dist]

theorem l1Dist_comm (f g : AffPerm4) : l1Dist f g = l1Dist g f := by
  have hsub : ∀ x y : ℤ, (x - y).natAbs = (y - x).natAbs := by intro x y; omega
  dsimp [l1Dist]
  rw [hsub (phiCoord f 0 1), hsub (phiCoord f 0 2), hsub (phiCoord f 0 3),
      hsub (phiCoord f 1 2), hsub (phiCoord f 1 3), hsub (phiCoord f 2 3)]

theorem l1Dist_triangle (f g h : AffPerm4) : l1Dist f h ≤ l1Dist f g + l1Dist g h := by
  have tri : ∀ x y z : ℤ, (x - z).natAbs ≤ (x - y).natAbs + (y - z).natAbs := by
    intro x y z; omega
  dsimp [l1Dist]
  linarith [tri (phiCoord f 0 1) (phiCoord g 0 1) (phiCoord h 0 1),
            tri (phiCoord f 0 2) (phiCoord g 0 2) (phiCoord h 0 2),
            tri (phiCoord f 0 3) (phiCoord g 0 3) (phiCoord h 0 3),
            tri (phiCoord f 1 2) (phiCoord g 1 2) (phiCoord h 1 2),
            tri (phiCoord f 1 3) (phiCoord g 1 3) (phiCoord h 1 3),
            tri (phiCoord f 2 3) (phiCoord g 2 3) (phiCoord h 2 3)]

/-- The residue pair `(rLo k, rHi k)` swapped by `gen k`, where `gen k` increases `rLo k`
by `+1` and decreases `rHi k` by `-1`. -/
private def rLo : Fin 4 → Fin 4
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2

private def rHi : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

private def uBase : Fin 4 → ℤ
  | 0 => 3
  | 1 => 0
  | 2 => 1
  | 3 => 2

private theorem gen_inv (k : Fin 4) : (gen k)⁻¹ = gen k := by
  have h : gen k * gen k = 1 := by
    have := gen_coxeter k k
    have hdiag : A3TildeMatrix k k = 1 := A3TildeMatrix.diagonal k
    rw [hdiag, pow_one] at this
    exact this
  exact inv_eq_of_mul_eq_one_right h

private theorem eval_gen (k : Fin 4) (x : ℤ) :
    (gen k).eval x =
      if mod4 x = rLo k then x + 1
      else if mod4 x = rHi k then x - 1
      else x := by
  have hdecomp := decomp_four x
  have hval := val_mod4 x
  generalize hm : mod4 x = r
  have hr : (r : ℤ) = x % 4 := by rw [← hm, hval]
  have hq : x = (r : ℤ) + 4 * (x / 4) := by omega
  match k, r with
  | 0, 0 => simp [eval, gen, rLo, rHi, hm]; omega
  | 0, 1 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 0, 2 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 0, 3 => simp [eval, gen, rLo, hm]; omega
  | 1, 0 => simp [eval, gen, rLo, hm]; omega
  | 1, 1 => simp [eval, gen, rLo, rHi, hm]; omega
  | 1, 2 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 1, 3 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 2, 0 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 2, 1 => simp [eval, gen, rLo, hm]; omega
  | 2, 2 => simp [eval, gen, rLo, rHi, hm]; omega
  | 2, 3 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 3, 0 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 3, 1 => simp [eval, gen, rLo, rHi, hm, Equiv.swap_apply_def]; omega
  | 3, 2 => simp [eval, gen, rLo, hm]; omega
  | 3, 3 => simp [eval, gen, rLo, rHi, hm]; omega

private theorem evalInv_mul_gen (f : AffPerm4) (k : Fin 4) (y : ℤ) :
    (f * gen k).evalInv y = (gen k).eval (f.evalInv y) := by
  rw [evalInv_eq_eval_inv, mul_inv_rev, gen_inv, eval_mul, evalInv_eq_eval_inv]

private theorem mod4_evalInv_fin (f : AffPerm4) (i : Fin 4) :
    mod4 (f.evalInv (i : ℤ)) = f.σ⁻¹ i := by
  rw [evalInv_fin]
  have h : (f.σ⁻¹ i : ℤ) - 4 * f.a i = (f.σ⁻¹ i : ℤ) + 4 * (-f.a i) := by ring
  rw [h, mod4_add_mul_four]

private theorem phiCoord_mul_gen (f : AffPerm4) (k : Fin 4) {i j : Fin 4} (hij : i < j) :
    phiCoord (f * gen k) i j =
      if i = f.σ (rLo k) ∧ j = f.σ (rHi k) then phiCoord f i j + 1
      else if i = f.σ (rHi k) ∧ j = f.σ (rLo k) then phiCoord f i j - 1
      else phiCoord f i j := by
  have hne_r : rLo k ≠ rHi k := by fin_cases k <;> decide
  have hne_ij : i ≠ j := ne_of_lt hij
  have hmod_i : mod4 (f.evalInv (i : ℤ)) = f.σ⁻¹ i := mod4_evalInv_fin f i
  have hmod_j : mod4 (f.evalInv (j : ℤ)) = f.σ⁻¹ j := mod4_evalInv_fin f j
  have hxi : f.evalInv (i : ℤ) % 4 = ((f.σ⁻¹ i : Fin 4) : ℤ) := by
    rw [← val_mod4, hmod_i]
  have hxj : f.evalInv (j : ℤ) % 4 = ((f.σ⁻¹ j : Fin 4) : ℤ) := by
    rw [← val_mod4, hmod_j]
  have hmod_ne : f.σ⁻¹ i ≠ f.σ⁻¹ j := f.σ⁻¹.injective.ne hne_ij
  have hmod_lo_i : f.σ⁻¹ i = rLo k ↔ i = f.σ (rLo k) := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  have hmod_hi_i : f.σ⁻¹ i = rHi k ↔ i = f.σ (rHi k) := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  have hmod_lo_j : f.σ⁻¹ j = rLo k ↔ j = f.σ (rLo k) := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  have hmod_hi_j : f.σ⁻¹ j = rHi k ↔ j = f.σ (rHi k) := by
    constructor
    · intro h; rw [← h]; simp
    · intro h; rw [h]; simp
  dsimp only [phiCoord]
  rw [evalInv_mul_gen, evalInv_mul_gen, eval_gen, eval_gen, hmod_i, hmod_j]
  generalize hri : f.σ⁻¹ i = ri at hxi hmod_ne hmod_lo_i hmod_hi_i ⊢
  generalize hrj : f.σ⁻¹ j = rj at hxj hmod_ne hmod_lo_j hmod_hi_j ⊢
  fin_cases k <;> fin_cases ri <;> fin_cases rj <;>
    simp_all [rLo, rHi] <;> omega

private theorem l1Dist_mul_gen_self (f : AffPerm4) (k : Fin 4) :
    l1Dist f (f * gen k) = 1 := by
  dsimp only [l1Dist]
  rw [phiCoord_mul_gen f k (by decide),
      phiCoord_mul_gen f k (by decide),
      phiCoord_mul_gen f k (by decide),
      phiCoord_mul_gen f k (by decide),
      phiCoord_mul_gen f k (by decide),
      phiCoord_mul_gen f k (by decide)]
  have hne : f.σ (rLo k) ≠ f.σ (rHi k) := f.σ.injective.ne (by fin_cases k <;> decide)
  generalize ha : f.σ (rLo k) = a at hne ⊢
  generalize hb : f.σ (rHi k) = b at hne ⊢
  fin_cases a <;> fin_cases b <;> simp_all

private theorem l1Dist_le_length (u v : W3) : l1Dist (rho u) (rho v) ≤ cs3.length (u⁻¹ * v) := by
  obtain ⟨ω, hred, hω⟩ := cs3.exists_isReduced (u⁻¹ * v)
  have hv : v = u * cs3.wordProd ω := by
    rw [← hω, mul_inv_cancel_left]
  have hlen : cs3.length (u⁻¹ * v) = ω.length := by
    rw [hω, ← hred.eq]
  rw [hlen, hv]
  clear hred hω hv hlen v
  induction ω generalizing u with
  | nil => simp [l1Dist_self]
  | cons k rest ih =>
    rw [CoxeterSystem.wordProd_cons, ← mul_assoc]
    have h1 := l1Dist_triangle (rho u) (rho (u * cs3.simple k)) (rho (u * cs3.simple k * cs3.wordProd rest))
    have hstep : l1Dist (rho u) (rho (u * cs3.simple k)) = 1 := by
      rw [map_mul, rho_simple]
      exact l1Dist_mul_gen_self (rho u) k
    have hrest := ih (u * cs3.simple k)
    simp only [List.length_cons]
    omega

private theorem eval_uBase (g : AffPerm4) (k : Fin 4) :
    mod4 (g.eval (uBase k)) = g.σ (rLo k) ∧
    mod4 (g.eval (uBase k + 1)) = g.σ (rHi k) := by
  have h1 : mod4 (uBase k) = rLo k := by fin_cases k <;> decide
  have h2 : mod4 (uBase k + 1) = rHi k := by fin_cases k <;> decide
  constructor
  · simp only [eval, h1]; exact mod4_add_mul_four _ _
  · simp only [eval, h2]; exact mod4_add_mul_four _ _

private theorem l1Dist_mul_gen_descent (f g : AffPerm4) (k : Fin 4)
    (hinv : f.evalInv (g.eval (uBase k + 1)) < f.evalInv (g.eval (uBase k))) :
    l1Dist f (g * gen k) + 1 = l1Dist f g := by
  set a : Fin 4 := g.σ (rLo k)
  set b : Fin 4 := g.σ (rHi k)
  have hne : a ≠ b := g.σ.injective.ne (by fin_cases k <;> decide)
  have hy0 : g.eval (uBase k) = (a : ℤ) + 4 * (g.eval (uBase k) / 4) := by
    have := decomp_four (g.eval (uBase k))
    rw [(eval_uBase g k).1] at this
    omega
  have hy1 : g.eval (uBase k + 1) = (b : ℤ) + 4 * (g.eval (uBase k + 1) / 4) := by
    have := decomp_four (g.eval (uBase k + 1))
    rw [(eval_uBase g k).2] at this
    omega
  set q0 : ℤ := g.eval (uBase k) / 4
  set q1 : ℤ := g.eval (uBase k + 1) / 4
  have hga : g.evalInv (a : ℤ) = uBase k - 4 * q0 := by
    have := evalInv_eval g (uBase k)
    rw [hy0, evalInv_add_mul_four] at this
    omega
  have hgb : g.evalInv (b : ℤ) = uBase k + 1 - 4 * q1 := by
    have := evalInv_eval g (uBase k + 1)
    rw [hy1, evalInv_add_mul_four] at this
    omega
  have hfa_fb : f.evalInv (b : ℤ) + 4 * q1 < f.evalInv (a : ℤ) + 4 * q0 := by
    rw [hy0, hy1, evalInv_add_mul_four, evalInv_add_mul_four] at hinv
    exact hinv
  have hphi_ab : phiCoord g a b < phiCoord f a b := by
    dsimp only [phiCoord]
    rw [hga, hgb]
    omega
  have hphi_ba : phiCoord f b a < phiCoord g b a := by
    dsimp only [phiCoord]
    rw [hga, hgb]
    omega
  change g.σ (rLo k) ≠ g.σ (rHi k) at hne
  change phiCoord g (g.σ (rLo k)) (g.σ (rHi k)) < phiCoord f (g.σ (rLo k)) (g.σ (rHi k)) at hphi_ab
  change phiCoord f (g.σ (rHi k)) (g.σ (rLo k)) < phiCoord g (g.σ (rHi k)) (g.σ (rLo k)) at hphi_ba
  dsimp only [l1Dist]
  rw [phiCoord_mul_gen g k (by decide),
      phiCoord_mul_gen g k (by decide),
      phiCoord_mul_gen g k (by decide),
      phiCoord_mul_gen g k (by decide),
      phiCoord_mul_gen g k (by decide),
      phiCoord_mul_gen g k (by decide)]
  clear hy0 hy1 q0 q1 hga hgb hfa_fb hinv a b
  generalize ha : g.σ (rLo k) = a' at hne hphi_ab hphi_ba ⊢
  generalize hb : g.σ (rHi k) = b' at hne hphi_ab hphi_ba ⊢
  fin_cases a' <;> fin_cases b' <;> simp_all <;> omega

private theorem exists_descent (f g : AffPerm4) (hne : f ≠ g) :
    ∃ k : Fin 4, f.evalInv (g.eval (uBase k + 1)) < f.evalInv (g.eval (uBase k)) := by
  by_contra hall
  push Not at hall
  set h : AffPerm4 := f⁻¹ * g
  have heval : ∀ x : ℤ, h.eval x = f.evalInv (g.eval x) := by
    intro x
    rw [eval_mul, evalInv_eq_eval_inv]
  have h01 : h.eval 0 ≤ h.eval 1 := by simpa [heval, uBase] using hall 1
  have h12 : h.eval 1 ≤ h.eval 2 := by simpa [heval, uBase] using hall 2
  have h23 : h.eval 2 ≤ h.eval 3 := by simpa [heval, uBase] using hall 3
  have h34 : h.eval 3 ≤ h.eval 4 := by simpa [heval, uBase] using hall 0
  have h4 : h.eval 4 = h.eval 0 + 4 := by
    have := eval_add_mul_four h 0 1
    simpa using this
  have hne01 : h.eval 0 ≠ h.eval 1 := h.eval_injective.ne (by omega)
  have hne12 : h.eval 1 ≠ h.eval 2 := h.eval_injective.ne (by omega)
  have hne23 : h.eval 2 ≠ h.eval 3 := h.eval_injective.ne (by omega)
  have hne34 : h.eval 3 ≠ h.eval 4 := h.eval_injective.ne (by omega)
  have hstep1 : h.eval 1 = h.eval 0 + 1 := by omega
  have hstep2 : h.eval 2 = h.eval 0 + 2 := by omega
  have hstep3 : h.eval 3 = h.eval 0 + 3 := by omega
  have hsum_eval : h.eval 0 + h.eval 1 + h.eval 2 + h.eval 3 = 6 := by
    have hf0 := eval_fin h 0
    have hf1 := eval_fin h 1
    have hf2 := eval_fin h 2
    have hf3 := eval_fin h 3
    have hsumσ : ((h.σ 0 : Fin 4) : ℤ) + (h.σ 1 : Fin 4) + (h.σ 2 : Fin 4) + (h.σ 3 : Fin 4) = 6 := by
      have hs := Equiv.sum_comp h.σ (fun j : Fin 4 => (j : ℤ))
      simp only [Fin.sum_univ_four] at hs
      simpa using hs
    have hsuma : h.a (h.σ 0) + h.a (h.σ 1) + h.a (h.σ 2) + h.a (h.σ 3) = 0 := by
      have hs := Equiv.sum_comp h.σ h.a
      simp only [Fin.sum_univ_four] at hs
      linarith [h.sum_eq]
    change h.eval (0 : Fin 4) + h.eval (1 : Fin 4) + h.eval (2 : Fin 4) + h.eval (3 : Fin 4) = 6
    rw [hf0, hf1, hf2, hf3]
    linarith
  have hx0 : h.eval 0 = 0 := by omega
  have hx1 : h.eval 1 = 1 := by omega
  have hx2 : h.eval 2 = 2 := by omega
  have hx3 : h.eval 3 = 3 := by omega
  have hh_one : h = 1 := by
    have hσj : ∀ j : Fin 4, h.σ j = j ∧ h.a (h.σ j) = 0 := by
      intro j
      have hj : h.eval (j : ℤ) = (j : ℤ) := by
        fin_cases j <;> assumption
      rw [eval_fin] at hj
      have hmod : h.σ j = j := by
        have hjlt : ((j : Fin 4) : ℤ) < 4 := by exact_mod_cast j.isLt
        have hσlt : ((h.σ j : Fin 4) : ℤ) < 4 := by exact_mod_cast (h.σ j).isLt
        have hj0 : 0 ≤ ((j : Fin 4) : ℤ) := by positivity
        have hσ0 : 0 ≤ ((h.σ j : Fin 4) : ℤ) := by positivity
        ext; omega
      refine ⟨hmod, ?_⟩
      rw [hmod] at hj ⊢
      omega
    refine AffPerm4.ext (funext fun j => ?_) (Equiv.ext fun j => (hσj j).1)
    have ⟨h1, h2⟩ := hσj j
    rw [h1] at h2
    exact h2
  apply hne
  have : f⁻¹ * g = 1 := hh_one
  exact inv_mul_eq_one.mp this

private theorem length_le_l1Dist :
    ∀ n : ℕ, ∀ u v : W3, l1Dist (rho u) (rho v) = n → cs3.length (u⁻¹ * v) ≤ n := by
  intro n
  induction n with
  | zero =>
    intro u v h0
    by_cases huv : rho u = rho v
    · have heq : u = v := rho_injective huv
      subst heq
      simp [cs3.length_one]
    · obtain ⟨k, hk⟩ := exists_descent (rho u) (rho v) huv
      have hdesc := l1Dist_mul_gen_descent (rho u) (rho v) k hk
      omega
  | succ n ih =>
    intro u v hsn
    have hne : rho u ≠ rho v := by
      intro heq
      rw [heq, l1Dist_self] at hsn
      omega
    obtain ⟨k, hk⟩ := exists_descent (rho u) (rho v) hne
    have hdesc := l1Dist_mul_gen_descent (rho u) (rho v) k hk
    have hn : l1Dist (rho u) (rho (v * cs3.simple k)) = n := by
      rw [map_mul, rho_simple]
      omega
    have hle := ih u (v * cs3.simple k) hn
    have hrew : u⁻¹ * v = (u⁻¹ * (v * cs3.simple k)) * cs3.simple k := by
      simp only [mul_assoc, s_sq, mul_one]
    rw [hrew]
    have hstep := cs3.length_mul_le (u⁻¹ * (v * cs3.simple k)) (cs3.simple k)
    have hsk := cs3.length_simple k
    omega

/-- Exact `ℓ₁` distance formula on `Cay(W(A₃~), S)`. -/
theorem cayleyGraph_dist_eq_l1Dist (u v : W3) :
    (cayleyGraph cs3).dist u v = l1Dist (rho u) (rho v) := by
  rw [cayleyGraph_dist]
  exact le_antisymm (length_le_l1Dist _ u v rfl) (l1Dist_le_length u v)

/-- Integer interval membership `min a b ≤ c ≤ max a b`. -/
def Between (a b c : ℤ) : Prop :=
  min a b ≤ c ∧ c ≤ max a b

private theorem natAbs_add_eq_iff (a b c : ℤ) :
    (a - c).natAbs + (c - b).natAbs = (a - b).natAbs ↔ Between a b c := by
  dsimp [Between]
  omega

/-- The `Φ`-coordinate box spanned by `u, v ∈ W(A₃~)`. -/
def phiBox (u v : W3) : Set W3 :=
  {w : W3 |
    Between (phiCoord (rho u) 0 1) (phiCoord (rho v) 0 1) (phiCoord (rho w) 0 1) ∧
    Between (phiCoord (rho u) 0 2) (phiCoord (rho v) 0 2) (phiCoord (rho w) 0 2) ∧
    Between (phiCoord (rho u) 0 3) (phiCoord (rho v) 0 3) (phiCoord (rho w) 0 3) ∧
    Between (phiCoord (rho u) 1 2) (phiCoord (rho v) 1 2) (phiCoord (rho w) 1 2) ∧
    Between (phiCoord (rho u) 1 3) (phiCoord (rho v) 1 3) (phiCoord (rho w) 1 3) ∧
    Between (phiCoord (rho u) 2 3) (phiCoord (rho v) 2 3) (phiCoord (rho w) 2 3)}

private theorem dist_add_eq_iff_phiBox (u v w : W3) :
    (cayleyGraph cs3).dist u w + (cayleyGraph cs3).dist w v = (cayleyGraph cs3).dist u v ↔
      w ∈ phiBox u v := by
  rw [cayleyGraph_dist_eq_l1Dist, cayleyGraph_dist_eq_l1Dist, cayleyGraph_dist_eq_l1Dist]
  have htri : ∀ x y z : ℤ, (x - z).natAbs ≤ (x - y).natAbs + (y - z).natAbs := by
    intro x y z; omega
  have t01 := htri (phiCoord (rho u) 0 1) (phiCoord (rho w) 0 1) (phiCoord (rho v) 0 1)
  have t02 := htri (phiCoord (rho u) 0 2) (phiCoord (rho w) 0 2) (phiCoord (rho v) 0 2)
  have t03 := htri (phiCoord (rho u) 0 3) (phiCoord (rho w) 0 3) (phiCoord (rho v) 0 3)
  have t12 := htri (phiCoord (rho u) 1 2) (phiCoord (rho w) 1 2) (phiCoord (rho v) 1 2)
  have t13 := htri (phiCoord (rho u) 1 3) (phiCoord (rho w) 1 3) (phiCoord (rho v) 1 3)
  have t23 := htri (phiCoord (rho u) 2 3) (phiCoord (rho w) 2 3) (phiCoord (rho v) 2 3)
  dsimp only [l1Dist, phiBox, Set.mem_ofPred_eq]
  rw [← natAbs_add_eq_iff, ← natAbs_add_eq_iff, ← natAbs_add_eq_iff,
      ← natAbs_add_eq_iff, ← natAbs_add_eq_iff, ← natAbs_add_eq_iff]
  constructor
  · intro hsum
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rintro ⟨h01, h02, h03, h12, h13, h23⟩
    omega

private theorem isConvex_phiBox (u v : W3) : IsConvex (cayleyGraph cs3) (phiBox u v) := by
  intro x hx y hy z hdist
  have hzxy : z ∈ phiBox x y := (dist_add_eq_iff_phiBox x y z).mp hdist
  rcases hx with ⟨hx01, hx02, hx03, hx12, hx13, hx23⟩
  rcases hy with ⟨hy01, hy02, hy03, hy12, hy13, hy23⟩
  rcases hzxy with ⟨hz01, hz02, hz03, hz12, hz13, hz23⟩
  dsimp only [phiBox, Set.mem_ofPred_eq, Between] at *
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Exact characterization of two-point geodesic convex hulls in `Cay(W(A₃~), S)`. -/
theorem convexHull_pair_eq_phiBox (u v : W3) :
    convexHull (cayleyGraph cs3) {u, v} = phiBox u v := by
  apply Set.Subset.antisymm
  · apply convexHull_subset
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl <;>
        exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩,
               ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
    · exact isConvex_phiBox u v
  · intro w hw
    exact mem_convexHull_pair_of_dist (cayleyGraph cs3) ((dist_add_eq_iff_phiBox u v w).mpr hw)

/-! ### 6. Explicit counterexample in `W(A₃~)` -/

/-- Pure translation `u(m) = t_{(6m, 6m, -6m, -6m)} ∈ W(A₃~)`. -/
def uFamily (m : ℕ) : W3 :=
  psi (trans ![(6 * (m : ℤ)), 6 * (m : ℤ), -(6 * (m : ℤ)), -(6 * (m : ℤ))]
    (by simp))

/-- Pure translation `v(m) = t_{(12m, -12m, 12m, -12m)} ∈ W(A₃~)`. -/
def vFamily (m : ℕ) : W3 :=
  psi (trans ![(12 * (m : ℤ)), -(12 * (m : ℤ)), 12 * (m : ℤ), -(12 * (m : ℤ))]
    (by simp))

private theorem uFamily_phi_bounds (m : ℕ) {w : W3} (hw : w ∈ phiBox 1 (uFamily m)) :
    0 ≤ (rho w).a 0 - (rho w).a 1 ∧
    (rho w).a 0 - (rho w).a 1 ≤ 1 ∧
    (rho w).a 2 - (rho w).a 3 = (rho w).a 0 - (rho w).a 1 ∧
    0 ≤ (rho w).a 0 ∧
    (rho w).a 0 ≤ 6 * (m : ℤ) + 1 := by
  have hu : rho (uFamily m) =
      trans ![(6 * (m : ℤ)), 6 * (m : ℤ), -(6 * (m : ℤ)), -(6 * (m : ℤ))] (by simp) :=
    rho_psi _
  have h01 := hw.1
  have h02 := hw.2.1
  have h23 := hw.2.2.2.2.2
  have h1_01 : phiCoord (rho 1) 0 1 = -1 := by rw [map_one]; exact phiCoord_one (by decide)
  have h1_02 : phiCoord (rho 1) 0 2 = -1 := by rw [map_one]; exact phiCoord_one (by decide)
  have h1_23 : phiCoord (rho 1) 2 3 = -1 := by rw [map_one]; exact phiCoord_one (by decide)
  have hu_01 : phiCoord (rho (uFamily m)) 0 1 = -1 := by
    rw [hu, phiCoord_trans _ _ (by decide)]; simp
  have hu_02 : phiCoord (rho (uFamily m)) 0 2 = -(12 * (m : ℤ)) - 1 := by
    rw [hu, phiCoord_trans _ _ (by decide)]; simp; ring
  have hu_23 : phiCoord (rho (uFamily m)) 2 3 = -1 := by
    rw [hu, phiCoord_trans _ _ (by decide)]; simp
  have hb01 := phiCoord_bounds (rho w) (by decide : (0 : Fin 4) ≠ 1)
  have hb02 := phiCoord_bounds (rho w) (by decide : (0 : Fin 4) ≠ 2)
  have hb23 := phiCoord_bounds (rho w) (by decide : (2 : Fin 4) ≠ 3)
  have hsum := (rho w).sum_eq
  dsimp only [Between] at h01 h02 h23
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

private theorem vFamily_phi_bounds (m : ℕ) {w : W3} (hw : w ∈ phiBox 1 (vFamily m)) :
    0 ≤ (rho w).a 0 - (rho w).a 2 ∧
    (rho w).a 0 - (rho w).a 2 ≤ 1 ∧
    (rho w).a 1 - (rho w).a 3 = (rho w).a 0 - (rho w).a 2 ∧
    0 ≤ (rho w).a 0 ∧
    (rho w).a 0 ≤ 12 * (m : ℤ) + 1 := by
  have hv : rho (vFamily m) =
      trans ![(12 * (m : ℤ)), -(12 * (m : ℤ)), 12 * (m : ℤ), -(12 * (m : ℤ))] (by simp) :=
    rho_psi _
  have h01 := hw.1
  have h02 := hw.2.1
  have h13 := hw.2.2.2.2.1
  have h1_01 : phiCoord (rho 1) 0 1 = -1 := by rw [map_one]; exact phiCoord_one (by decide)
  have h1_02 : phiCoord (rho 1) 0 2 = -1 := by rw [map_one]; exact phiCoord_one (by decide)
  have h1_13 : phiCoord (rho 1) 1 3 = -1 := by rw [map_one]; exact phiCoord_one (by decide)
  have hv_01 : phiCoord (rho (vFamily m)) 0 1 = -(24 * (m : ℤ)) - 1 := by
    rw [hv, phiCoord_trans _ _ (by decide)]; simp; ring
  have hv_02 : phiCoord (rho (vFamily m)) 0 2 = -1 := by
    rw [hv, phiCoord_trans _ _ (by decide)]; simp
  have hv_13 : phiCoord (rho (vFamily m)) 1 3 = -1 := by
    rw [hv, phiCoord_trans _ _ (by decide)]; simp
  have hb01 := phiCoord_bounds (rho w) (by decide : (0 : Fin 4) ≠ 1)
  have hb02 := phiCoord_bounds (rho w) (by decide : (0 : Fin 4) ≠ 2)
  have hb13 := phiCoord_bounds (rho w) (by decide : (1 : Fin 4) ≠ 3)
  have hsum := (rho w).sum_eq
  dsimp only [Between] at h01 h02 h13
  exact ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Linear upper bound `|Conv(1, u(m))| ≤ 48 (6m + 2)`. -/
theorem encard_convexHull_one_uFamily_le (m : ℕ) :
    (convexHull (cayleyGraph cs3) {1, uFamily m}).encard ≤ (48 * (6 * m + 2) : ℕ) := by
  rw [convexHull_pair_eq_phiBox]
  let encode : phiBox 1 (uFamily m) → Equiv.Perm (Fin 4) × Fin 2 × Fin (6 * m + 2) :=
    fun ⟨w, hw⟩ =>
      have hb := uFamily_phi_bounds m hw
      ((rho w).σ,
       ⟨((rho w).a 0 - (rho w).a 1).toNat, by omega⟩,
       ⟨((rho w).a 0).toNat, by omega⟩)
  have hinj : Function.Injective encode := by
    intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ heq
    dsimp only [encode] at heq
    apply Subtype.ext; dsimp only
    apply rho_injective
    have hσ : (rho w₁).σ = (rho w₂).σ := congrArg Prod.fst heq
    have hδ_eq : ((rho w₁).a 0 - (rho w₁).a 1).toNat = ((rho w₂).a 0 - (rho w₂).a 1).toNat :=
      congrArg (fun p => p.2.1.val) heq
    have ha0_eq : ((rho w₁).a 0).toNat = ((rho w₂).a 0).toNat :=
      congrArg (fun p => p.2.2.val) heq
    obtain ⟨h1a, _, h1c, h1d, _⟩ := uFamily_phi_bounds m hw₁
    obtain ⟨h2a, _, h2c, h2d, _⟩ := uFamily_phi_bounds m hw₂
    have hs1 := (rho w₁).sum_eq
    have hs2 := (rho w₂).sum_eq
    refine AffPerm4.ext (funext fun k => ?_) hσ
    match k with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
  have hcard_le : (phiBox 1 (uFamily m)).encard ≤
      (Fintype.card (Equiv.Perm (Fin 4) × Fin 2 × Fin (6 * m + 2)) : ℕ) := by
    rw [Set.encard, ← ENat.card_eq_coe_fintype_card]
    exact ENat.card_le_card_of_injective hinj
  have hcard_eq : Fintype.card (Equiv.Perm (Fin 4) × Fin 2 × Fin (6 * m + 2)) =
      48 * (6 * m + 2) := by
    simp [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
    ring
  rwa [hcard_eq] at hcard_le

/-- Linear upper bound `|Conv(1, v(m))| ≤ 48 (12m + 2)`. -/
theorem encard_convexHull_one_vFamily_le (m : ℕ) :
    (convexHull (cayleyGraph cs3) {1, vFamily m}).encard ≤ (48 * (12 * m + 2) : ℕ) := by
  rw [convexHull_pair_eq_phiBox]
  let encode : phiBox 1 (vFamily m) → Equiv.Perm (Fin 4) × Fin 2 × Fin (12 * m + 2) :=
    fun ⟨w, hw⟩ =>
      have hb := vFamily_phi_bounds m hw
      ((rho w).σ,
       ⟨((rho w).a 0 - (rho w).a 2).toNat, by omega⟩,
       ⟨((rho w).a 0).toNat, by omega⟩)
  have hinj : Function.Injective encode := by
    intro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ heq
    dsimp only [encode] at heq
    apply Subtype.ext; dsimp only
    apply rho_injective
    have hσ : (rho w₁).σ = (rho w₂).σ := congrArg Prod.fst heq
    have hδ_eq : ((rho w₁).a 0 - (rho w₁).a 2).toNat = ((rho w₂).a 0 - (rho w₂).a 2).toNat :=
      congrArg (fun p => p.2.1.val) heq
    have ha0_eq : ((rho w₁).a 0).toNat = ((rho w₂).a 0).toNat :=
      congrArg (fun p => p.2.2.val) heq
    obtain ⟨h1a, _, h1c, h1d, _⟩ := vFamily_phi_bounds m hw₁
    obtain ⟨h2a, _, h2c, h2d, _⟩ := vFamily_phi_bounds m hw₂
    have hs1 := (rho w₁).sum_eq
    have hs2 := (rho w₂).sum_eq
    refine AffPerm4.ext (funext fun k => ?_) hσ
    match k with
    | 0 => omega
    | 1 => omega
    | 2 => omega
    | 3 => omega
  have hcard_le : (phiBox 1 (vFamily m)).encard ≤
      (Fintype.card (Equiv.Perm (Fin 4) × Fin 2 × Fin (12 * m + 2)) : ℕ) := by
    rw [Set.encard, ← ENat.card_eq_coe_fintype_card]
    exact ENat.card_le_card_of_injective hinj
  have hcard_eq : Fintype.card (Equiv.Perm (Fin 4) × Fin 2 × Fin (12 * m + 2)) =
      48 * (12 * m + 2) := by
    simp [Fintype.card_perm, Fintype.card_fin]
    norm_num [Nat.factorial]
    ring
  rwa [hcard_eq] at hcard_le

/-- Cubic lower bound `(m + 1)³ ≤ |Conv(u(m), v(m))|`. -/
theorem le_encard_convexHull_uFamily_vFamily (m : ℕ) :
    (((m + 1) ^ 3 : ℕ) : ENat) ≤
      (convexHull (cayleyGraph cs3) {uFamily m, vFamily m}).encard := by
  rw [convexHull_pair_eq_phiBox]
  let boxPt (p q r : Fin (m + 1)) : AffPerm4 :=
    trans ![9 * (m : ℤ) + (p : ℤ),
            -(3 * (m : ℤ)) + (q : ℤ),
            3 * (m : ℤ) + (r : ℤ),
            -(9 * (m : ℤ)) - (p : ℤ) - (q : ℤ) - (r : ℤ)] (by simp; ring)
  let emb : Fin (m + 1) × Fin (m + 1) × Fin (m + 1) →
      phiBox (uFamily m) (vFamily m) := fun ⟨p, q, r⟩ =>
    ⟨psi (boxPt p q r), by
      have hu : rho (uFamily m) =
          trans ![(6 * (m : ℤ)), 6 * (m : ℤ), -(6 * (m : ℤ)), -(6 * (m : ℤ))]
            (by simp) := rho_psi _
      have hv : rho (vFamily m) =
          trans ![(12 * (m : ℤ)), -(12 * (m : ℤ)), 12 * (m : ℤ), -(12 * (m : ℤ))]
            (by simp) := rho_psi _
      have hw : rho (psi (boxPt p q r)) = boxPt p q r := rho_psi _
      have hp0 : (0 : ℤ) ≤ (p : ℤ) := by positivity
      have hq0 : (0 : ℤ) ≤ (q : ℤ) := by positivity
      have hr0 : (0 : ℤ) ≤ (r : ℤ) := by positivity
      have hpM : (p : ℤ) ≤ (m : ℤ) := by have := p.isLt; omega
      have hqM : (q : ℤ) ≤ (m : ℤ) := by have := q.isLt; omega
      have hrM : (r : ℤ) ≤ (m : ℤ) := by have := r.isLt; omega
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (dsimp only [Between]; rw [hu, hv, hw,
          phiCoord_trans _ _ (by decide), phiCoord_trans _ _ (by decide),
          phiCoord_trans _ _ (by decide)]; simp; omega)⟩
  have hinj : Function.Injective emb := by
    intro ⟨p₁, q₁, r₁⟩ ⟨p₂, q₂, r₂⟩ heq
    have hval := congrArg (fun x => rho x.val) heq
    simp only [emb, rho_psi] at hval
    have ha0 := congrArg (fun f : AffPerm4 => f.a 0) hval
    have ha1 := congrArg (fun f : AffPerm4 => f.a 1) hval
    have ha2 := congrArg (fun f : AffPerm4 => f.a 2) hval
    simp only [boxPt, trans] at ha0 ha1 ha2
    simp at ha0 ha1 ha2
    refine Prod.ext (Fin.ext ?_) (Prod.ext (Fin.ext ?_) (Fin.ext ?_)) <;> omega
  have hcard_le : (Fintype.card (Fin (m + 1) × Fin (m + 1) × Fin (m + 1)) : ENat) ≤
      (phiBox (uFamily m) (vFamily m)).encard := by
    rw [Set.encard, ← ENat.card_eq_coe_fintype_card]
    exact ENat.card_le_card_of_injective hinj
  have hcard_eq : Fintype.card (Fin (m + 1) × Fin (m + 1) × Fin (m + 1)) =
      (m + 1) ^ 3 := by
    simp [Fintype.card_fin]
    ring
  rwa [hcard_eq] at hcard_le

end AffPerm4

/-- The undirected right Cayley graph of `W(A₃~)` fails the ordinary hull property
(so `log |Conv(-, -)|` is not a metric on `W(A₃~)`). -/
theorem not_hasHullProperty_A3Tilde : ¬ HasHullProperty (cayleyGraph cs3) := by
  intro hHull
  have hpair := hHull (AffPerm4.uFamily 200000) 1 (AffPerm4.vFamily 200000)
  have hsymm : ({AffPerm4.uFamily 200000, (1 : W3)} : Set W3) = {1, AffPerm4.uFamily 200000} := by
    ext x; simp [or_comm]
  rw [hsymm] at hpair
  have hu := AffPerm4.encard_convexHull_one_uFamily_le 200000
  have hv := AffPerm4.encard_convexHull_one_vFamily_le 200000
  have huv := AffPerm4.le_encard_convexHull_uFamily_vFamily 200000
  have hprod :
      (((200000 + 1) ^ 3 : ℕ) : ENat) ≤
        ((48 * (6 * 200000 + 2) : ℕ) : ENat) *
        ((48 * (12 * 200000 + 2) : ℕ) : ENat) :=
    huv.trans (hpair.trans (mul_le_mul' hu hv))
  have hnat :
      (200000 + 1) ^ 3 ≤
        (48 * (6 * 200000 + 2)) * (48 * (12 * 200000 + 2)) := by
    exact_mod_cast hprod
  norm_num at hnat

/-- Conjecture 1.2 of Gaetz–Gao (`arXiv:2012.06841`) is false:
the undirected right Cayley graph of `W(A₃~)` fails the strong hull property. -/
theorem not_hasStrongHullProperty_A3Tilde : ¬ HasStrongHullProperty (cayleyGraph cs3) :=
  fun h => not_hasHullProperty_A3Tilde (hasHullProperty_of_hasStrongHullProperty h)

/-- Existential form: there exists a finite-rank Coxeter system whose Cayley graph fails
both the strong hull property and the ordinary hull property. -/
theorem counterexample_exists :
    ∃ (B : Type) (M : CoxeterMatrix B),
      ¬ HasStrongHullProperty (cayleyGraph M.toCoxeterSystem) ∧
      ¬ HasHullProperty (cayleyGraph M.toCoxeterSystem) :=
  ⟨Fin 4, A3TildeMatrix, not_hasStrongHullProperty_A3Tilde, not_hasHullProperty_A3Tilde⟩

end YiboGaoCoxeterGeodesicHull
