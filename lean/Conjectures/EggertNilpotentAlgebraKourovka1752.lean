import Mathlib.Algebra.CharP.Frobenius
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Flat.Basic
/-!
# Eggert's inequality in characteristic two (Kourovka 17.52)

`kourovka_17_52_char_two` is the finite-field statement for an associative
commutative algebra without identity. The proof also works over any field of
characteristic two with surjective squaring. The generic scalar functional
is constructed over a rational function field; this extension itself is not
assumed perfect. For the written proof see the accompanying result package.
-/
namespace EggertNilpotentAlgebra

open LinearMap Module Submodule

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

private def stable (m : V →ₗ[K] V →ₗ[K] V) (S : Submodule K V) : Prop :=
  ∀ a x : V, x ∈ S → m a x ∈ S

/-- A self-adjoint nilpotent commuting action on a symmetric bilinear
space has an invariant isotropic subspace with trivial middle action. -/
private theorem isotropic_middle
    (m : V →ₗ[K] V →ₗ[K] V) (B : LinearMap.BilinForm K V)
    (hsymm : ∀ x y, B x y = B y x)
    (hadj : ∀ a x y, B (m a x) y = B x (m a y))
    (hcomm : ∀ a b, Commute (m a) (m b))
    (hnil : ∀ a, IsNilpotent (m a : Module.End K V)) :
    ∃ I : Submodule K V, B.ker ≤ I ∧ I ≤ B.orthogonal I ∧
      ∀ a x : V, x ∈ B.orthogonal I → m a x ∈ I := by
  classical
  let good := fun S : Submodule K V =>
    stable m S ∧ B.ker ≤ S ∧ S ≤ B.orthogonal S
  have hg : good B.ker := by
    refine ⟨?_, le_rfl, ?_⟩
    · intro a x hx
      apply LinearMap.ext
      intro y
      change B (m a x) y = 0
      rw [hadj]
      exact LinearMap.congr_fun (show B x = 0 from hx) _
    · intro x _ y hy
      exact LinearMap.congr_fun (show B y = 0 from hy) x
  let P := fun n : ℕ => ∃ S : Submodule K V, good S ∧ finrank K S = n
  have hex : P (Nat.findGreatest P (finrank K V)) :=
    Nat.findGreatest_spec (Submodule.finrank_le B.ker) ⟨B.ker, hg, rfl⟩
  obtain ⟨I, hI, hdI⟩ := hex
  have maximal (S : Submodule K V) (hs : good S) (hIS : I ≤ S) : S ≤ I := by
    apply (Submodule.eq_of_le_of_finrank_le hIS ?_).ge
    rw [hdI]
    exact Nat.le_findGreatest (Submodule.finrank_le S) (show P (finrank K S) from ⟨S, hs, rfl⟩)
  let J := B.orthogonal I
  have hJ : stable m J := by
    intro a x hx i hi
    rw [← hadj]
    exact hx _ (hI.1 a i hi)
  have pow_mem (a : V) (n : ℕ) {x : V} (hx : x ∈ J) : (m a ^ n) x ∈ J := by
    induction n with
    | zero => simpa using hx
    | succ n ih => simpa only [pow_succ', Module.End.mul_apply] using hJ a _ ih
  have adjpow (a : V) (n : ℕ) (x y : V) :
      B ((m a ^ n) x) y = B x ((m a ^ n) y) := by
    induction n generalizing x y with
    | zero => simp
    | succ n ih =>
      calc
        _ = B ((m a ^ n) x) (m a y) := by rw [pow_succ', Module.End.mul_apply, hadj]
        _ = B x ((m a ^ n) (m a y)) := ih x _
        _ = _ := by rw [pow_succ, Module.End.mul_apply]
  refine ⟨I, hI.2.1, hI.2.2, ?_⟩
  intro a
  let f : Module.End K V := m a
  -- If f^(2j) sends the perpendicular into I, then already f^j does:
  -- otherwise the image extends I as an invariant totally isotropic subspace.
  have halve (j : ℕ) (h2 : ∀ x ∈ J, (f ^ (j+j)) x ∈ I) :
      ∀ x ∈ J, (f ^ j) x ∈ I := by
    let U := J.map (f ^ j)
    have hU : stable m U := by
      rintro b _ ⟨x, hx, rfl⟩
      refine ⟨m b x, hJ b x hx, ?_⟩
      exact LinearMap.congr_fun ((hcomm b a).pow_right j).eq.symm x
    have uj : U ≤ J := by rintro _ ⟨x, hx, rfl⟩; exact pow_mem a j hx
    have ui : U ≤ B.orthogonal U := by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      change B ((m a ^ j) y) ((m a ^ j) x) = 0
      rw [adjpow, hsymm]
      apply hy
      simpa only [f, pow_add, Module.End.mul_apply] using h2 x hx
    have gsup : good (I ⊔ U) := by
      refine ⟨?_, le_trans hI.2.1 le_sup_left, ?_⟩
      · intro b z hz
        obtain ⟨i, hi, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
        rw [map_add]
        exact Submodule.add_mem_sup (hI.1 b i hi) (hU b u hu)
      · intro z hz w hw
        obtain ⟨i, hi, u, hu, rfl⟩ := Submodule.mem_sup.mp hz
        obtain ⟨i', hi', u', hu', rfl⟩ := Submodule.mem_sup.mp hw
        have a₁ := hI.2.2 hi i' hi'
        have a₂ := uj hu i' hi'
        have a₃ : B u' i = 0 := by rw [hsymm]; exact uj hu' i hi
        have a₄ := ui hu u' hu'
        simp only [map_add, LinearMap.add_apply, a₁, a₂, a₃, a₄, add_zero]
    intro x hx
    exact maximal _ gsup le_sup_left ((show U ≤ I ⊔ U from le_sup_right) (show (f ^ j) x ∈ U from ⟨x, hx, rfl⟩))
  have descend (j : ℕ) (h : ∀ x ∈ J, (f ^ (2^j)) x ∈ I) : ∀ x ∈ J, f x ∈ I := by
    induction j with
    | zero => simpa using h
    | succ j ih =>
      apply ih
      apply halve
      simpa only [pow_succ, Nat.mul_two] using h
  obtain ⟨j, hj⟩ := hnil a
  apply descend j
  have hf : f ^ (2^j) = 0 := pow_eq_zero_of_le (by exact Nat.le_of_lt (Nat.lt_two_pow_self)) hj
  simp [hf]

/-- Span-rank, not cardinality of the image: the scalar map need not be surjective. -/
private theorem square_span_bound {σ : K →+* K} (q : V →ₛₗ[σ] V)
    (J N : Submodule K V) (h : ∀ x ∈ J, q x ∈ N) :
    finrank K (span K (Set.range q)) + finrank K J ≤ finrank K V + finrank K N := by
  classical
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl J
  let e := Module.finBasis K D
  let S := span K (Set.range (fun i => q ((e i : D) : V)))
  have hgen : (⊤ : Submodule K D) ≤ S.comap (q.domRestrict D) := by
    rw [← e.span_eq, span_le]
    rintro _ ⟨i, rfl⟩
    exact subset_span ⟨i, rfl⟩
  have incl : span K (Set.range q) ≤ N ⊔ S := by
    apply span_le.mpr
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ J ⊔ D := hD.sup_eq_top ▸ Submodule.mem_top
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add]
    exact Submodule.add_mem_sup (h u hu) (hgen (Submodule.mem_top : (⟨w, hw⟩ : D) ∈ ⊤))
  have hd : finrank K S ≤ finrank K D := by
    simpa only [S, Set.finrank, Fintype.card_fin] using
      (finrank_range_le_card (R := K) (fun i => q ((e i : D) : V)))
  have hJD := Submodule.finrank_sup_add_finrank_inf_eq J D
  rw [hD.sup_eq_top, hD.inf_eq_bot, finrank_bot, finrank_top, add_zero] at hJD
  have hNS := Submodule.finrank_sup_add_finrank_inf_eq N S
  have hi := Submodule.finrank_mono incl
  omega

variable [CharP K 2]

private def squareMap (m : V →ₗ[K] V →ₗ[K] V) (hc : ∀ x y, m x y = m y x) :
    V →ₛₗ[frobenius K 2] V where
  toFun x := m x x
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, hc y x]
    have h : m x y + m x y = 0 := by
      rw [← two_smul K, show (2 : K) = 0 by simpa using CharP.cast_eq_zero K 2, zero_smul]
    calc
      _ = (m x y + m x y) + (m x x + m y y) := by abel
      _ = _ := by rw [h, zero_add]
  map_smul' a x := by
    change m (a • x) (a • x) = a ^ 2 • m x x
    simp only [map_smul, smul_apply, smul_smul, pow_two]


/-- Core bound over a field where one scalar functional detects zero
squares. The application constructs such a field; it is typically imperfect. -/
theorem bound_of_square_test
    (m : V →ₗ[K] V →ₗ[K] V) (hc : ∀ x y, m x y = m y x)
    (ha : ∀ x y z, m (m x y) z = m x (m y z))
    (hn : ∀ x, IsNilpotent (m x : Module.End K V))
    (l : V →ₗ[K] K) (hdet : ∀ x, l (m x x) = 0 → m x x = 0) :
    2 * finrank K (span K (Set.range fun x : V => m x x)) ≤ finrank K V := by
  let B : LinearMap.BilinForm K V := m.compr₂ l
  have hs : ∀ x y, B x y = B y x := fun x y => congrArg l (hc x y)
  have hb : ∀ a x y, B (m a x) y = B x (m a y) := by
    intro a x y
    change l (m (m a x) y) = l (m x (m a y))
    rw [hc a x, ha]
  have commute (a b : V) : Commute (m a) (m b) := by
    ext x
    change m a (m b x) = m b (m a x)
    rw [← ha, hc a b, ha]
  obtain ⟨I, hN, hi, hm⟩ := isotropic_middle m B hs hb commute hn
  let J := B.orthogonal I
  let q := squareMap m hc
  have hI : ∀ x ∈ I, q x ∈ (⊥ : Submodule K V) := by
    intro x hx
    exact hdet x (hi hx x hx)
  have hJ : ∀ x ∈ J, q x ∈ B.ker := by
    intro x hx
    ext a
    change l (m (m x x) a) = 0
    rw [ha, hc x (m x a), hc x a]
    exact hx _ (hm a x hx)
  have h1 := square_span_bound q I ⊥ hI
  have h2 := square_span_bound q J B.ker hJ
  have h3 := LinearMap.BilinForm.finrank_add_finrank_orthogonal' (B := B) I
  rw [inf_eq_right.mpr hN] at h3
  rw [finrank_bot, add_zero] at h1
  change finrank K I + finrank K J = _ at h3
  change 2 * finrank K (span K (Set.range q)) ≤ finrank K V
  omega

end EggertNilpotentAlgebra

namespace EggertNilpotentAlgebra
open TensorProduct LinearMap Module
open LinearMap (BilinMap)

variable {k L V : Type*} [Field k] [Field L] [Algebra k L]
  [AddCommGroup V] [Module k V]

private theorem mul_baseChange_assoc (m : BilinMap k V V)
    (ha : ∀ x y z, m (m x y) z = m x (m y z)) :
    ∀ x y z : L ⊗[k] V, m.baseChange L (m.baseChange L x y) z =
      m.baseChange L x (m.baseChange L y z) := by
  intro x y z
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [map_add, LinearMap.add_apply, hx, hx']
  | tmul a v =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [map_add, LinearMap.add_apply, hy, hy']
    | tmul b w =>
      induction z using TensorProduct.inductionOn with
      | add z z' hz hz' => simp only [map_add, hz, hz']
      | tmul c u => simp only [BilinMap.baseChange_tmul, mul_assoc, ha]

private theorem mul_baseChange_nil (m : BilinMap k V V)
    (hc : ∀ x y, m x y = m y x) (ha : ∀ x y z, m (m x y) z = m x (m y z))
    (hn : ∀ x, IsNilpotent (m x : Module.End k V)) :
    ∀ x : L ⊗[k] V, IsNilpotent (m.baseChange L x : Module.End L _) := by
  let M := m.baseChange L
  have ha' : ∀ x y z, M (M x y) z = M x (M y z) := mul_baseChange_assoc m ha
  have hc' : ∀ x y, M x y = M y x := BilinMap.baseChange_isSymm hc
  intro x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    have comm : Commute (M x) (M y) := by
      apply LinearMap.ext
      intro z
      change M x (M y z) = M y (M x z)
      rw [← ha', hc' x y, ha']
    rw [map_add]
    exact comm.isNilpotent_add hx hy
  | tmul a v =>
    obtain ⟨n, hn⟩ := hn v
    refine ⟨n, ?_⟩
    have hp (j : ℕ) (c : L) (u : V) :
        ((M (a ⊗ₜ[k] v)) ^ j) (c ⊗ₜ[k] u) = (a^j*c) ⊗ₜ[k] ((m v)^j) u := by
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih]
        simp only [M, BilinMap.baseChange_tmul, pow_succ', Module.End.mul_apply, mul_assoc]
    apply LinearMap.ext
    intro z
    change (M (a ⊗ₜ[k] v)^n) z = 0
    induction z using TensorProduct.inductionOn with
    | add z w hz hw => simp [hz, hw]
    | tmul c u => simp [hp, hn]

end EggertNilpotentAlgebra

namespace EggertNilpotentAlgebra
open scoped BigOperators nonZeroDivisors
open MvPolynomial

/-- The coordinate variables are linearly independent over the squares of the fraction field.
Clear denominators, then differentiate with respect to a single variable. -/
private theorem generic_square_separation
    {k ι : Type*} [Field k] [CharP k 2] [Fintype ι]
    (c : ι → FractionRing (MvPolynomial ι k))
    (h : ∑ j, algebraMap _ (FractionRing (MvPolynomial ι k)) (X j : MvPolynomial ι k) *
      c j ^ 2 = 0) (i : ι) : c i = 0 := by
  classical
  let P := MvPolynomial ι k
  let L := FractionRing P
  let f := algebraMap P L
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite P⁰ c
  change ∀ j, ∃ u : P, f u = (b : P) • c j at hb
  choose u hu using hb
  have hf : Function.Injective f := IsFractionRing.injective P L
  have hsum : (∑ j, (X j : P) * u j ^ 2) = 0 := by
    apply hf
    rw [map_zero, map_sum]
    calc
      _ = f (b : P) ^ 2 * ∑ j, f (X j) * c j ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [map_mul, map_pow, hu, Algebra.smul_def]
        ring
      _ = 0 := by rw [show (∑ j, f (X j) * c j ^ 2) = 0 from h, mul_zero]
  have hd := congrArg (pderiv i : P → P) hsum
  have htwo : (2 : P) = 0 := by
    simpa only [map_ofNat, map_zero] using congrArg (MvPolynomial.C : k →+* P) (show (2 : k) = 0 by simpa using CharP.cast_eq_zero k 2)
  have hd' : u i ^ 2 = 0 := by
    simpa [map_sum, pderiv_mul, pderiv_pow, Pi.single_apply, htwo] using hd
  have hu0 : u i = 0 := (mul_eq_zero.mp (by simpa only [pow_two] using hd')).elim id id
  have hx := hu i
  rw [hu0, map_zero, Algebra.smul_def] at hx
  have hbf : f (b : P) ≠ 0 := fun e => nonZeroDivisors.ne_zero b.property (hf (e.trans f.map_zero.symm))
  exact (mul_eq_zero.mp hx.symm).resolve_left hbf

end EggertNilpotentAlgebra

namespace EggertNilpotentAlgebra
open LinearMap Module Submodule
open scoped TensorProduct BigOperators
private theorem coords_of_extended_square
    {k L V ι : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup V] [Module k V] [CharP k 2] [CharP L 2]
    (b : Basis ι k V) (hp : ∀ x : k, ∃ y : k, y^2 = x)
    (m : V →ₗ[k] V →ₗ[k] V)
    (hs : ∀ x y, (LinearMap.BilinMap.baseChange L m) x y = (LinearMap.BilinMap.baseChange L m) y x)
    (z : L ⊗[k] V) (i : ι) :
    ∃ a : L, ((b.baseChange L).repr ((LinearMap.BilinMap.baseChange L m) z z)) i = a^2 := by
  let b' := b.baseChange L
  let q := squareMap ((LinearMap.BilinMap.baseChange L m)) hs
  change ∃ a : L, b'.repr (q z) i = a^2
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
    obtain ⟨u, hu⟩ := hp ((b.repr (m x x)) i)
    refine ⟨algebraMap k L u * a, ?_⟩
    change b'.repr ((LinearMap.BilinMap.baseChange L m) (a ⊗ₜ[k] x) (a ⊗ₜ[k] x)) i = _
    simp only [b', LinearMap.BilinMap.baseChange_tmul, Module.Basis.baseChange_repr_tmul,
      Algebra.smul_def, ← hu, pow_two, map_mul]
    ring
  | add u v hu hv =>
    obtain ⟨a,ha⟩ := hu
    obtain ⟨c,hc⟩ := hv
    refine ⟨a+c, ?_⟩
    simp only [map_add, Finsupp.add_apply, ha, hc]
    exact ((frobenius L 2).map_add a c).symm

private lemma scalar_dim (k L W : Type*) [Field k] [Field L] [Algebra k L]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] :
    finrank L (L ⊗[k] W) = finrank k W := by
  classical
  simpa only [Fintype.card_fin] using
    (Module.finrank_eq_card_basis ((Module.finBasis k W).baseChange L))

private lemma rank_of_base_squares
    {k L W : Type*} [Field k] [Field L] [Algebra k L]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (m : W →ₗ[k] W →ₗ[k] W) :
    finrank k (span k (Set.range (fun x : W => m x x))) ≤
    finrank L (span L (Set.range (fun x : L ⊗[k] W => (LinearMap.BilinMap.baseChange L m) x x))) := by
  let S := span k (Set.range (fun x : W => m x x))
  have h : S.baseChange L ≤
      span L (Set.range (fun x : L ⊗[k] W => (LinearMap.BilinMap.baseChange L m) x x)) := by
    dsimp only [S]
    rw [Submodule.baseChange_span, span_le]
    rintro _ ⟨_, ⟨v,rfl⟩,rfl⟩
    apply subset_span
    exact ⟨1 ⊗ₜ[k] v, by simp⟩
  calc finrank k S = finrank L (L ⊗[k] S) := (scalar_dim k L S).symm
       _ = finrank L (S.baseChange L) := (Submodule.toBaseChange.toLinearEquiv L S).finrank_eq
       _ ≤ _ := Submodule.finrank_mono h
/-- Over a field with surjective squaring the set of squares already is
the subspace whose finrank occurs in the inequality. -/
theorem square_span_carrier
    {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    (hp : ∀ a : k, ∃ u : k, u^2 = a)
    (m : V →ₗ[k] V →ₗ[k] V) (hc : ∀ x y, m x y = m y x) :
    (↑(span k (Set.range fun x : V => m x x)) : Set V) =
      Set.range (fun x : V => m x x) := by
  let q := squareMap m hc
  let S : Submodule k V :=
    { carrier := Set.range q
      zero_mem' := ⟨0, map_zero q⟩
      add_mem' := by
        rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩
        exact ⟨x+y, q.map_add x y⟩
      smul_mem' := by
        rintro a _ ⟨x,rfl⟩
        obtain ⟨u,rfl⟩ := hp a
        exact ⟨u • x, q.map_smulₛₗ u x⟩ }
  change (↑(span k (S : Set V)) : Set V) = (S : Set V)
  rw [Submodule.span_eq]

private theorem bound_after_extension
    {k L V ι : Type*} [Field k] [Field L] [Algebra k L] [CharP L 2] [Fintype ι] [CharP k 2] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hp : ∀ a : k, ∃ u : k, u^2 = a)
    (m : V →ₗ[k] V →ₗ[k] V) (hc : ∀ x y, m x y = m y x)
    (ha : ∀ x y z, m (m x y) z = m x (m y z))
    (hn : ∀ x, IsNilpotent (m x : Module.End k V))
    (b : Basis ι k V) (t : ι → L)
    (sep : ∀ c : ι → L, (∑ i, t i * (c i)^2) = 0 → ∀ i, c i = 0) :
    2 * finrank k (span k (Set.range fun v : V => m v v)) ≤ finrank k V := by
  classical
  let b' := b.baseChange L
  let l : (L ⊗[k] V) →ₗ[L] L := b'.constr L t
  let m' := LinearMap.BilinMap.baseChange L m
  have hc' : ∀ x y, m' x y = m' y x := LinearMap.BilinMap.baseChange_isSymm hc
  have ha' : ∀ x y z, m' (m' x y) z = m' x (m' y z) := by
    exact mul_baseChange_assoc m ha
  have hn' : ∀ x, IsNilpotent (m' x : Module.End L (L ⊗[k] V)) := by
    exact mul_baseChange_nil m hc ha hn
  have det : ∀ x, l (m' x x) = 0 → m' x x = 0 := by
    intro x hx
    choose a h using coords_of_extended_square b hp m hc' x
    have eqn : ∑ i, t i * (a i)^2 = 0 := by
      change (b'.constr L t) (m' x x) = 0 at hx
      rw [Basis.constr_apply_fintype] at hx
      simpa only [Basis.equivFun_apply, b', m', h, smul_eq_mul, mul_comm] using hx
    have h0 : ∀ i, a i = 0 := sep a eqn
    apply b'.repr.injective
    ext i
    change (b.baseChange L).repr (m' x x) i = _
    simp [m', h, h0]
  have h1 := bound_of_square_test m' hc' ha' hn' l det
  have h2 := rank_of_base_squares (L := L) m
  have h3 := scalar_dim k L V
  change 2 * finrank L (span L (Set.range (fun x : L ⊗[k] V => m' x x))) ≤ _ at h1
  change finrank k _ ≤ finrank L (span L (Set.range (fun x : L ⊗[k] V => m' x x))) at h2
  omega

/-- Eggert's dimension inequality in characteristic two.  The multiplication
is unital neither in its type nor in the nilpotence hypothesis: `hn` asks
only that each left multiplication be nilpotent, as is always the case if
all products of some common positive length are zero. -/
theorem eggert_char_two_of_surjective_square
    {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] (hp : ∀ a : k, ∃ u : k, u^2 = a)
    (m : V →ₗ[k] V →ₗ[k] V) (hc : ∀ x y, m x y = m y x)
    (ha : ∀ x y z, m (m x y) z = m x (m y z))
    (hn : ∀ x, IsNilpotent (m x : Module.End k V)) :
    2 * finrank k (span k (Set.range fun v : V => m v v)) ≤ finrank k V := by
  classical
  let ι := Fin (finrank k V)
  let P := MvPolynomial ι k
  let L := FractionRing P
  let phi : k →+* L := (algebraMap P L).comp MvPolynomial.C
  let : Algebra k L := phi.toAlgebra
  let : CharP L 2 := ⟨fun n => by
    calc ((n : L) = 0) ↔ (phi (n:k) = phi 0) := by simp
         _ ↔ (n:k) = 0 := phi.injective.eq_iff
         _ ↔ 2 ∣ n := CharP.cast_eq_zero_iff k 2 n⟩
  let b : Basis ι k V := Module.finBasis k V
  let t : ι → L := fun i => algebraMap P L (MvPolynomial.X i)
  exact bound_after_extension hp m hc ha hn b t (fun c h => generic_square_separation c h)

/-- The characteristic-two case of Kourovka 17.52, for actual finite
fields and non-unital algebras whose products vanish in sufficiently
large length. The range-span is exactly the square subalgebra over a finite field. -/
theorem kourovka_17_52_char_two
    {k R : Type*} [Field k] [Finite k] [CharP k 2] [NonUnitalCommRing R]
    [Module k R] [IsScalarTower k R R] [SMulCommClass k R R] [FiniteDimensional k R]
    (hnil : ∃ n : ℕ, ∀ l : List R, n ≤ l.length → ∀ y : R, l.foldr (· * ·) y = 0) :
    2 * finrank k (span k (Set.range fun v : R => v * v)) ≤ finrank k R := by
  let m := LinearMap.mul k R
  have hp : Function.Surjective (frobenius k 2) :=
    Finite.surjective_of_injective (frobenius k 2).injective
  apply eggert_char_two_of_surjective_square (V := R) (k := k) hp m mul_comm mul_assoc
  obtain ⟨n,hn⟩ := hnil
  intro x
  refine ⟨n, LinearMap.ext fun y => ?_⟩
  have eqn (j : ℕ) : (m x ^ j) y = (List.replicate j x).foldr (· * ·) y := by
    induction j with
    | zero => simp
    | succ j ih => simp [pow_succ', Module.End.mul_apply, List.replicate_succ, ih, m]
  exact (eqn n).trans (hn _ (by simp) y)
end EggertNilpotentAlgebra

