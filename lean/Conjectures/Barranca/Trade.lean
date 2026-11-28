import Conjectures.Barranca.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! The cubelike host and the integral-spectrum trade for cliques and stars. -/
namespace Barranca

open SimpleGraph Matrix Polynomial Finset
open scoped Classical BigOperators
set_option linter.unusedSimpArgs false

noncomputable section

theorem cp_zeroG (n : ℕ) : cp (zeroG n) = X ^ n := by
  unfold zeroG
  rw [cp_pack]
  simp

theorem cp_clq (p : ℕ) : cp (clq (p+1)) = (X - C (p : ℤ)) * (X+1)^p := by
  let u : Fin (p+1) → ℤ := fun _ => 1
  have h : (completeGraph (Fin (p+1))).adjMatrix ℤ =
      Matrix.vecMulVec u u - Matrix.scalar _ 1 := by
    rw [SimpleGraph.adjMatrix_completeGraph_eq_of_one_sub_one]
    simp [u, Matrix.vecMulVec]
    rfl
  unfold clq
  rw [cp_pack]
  rw [h, Matrix.charpoly_sub_scalar, Matrix.charpoly_vecMulVec]
  simp [u, dotProduct, Polynomial.smul_eq_C_mul, pow_succ]
  ring

/-- Compress the complete bipartite adjacency matrix to its two part indicators. -/
theorem cp_bic (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    cp (bic a b) = X^(a+b-2) * (X^2 - C ((a : ℤ)*b)) := by
  let U : Matrix (Fin a ⊕ Fin b) (Fin 2) ℤ := fun i => Sum.elim (fun _ => ![1,0]) (fun _ => ![0,1]) i
  let V : Matrix (Fin 2) (Fin a ⊕ Fin b) ℤ :=
    fun i j => Sum.elim (fun _ => ![0,1] i) (fun _ => ![1,0] i) j
  have hUV : (completeBipartiteGraph (Fin a) (Fin b)).adjMatrix ℤ = U*V := by
    ext (i|i) (j|j) <;> rw [Matrix.mul_apply, SimpleGraph.adjMatrix_apply] <;> simp [U,V, Fin.sum_univ_two,
      SimpleGraph.adjMatrix_apply, completeBipartiteGraph]
  have hVU : V*U = !![0,(b : ℤ);(a : ℤ),0] := by
    ext i j
    rw [Matrix.mul_apply]
    fin_cases i <;> fin_cases j <;> simp [U,V, Fintype.sum_sum_type]
  unfold bic
  rw [cp_pack]
  rw [hUV, Matrix.charpoly_mul_comm_of_le, hVU]
  · simp only [Fintype.card_sum, Fintype.card_fin]
    congr 1
    simp [Matrix.charpoly, Matrix.charmatrix, Matrix.det_fin_two, Matrix.one_apply]
    ring
  · simp; omega


section Cube

variable {ι : Type} [Fintype ι] [DecidableEq ι]
abbrev Cube (ι : Type) := ι → ZMod 2

def bit (i : ι) : Cube ι := fun j => if i = j then 1 else 0

theorem twice (x : Cube ι) : x+x = 0 := by
  funext i
  change x i + x i = 0
  generalize x i = t
  fin_cases t <;> decide

def steps (H : SimpleGraph ι) : Finset (Cube ι) :=
  univ.filter fun s => ∃ i j, H.Adj i j ∧ s = bit i + bit j

@[simp] theorem mem_steps {H : SimpleGraph ι} {s : Cube ι} :
    s ∈ steps H ↔ ∃ i j, H.Adj i j ∧ s = bit i + bit j := by simp [steps]

theorem no_zero (H : SimpleGraph ι) : 0 ∉ steps H := by
  rintro hh
  obtain ⟨i,j,hij,h⟩ := mem_steps.mp hh
  have hi := congrFun h i
  simp [bit,hij.ne.symm] at hi

def cubeGraph (H : SimpleGraph ι) : SimpleGraph (Cube ι) where
  Adj x y := x+y ∈ steps H
  symm := ⟨fun {x y} h => add_comm x y ▸ h⟩
  loopless := ⟨fun x => by rw [twice]; exact no_zero H⟩

theorem bit_inj : Function.Injective (bit (ι := ι)) := by
  intro i j h
  by_contra hn
  have := congrFun h i
  simp [bit, Ne.symm hn] at this

def intoCube (H : SimpleGraph ι) : H ↪g cubeGraph H where
  toFun := bit
  inj' := bit_inj
  map_rel_iff' := by
    intro i j
    change bit i + bit j ∈ steps H ↔ H.Adj i j
    constructor
    · intro hm
      obtain ⟨u,v,huv,hh⟩ := mem_steps.mp hm
      have hou : u=i ∨ u=j := by
        by_contra! hn
        have h := congrFun hh u
        simp [bit, hn.1.symm, hn.2.symm, huv.ne.symm] at h
      have hov : v=i ∨ v=j := by
        by_contra! hn
        have h := congrFun hh v
        simp [bit, hn.1.symm, hn.2.symm, huv.ne] at h
      rcases hou with rfl|rfl <;> rcases hov with rfl|rfl <;> first | exact huv | exact huv.symm | exact (huv.ne rfl).elim
    · intro h; exact mem_steps.mpr ⟨i,j,h,rfl⟩

def w0 (a b : ZMod 2) : ℤ := if a = 1 ∧ b = 1 then -1 else 1
def walsh (a b : Cube ι) : ℤ := ∏ i, w0 (a i) (b i)

theorem w0_add (a b c : ZMod 2) : w0 (a+b) c = w0 a c * w0 b c := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> decide

theorem walsh_add (a b c : Cube ι) : walsh (a+b) c = walsh a c * walsh b c := by
  simp [walsh, Pi.add_apply, w0_add, Finset.prod_mul_distrib]

theorem w0_sq (a b : ZMod 2) :
    ∑ t : ZMod 2, w0 a t * w0 t b = if a=b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;> decide

theorem walsh_sq (a b : Cube ι) :
    ∑ x, walsh a x * walsh x b = if a=b then (2:ℤ)^Fintype.card ι else 0 := by
  simp only [walsh, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun (i : ι) (t : ZMod 2) => w0 (a i) t * w0 t (b i))]
  simp only [w0_sq]
  by_cases h : a=b
  · subst b; simp
  · obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by simpa [funext_iff] using h
    rw [if_neg h]
    apply Finset.prod_eq_zero (mem_univ i)
    simp [hi]

def cubeEig (H : SimpleGraph ι) (b : Cube ι) : ℤ := ∑ s ∈ steps H, walsh s b

theorem cube_conjugacy (H : SimpleGraph ι) :
    ((cubeGraph H).adjMatrix ℤ).charpoly = (Matrix.diagonal (cubeEig H)).charpoly := by
  let W : Matrix (Cube ι) (Cube ι) ℤ := walsh
  have hW : W*W = Matrix.scalar _ ((2:ℤ)^Fintype.card ι) := by
    ext a b
    rw [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
    exact walsh_sq a b
  have hdet : W.det ≠ 0 := by
    intro hn
    have hh := congrArg Matrix.det hW
    rw [Matrix.det_mul, hn, zero_mul, Matrix.scalar_apply, Matrix.det_diagonal] at hh
    exact (Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ (by decide : (2:ℤ) ≠ 0))) hh.symm
  apply Matrix.charpoly_eq_of_mul_eq_mul (P := W) hdet
  ext a b
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have hentry (x : Cube ι) : (cubeGraph H).adjMatrix ℤ a x = if a+x ∈ steps H then 1 else 0 := by
    unfold SimpleGraph.adjMatrix
    dsimp only [Matrix.of_apply]
    split <;> split <;> simp_all only [cubeGraph, not_true_eq_false]
  simp_rw [hentry]
  change (∑ x : Cube ι, (if a+x ∈ steps H then (1:ℤ) else 0) * walsh x b) =
    walsh a b * cubeEig H b
  have tr (x : Cube ι) : a+(a+x) = x := by rw [← add_assoc, twice, zero_add]
  calc
    _ = ∑ x : Cube ι, if a+x ∈ steps H then walsh (a+(a+x)) b else 0 := by
      simp [tr, ite_mul]
    _ = ∑ x : Cube ι, if x ∈ steps H then walsh (a+x) b else 0 :=
      Equiv.sum_comp (Equiv.addLeft a) (fun x => if x ∈ steps H then walsh (a+x) b else 0)
    _ = _ := by simp only [walsh_add, cubeEig, Finset.mul_sum, ← Finset.sum_filter, filter_mem_eq_inter, univ_inter]

theorem cube_charpoly (H : SimpleGraph ι) :
    ((cubeGraph H).adjMatrix ℤ).charpoly = ∏ b : Cube ι, (X-C (cubeEig H b)) := by
  rw [cube_conjugacy, Matrix.charpoly_diagonal]

theorem cubeEig_sum (H : SimpleGraph ι) : ∑ b : Cube ι, cubeEig H b = 0 := by
  have h := congrArg (fun p : ℤ[X] => -p.nextCoeff) (cube_conjugacy H)
  rw [← Matrix.trace_eq_neg_charpoly_nextCoeff, ← Matrix.trace_eq_neg_charpoly_nextCoeff] at h
  simpa [Matrix.trace, SimpleGraph.adjMatrix_apply] using h.symm

end Cube

/-- Disjoint unions of cliques, stars and isolates. -/
inductive Pieces : Graph → Prop
  | isolated (n : ℕ) : Pieces (zeroG n)
  | clique (n : ℕ) : Pieces (clq n)
  | star (n : ℕ) : Pieces (bic 1 n)
  | sum {A B} : Pieces A → Pieces B → Pieces (A ⊞ B)

theorem one_trade (z : ℤ) : ∃ L R : Graph, Pieces R ∧
    (X-C z) * cp L * (X+1)^z.toNat = cp R * (X+1)^(-z).toNat := by
  cases z with
  | ofNat n =>
    refine ⟨zeroG 0, clq (n+1), .clique _, ?_⟩
    simp [cp_zeroG, cp_clq]
  | negSucc n =>
    let r := n+1
    have hr : 0 < r := by dsimp [r]; omega
    have hs : 0 < r^2 := pow_pos hr _
    refine ⟨clq (r+1) ⊞ zeroG (r^2-1), bic 1 (r^2), .star _, ?_⟩
    rw [cp_plus, cp_zeroG, cp_clq, cp_bic _ _ (by decide) hs]
    have hh : 1+r^2-2 = r^2-1 := by omega
    rw [hh]
    change (X-C (Int.negSucc n)) * ((X-C (r : ℤ)) * (X+1)^r * X^(r^2-1)) *
      (X+1)^0 = X^(r^2-1) * (X^2 - C ((1:ℤ)*↑(r^2))) * (X+1)^r
    have hz : (Int.negSucc n) = -(r:ℤ) := by simp [r, Int.negSucc_eq]
    rw [hz]
    push_cast
    simp only [one_mul, map_neg, map_pow]
    ring

theorem trade_finset {κ : Type} (s : Finset κ) (e : κ → ℤ) :
    ∃ L R : Graph, Pieces R ∧
      (∏ i ∈ s, (X-C (e i))) * cp L * (X+1)^(∑ i ∈ s, (e i).toNat) =
        cp R * (X+1)^(∑ i ∈ s, (-e i).toNat) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨zeroG 0, zeroG 0, .isolated _, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨L,R,hR,h⟩ := ih
    obtain ⟨l,r,hr,h'⟩ := one_trade (e i)
    refine ⟨l ⊞ L,r ⊞ R,.sum hr hR,?_⟩
    simp only [prod_insert hi, sum_insert hi, cp_plus, pow_add]
    linear_combination (∏ j ∈ s, (X-C (e j))) * cp L * (X+1)^(∑ j ∈ s, (e j).toNat) * h' +
      cp r * (X+1)^(-e i).toNat * h

/-- Spectral synthesis: move finitely many clique and zero blocks to the host
side; the other side consists only of cliques, stars and isolates. -/
theorem integral_trade {κ : Type} [Fintype κ] (G : Graph) (e : κ → ℤ)
    (hc : cp G = ∏ i, (X-C (e i))) (he : ∑ i, e i = 0) :
    ∃ L R : Graph, Pieces R ∧ cp (G ⊞ L) = cp R := by
  obtain ⟨L,R,hR,h⟩ := trade_finset univ e
  refine ⟨L,R,hR,?_⟩
  have hz : ∑ i, (e i).toNat = ∑ i, (-e i).toNat := by
    have h1 : (∑ i, (((e i).toNat : ℕ) : ℤ)) - ∑ i, (((-e i).toNat : ℕ) : ℤ) = 0 := by
      rw [← Finset.sum_sub_distrib, ← he]
      apply Finset.sum_congr rfl
      intro x _
      omega
    exact_mod_cast sub_eq_zero.mp h1
  rw [← hc, hz] at h
  rw [cp_plus]
  exact mul_right_cancel₀ (pow_ne_zero _ (by exact X_add_C_ne_zero (1:ℤ))) h

/-- Every finite graph is an induced subgraph of one member of an adjacency-
cospectral pair whose other member is a union of cliques and stars. -/
theorem universal_pair (H : Graph) :
    ∃ A B : Graph, Has H A ∧ cp A = cp B ∧ Pieces B := by
  let G := pack _ (cubeGraph H.gr)
  have hcp : cp G = ∏ b, (X-C (cubeEig H.gr b)) := by
    unfold G
    rw [cp_pack, cube_charpoly]
  obtain ⟨L,R,hR,h⟩ := integral_trade G (cubeEig H.gr) hcp (cubeEig_sum _)
  refine ⟨G ⊞ L,R,?_,h,hR⟩
  exact ⟨(SimpleGraph.Embedding.sumInl : G.gr ↪g G.gr ⊕g L.gr).comp (intoCube H.gr)⟩

theorem rs_embeds_in_pieces (H : Graph) (hr : RS H) : ∃ B : Graph, Pieces B ∧ Has H B := by
  obtain ⟨A,B,hA,h,hB⟩ := universal_pair H
  exact ⟨B,hB,(hr A B h).mp hA⟩


end
end Barranca
