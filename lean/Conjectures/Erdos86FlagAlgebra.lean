import Mathlib

/-!
# Cubical edge sets and the face incidence count

A vertex is a Boolean word. For counting we identify it with its support; an
edge is then indexed *once*, by its direction and the support of its lower
endpoint (which does not contain that direction). A face fixes the coordinates
in `S`, setting exactly `b ⊆ S` of them to true.
-/

namespace Erdos86FlagAlgebra

abbrev Vertex (n : ℕ) := Fin n → Bool

def vertexOfSupport {n : ℕ} (u : Finset (Fin n)) : Vertex n :=
  fun i => decide (i ∈ u)

def supportEquiv (n : ℕ) : Finset (Fin n) ≃ Vertex n where
  toFun := vertexOfSupport
  invFun x := Finset.univ.filter (fun i => x i = true)
  left_inv u := by ext i; simp [vertexOfSupport]
  right_inv x := by funext i; cases h : x i <;> simp [vertexOfSupport, h]

/-- The endpoints differ in exactly one coordinate. -/
def Adj {n : ℕ} (x y : Vertex n) : Prop := ∃! i, x i ≠ y i

abbrev EdgeCode (n : ℕ) := Fin n × Finset (Fin n)
abbrev Graph (n : ℕ) := Finset (EdgeCode n)

/-- The legal edge codes of the undirected hypercube. -/
def cubeEdges (n : ℕ) : Graph n := Finset.univ.filter fun e => e.1 ∉ e.2

@[simp] theorem mem_cubeEdges {n : ℕ} {e : EdgeCode n} :
    e ∈ cubeEdges n ↔ e.1 ∉ e.2 := by simp [cubeEdges]

theorem adjacent_endpoints {n : ℕ} {i : Fin n} {u : Finset (Fin n)} (h : i ∉ u) :
    Adj (vertexOfSupport u) (vertexOfSupport (insert i u)) := by
  refine ⟨i, ?_, ?_⟩
  · simp [vertexOfSupport, h]
  · intro j hj
    by_contra hji
    simp [vertexOfSupport, hji] at hj

/-- A square with lower corner `u` and independent directions `i,j`. -/
def HasSquare {n : ℕ} (G : Graph n) (u : Finset (Fin n)) (i j : Fin n) : Prop :=
  i ≠ j ∧ (i, u) ∈ G ∧ (j, u) ∈ G ∧
    (i, insert j u) ∈ G ∧ (j, insert i u) ∈ G

/-- A subgraph of the actual cube with no complete two-dimensional face. -/
def IsC4Free {n : ℕ} (G : Graph n) : Prop :=
  G ⊆ cubeEdges n ∧ ∀ u i j, ¬ HasSquare G u i j

abbrev edgeCount {n : ℕ} (G : Graph n) := G.card
def totalEdges (n : ℕ) := n * 2 ^ (n - 1)
def edgeDensity {n : ℕ} (G : Graph n) : ℚ := G.card / (totalEdges n : ℚ)

noncomputable def exC4 (n : ℕ) : ℕ := by
  classical
  exact ((cubeEdges n).powerset.filter IsC4Free).sup Finset.card

theorem card_le_exC4 {n : ℕ} {G : Graph n} (h : IsC4Free G) : G.card ≤ exC4 n := by
  classical
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr h.1, h⟩)

theorem exC4_le {n t : ℕ} (h : ∀ G : Graph n, IsC4Free G → G.card ≤ t) : exC4 n ≤ t := by
  classical
  apply Finset.sup_le
  intro G hG
  exact h G (Finset.mem_filter.mp hG).2

/-- Edges of `G` lying wholly within the specified face, still in ambient coordinates. -/
def face {n : ℕ} (G : Graph n) (S b : Finset (Fin n)) : Graph n :=
  G.filter fun e => e.1 ∉ S ∧ e.2 ∩ S = b

theorem sum_face_fixed {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    ∑ b ∈ S.powerset, (face G S b).card = (G.filter fun e => e.1 ∉ S).card := by
  classical
  simp only [face, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hm : e.2 ∩ S ∈ S.powerset := Finset.mem_powerset.mpr Finset.inter_subset_right
  by_cases h : e.1 ∈ S <;> simp [h, hm, eq_comm (a := e.2 ∩ S)]

private theorem avoiding_subsets {n : ℕ} (i : Fin n) (k : ℕ) :
    (((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => i ∉ S).card =
      (n - 1).choose k := by
  classical
  have eqn : (((Finset.univ : Finset (Fin n)).powersetCard k).filter fun S => i ∉ S) =
        (Finset.univ.erase i).powersetCard k := by
    ext S
    simp [Finset.subset_erase, and_comm]
  rw [eqn, Finset.card_powersetCard]
  simp

/-- The exact integer subcube averaging identity (codimension `k`).
Each edge belongs to precisely `(n-1).choose k` of the faces. -/
theorem subcube_incidence {n : ℕ} (G : Graph n) (k : ℕ) :
    ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      ∑ b ∈ S.powerset, (face G S b).card = (n - 1).choose k * G.card := by
  classical
  simp_rw [sum_face_fixed]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ e ∈ G, (n - 1).choose k := by
      apply Finset.sum_congr rfl
      intro e he
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using avoiding_subsets e.1 k
    _ = _ := by simp [mul_comm]

def facet {n : ℕ} (G : Graph n) (i : Fin n) (b : Bool) :=
  face G {i} (if b then {i} else ∅)

theorem opposite_facets {n : ℕ} (G : Graph n) :
    ∑ i : Fin n, ((facet G i false).card + (facet G i true).card) = (n - 1) * G.card := by
  classical
  have h (i : Fin n) := sum_face_fixed G {i}
  have hh (i : Fin n) : (facet G i false).card + (facet G i true).card =
      (G.filter fun e => e.1 ≠ i).card := by
    have hp : ({i} : Finset (Fin n)).powerset = {∅, {i}} := by
      rw [show ({i} : Finset (Fin n)) = insert i ∅ from rfl, Finset.powerset_insert]; simp
    simpa [facet, hp, add_comm] using h i
  simp_rw [hh]
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  calc
    _ = ∑ _e ∈ G, (n - 1) := by
      apply Finset.sum_congr rfl
      intro e he
      have ha : ((Finset.univ : Finset (Fin n)).filter fun i => e.1 ≠ i) =
          Finset.univ.erase e.1 := by ext j; simp [ne_comm]
      have h' : ((Finset.univ : Finset (Fin n)).filter fun i => e.1 ≠ i).card = n - 1 := by
        rw [ha]; simp
      simpa only [Finset.card_eq_sum_ones, Finset.sum_filter] using h'
    _ = _ := by simp [mul_comm]


/-- Lift a labelled local edge to the ambient coordinates; `b` is the
set of fixed one-coordinates outside the image of `f`. -/
def liftEdge {l n : ℕ} (f : Fin l ↪ Fin n) (b : Finset (Fin n)) (e : EdgeCode l) : EdgeCode n :=
  (f e.1, b ∪ e.2.map f)

def restrict {l n : ℕ} (G : Graph n) (f : Fin l ↪ Fin n) (b : Finset (Fin n)) : Graph l :=
  (cubeEdges l).filter fun e => liftEdge f b e ∈ G

theorem restrict_free {l n : ℕ} {G : Graph n} (hG : IsC4Free G) (f : Fin l ↪ Fin n)
    (b : Finset (Fin n)) : IsC4Free (restrict G f b) := by
  classical
  constructor
  · exact Finset.filter_subset _ _
  intro u i j hs
  obtain ⟨hne, h1, h2, h3, h4⟩ := hs
  apply hG.2 (b ∪ u.map f) (f i) (f j)
  refine ⟨f.injective.ne hne, (Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2, ?_, ?_⟩
  · simpa [liftEdge, Finset.union_insert] using (Finset.mem_filter.mp h3).2
  · simpa [liftEdge, Finset.union_insert] using (Finset.mem_filter.mp h4).2

private theorem freeCoordinateMap {n : ℕ} (S : Finset (Fin n)) :
    ∃ f : Fin (n - S.card) ↪ Fin n, ∀ i, (∃ j, f j = i) ↔ i ∉ S := by
  classical
  let T := (Finset.univ : Finset (Fin n)) \ S
  have hc : Fintype.card (↥T) = n - S.card := by
    simp [T]
  let e : Fin (n - S.card) ≃ ↥T := Fintype.equivOfCardEq (by simp [hc])
  let f : Fin (n - S.card) ↪ Fin n := ⟨fun j => (e j).val, fun _ _ hh => e.injective (Subtype.ext hh)⟩
  refine ⟨f, fun i => ⟨?_, ?_⟩⟩
  · rintro ⟨j, rfl⟩
    exact (Finset.mem_sdiff.mp (e j).property).2
  · intro hi
    let v : ↥T := ⟨i, by simp [T, hi]⟩
    exact ⟨e.symm v, congrArg Subtype.val (e.apply_symm_apply v)⟩

/-- Even though `face` retains ambient labels, its edge count is bounded
by the true extremal number in its own dimension. -/
theorem face_card_le {n : ℕ} {G : Graph n} (hG : IsC4Free G) (S b : Finset (Fin n)) :
    (face G S b).card ≤ exC4 (n - S.card) := by
  classical
  obtain ⟨f, hf⟩ := freeCoordinateMap S
  apply le_trans _ (card_le_exC4 (restrict_free hG f b))
  apply le_trans _ (Finset.card_image_le (f := liftEdge f b) (s := restrict G f b))
  apply Finset.card_le_card
  rintro ⟨i, U⟩ he
  obtain ⟨heG, hi, hU⟩ := Finset.mem_filter.mp he
  obtain ⟨j, rfl⟩ := (hf i).2 hi
  let u := Finset.univ.filter fun j => f j ∈ U
  have hbase : b ∪ u.map f = U := by
    rw [← hU]
    ext t
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_map]
    constructor
    · rintro (ht | ⟨z, hz, rfl⟩)
      · exact ht.1
      · exact (Finset.mem_filter.mp hz).2
    · intro ht
      by_cases hS : t ∈ S
      · exact Or.inl ⟨ht, hS⟩
      · obtain ⟨z, rfl⟩ := (hf t).2 hS
        exact Or.inr ⟨z, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht⟩, rfl⟩
  have heq : liftEdge f b (j, u) = (f j, U) := Prod.ext rfl hbase
  apply Finset.mem_image.mpr
  refine ⟨(j, u), Finset.mem_filter.mpr ⟨mem_cubeEdges.mpr ?_, ?_⟩, heq⟩
  · intro hj
    exact mem_cubeEdges.mp (hG.1 heG) ((Finset.mem_filter.mp hj).2)
  · rwa [heq]

theorem facet_card_le {n : ℕ} {G : Graph (n+1)} (hG : IsC4Free G) (i : Fin (n+1))
    (b : Bool) : (facet G i b).card ≤ exC4 n := by
  simpa [facet] using face_card_le hG {i} (if b then {i} else ∅)

private theorem choose_balance (n k : ℕ) :
    (n - 1).choose k * n = n.choose k * (n-k) := by
  classical
  let P := (Finset.univ : Finset (Fin n)).powersetCard k
  calc
    _ = ∑ i : Fin n, ∑ S ∈ P, (if i ∉ S then 1 else 0 : ℕ) := by
      have hs (i : Fin n) : ∑ S ∈ P, (if i ∉ S then 1 else 0 : ℕ) = (n-1).choose k := by
        simpa only [P, Finset.card_eq_sum_ones, Finset.sum_filter] using avoiding_subsets i k
      simp_rw [hs]
      simp [mul_comm]
    _ = ∑ S ∈ P, ∑ i : Fin n, (if i ∉ S then 1 else 0 : ℕ) := Finset.sum_comm
    _ = ∑ _S ∈ P, (n-k) := by
      apply Finset.sum_congr rfl
      intro S hS
      have hh := (Finset.mem_powersetCard.mp hS).2
      have h' : ((Finset.univ : Finset (Fin n)) \ S).card = n-k := by
        simp [Finset.card_sdiff_of_subset, hh]
      simpa only [Finset.sdiff_eq_filter, Finset.card_eq_sum_ones, Finset.sum_filter] using h'
    _ = _ := by simp [P, Finset.card_powersetCard]

def numberFaces (n l : ℕ) := n.choose (n-l) * 2 ^ (n-l)

private theorem incidence_normalization {l n : ℕ} (hl : 1 ≤ l) (hn : l ≤ n) :
    (n - 1).choose (n-l) * totalEdges n = numberFaces n l * totalEdges l := by
  have h : n - 1 = (n-l) + (l-1) := by omega
  have h' := choose_balance n (n-l)
  rw [show n-(n-l)=l by omega] at h'
  calc
    _ = ((n-1).choose (n-l) * n) * (2^(n-l) * 2^(l-1)) := by
      unfold totalEdges; rw [← pow_add, ← h]; ring
    _ = _ := by rw [h']; unfold numberFaces totalEdges; ring

private theorem total_pos {n : ℕ} (hn : 0 < n) : 0 < totalEdges n := by
  unfold totalEdges
  positivity

private theorem faces_pos {n l : ℕ} : 0 < numberFaces n l := by
  unfold numberFaces
  exact Nat.mul_pos (Nat.choose_pos (Nat.sub_le n l)) (by positivity)

/-- Uniform average over the *unlabelled geometric faces*, with no
asymptotic error and no restrictions on the input graph. -/
theorem subcube_averaging {l n : ℕ} (hl : 1 ≤ l) (hn : l ≤ n) (G : Graph n) :
    edgeDensity G = (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (n-l),
      ∑ b ∈ S.powerset, ((face G S b).card : ℚ) / totalEdges l) / numberFaces n l := by
  have h₁ : (0 : ℚ) < totalEdges n := by exact_mod_cast total_pos (by omega : 0 < n)
  have h₂ : (0 : ℚ) < totalEdges l := by exact_mod_cast total_pos hl
  have h₃ : (0 : ℚ) < numberFaces n l := by exact_mod_cast faces_pos (n := n) (l := l)
  have hi : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard (n-l),
      ∑ b ∈ S.powerset, ((face G S b).card : ℚ)) = ((n-1).choose (n-l) : ℚ) * G.card := by
    exact_mod_cast subcube_incidence G (n-l)
  have hb : ((n-1).choose (n-l) : ℚ) * totalEdges n = (numberFaces n l : ℚ) * totalEdges l := by
    exact_mod_cast incidence_normalization hl hn
  simp_rw [← Finset.sum_div]
  rw [hi]
  unfold edgeDensity
  field_simp
  linear_combination -(G.card : ℚ) * hb

theorem exists_extremal (n : ℕ) : ∃ G : Graph n, IsC4Free G ∧ G.card = exC4 n := by
  classical
  let s := (cubeEdges n).powerset.filter IsC4Free
  have h0 : IsC4Free (∅ : Graph n) := by simp [IsC4Free, HasSquare]
  have hs : s.Nonempty := ⟨∅, by simp [s, h0]⟩
  obtain ⟨G, hm, he⟩ := Finset.exists_mem_eq_sup s hs Finset.card
  exact ⟨G, (Finset.mem_filter.mp hm).2, he.symm⟩

theorem exC4_facets (n : ℕ) : n * exC4 (n+1) ≤ (n+1) * (2 * exC4 n) := by
  obtain ⟨G, hG, hcard⟩ := exists_extremal (n+1)
  rw [← hcard]
  have h (i : Fin (n+1)) : (facet G i false).card + (facet G i true).card ≤ 2 * exC4 n := by
    have h0 := facet_card_le hG i false
    have h1 := facet_card_le hG i true
    omega
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (n+1)))) (fun i _ => h i)
  rw [opposite_facets] at hh
  simpa using hh

noncomputable def extremalDensity (n : ℕ) : ℝ := (exC4 n : ℝ) / totalEdges n

theorem extremalDensity_succ {n : ℕ} (hn : 0 < n) :
    extremalDensity (n+1) ≤ extremalDensity n := by
  have h₁ : (0 : ℝ) < totalEdges n := by exact_mod_cast total_pos hn
  have h₂ : (0 : ℝ) < totalEdges (n+1) := by exact_mod_cast total_pos (Nat.succ_pos n)
  unfold extremalDensity
  apply (div_le_div_iff₀ h₂ h₁).2
  exact_mod_cast (show exC4 (n+1) * totalEdges n ≤ exC4 n * totalEdges (n+1) by
    have hh := Nat.mul_le_mul_right (2^(n-1)) (exC4_facets n)
    have hp : 2^n = 2^(n-1) * 2 := by
      conv_lhs => rw [show n = (n-1)+1 by omega, pow_succ]
    simp only [totalEdges, Nat.add_sub_cancel] 
    rw [hp]
    nlinarith only [hh])

noncomputable def piC4 : ℝ := ⨅ m : ℕ, extremalDensity (m+1)

theorem density_limit : Filter.Tendsto (fun m : ℕ => extremalDensity (m+1))
    Filter.atTop (nhds piC4) := by
  have ha : Antitone (fun m : ℕ => extremalDensity (m+1)) :=
    antitone_nat_of_succ_le fun m => extremalDensity_succ (Nat.succ_pos m)
  apply tendsto_atTop_ciInf ha
  refine ⟨0, ?_⟩
  rintro _ ⟨m, rfl⟩
  unfold extremalDensity
  positivity


namespace Flags

variable {ι : Type*} [DecidableEq ι]

def overlapClass (U A : Finset ι) (d k : ℕ) :=
  (U.powersetCard d).filter fun B => (B ∩ A).card = k

private theorem split_union (A B : Finset ι) : (B ∩ A) ∪ (B \ A) = B := by
  ext x; simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]; tauto

private theorem split_disjoint (A B : Finset ι) : Disjoint (B ∩ A) (B \ A) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact (Finset.mem_sdiff.mp hy).2 (Finset.mem_inter.mp hx).2

/-- Hypergeometric numerator. The denominator, independent of the first
extension, is `U.card.choose A.card`. Includes impossible intersection sizes. -/
theorem card_overlapClass {U A : Finset ι} (hA : A ⊆ U) (k : ℕ) :
    (overlapClass U A A.card k).card =
      A.card.choose k * (U.card - A.card).choose (A.card-k) := by
  classical
  let f : Finset ι → Finset ι × Finset ι := fun B => (B ∩ A, B \ A)
  let P := (A.powersetCard k) ×ˢ ((U \ A).powersetCard (A.card-k))
  have inj : Function.Injective f := by
    intro X Y h
    calc
      X = (f X).1 ∪ (f X).2 := (split_union A X).symm
      _ = (f Y).1 ∪ (f Y).2 := by rw [h]
      _ = Y := split_union A Y
  have image_eq : (overlapClass U A A.card k).image f = P := by
    ext p
    rcases p with ⟨X,Y⟩
    constructor
    · rintro hp
      obtain ⟨B, hB, heq⟩ := Finset.mem_image.mp hp
      rw [← heq]
      obtain ⟨hb, hk⟩ := Finset.mem_filter.mp hB
      obtain ⟨hbu,hbd⟩ := Finset.mem_powersetCard.mp hb
      have hs := Finset.card_union_of_disjoint (split_disjoint A B)
      rw [split_union] at hs
      apply Finset.mem_product.mpr
      refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, hk⟩, ?_⟩
      apply Finset.mem_powersetCard.mpr
      constructor
      · exact Finset.sdiff_subset_sdiff hbu (fun _ h => h)
      · change (B \ A).card = A.card-k; omega
    · intro hp
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
      obtain ⟨hxa,hxc⟩ := Finset.mem_powersetCard.mp hx
      obtain ⟨hyu,hyc⟩ := Finset.mem_powersetCard.mp hy
      have hdis : Disjoint X Y := Finset.disjoint_left.mpr
        (fun _ hx hy => (Finset.mem_sdiff.mp (hyu hy)).2 (hxa hx))
      have hX : (X ∪ Y) ∩ A = X := by
        ext t
        simp only [Finset.mem_inter, Finset.mem_union]
        exact ⟨fun ⟨h, ha⟩ => h.elim id (fun hy => ((Finset.mem_sdiff.mp (hyu hy)).2 ha).elim),
          fun hx => ⟨Or.inl hx, hxa hx⟩⟩
      have hY : (X ∪ Y) \ A = Y := by
        ext t
        simp only [Finset.mem_sdiff, Finset.mem_union]
        exact ⟨fun ⟨h, ha⟩ => h.elim (fun hx => (ha (hxa hx)).elim) id,
          fun hy => ⟨Or.inr hy, (Finset.mem_sdiff.mp (hyu hy)).2⟩⟩
      have hk : k ≤ A.card := hxc ▸ Finset.card_le_card hxa
      apply Finset.mem_image.mpr
      refine ⟨X ∪ Y, Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨?_, ?_⟩, by rwa [hX]⟩, Prod.ext hX hY⟩
      · exact Finset.union_subset (hxa.trans hA) (hyu.trans Finset.sdiff_subset)
      · rw [Finset.card_union_of_disjoint hdis, hxc, hyc]; omega
  calc
    _ = ((overlapClass U A A.card k).image f).card := (Finset.card_image_of_injective _ inj).symm
    _ = P.card := congrArg Finset.card image_eq
    _ = _ := by simp [P, Finset.card_powersetCard, Finset.card_sdiff_of_subset hA]

def overlapWeight (n s m k : ℕ) : ℚ :=
  ((m-s).choose k * (n-m).choose (m-s-k) : ℕ) / (((n-s).choose (m-s) : ℕ) : ℚ)

theorem overlap_probability {s m n : ℕ} (hs : s ≤ m) (hm : m ≤ n)
    {U A : Finset ι} (hU : U.card=n-s) (ha : A.card=m-s) (h : A ⊆ U) (k : ℕ) :
    ((overlapClass U A (m-s) k).card : ℚ) / (U.powersetCard (m-s)).card =
      overlapWeight n s m k := by
  rw [← ha, card_overlapClass h, Finset.card_powersetCard, ha, hU,
    show n - s - (m - s) = n - m by omega]
  rfl

theorem overlap_step_one {s n k : ℕ} (hk : k ≠ 0 ∧ k ≠ 1) :
    overlapWeight n s (s+1) k = 0 := by
  have h : 1 < k := by omega
  simp [overlapWeight, Nat.choose_eq_zero_of_lt h]

theorem overlap_step_two {s n k : ℕ} (hk : k ≠ 0 ∧ k ≠ 1 ∧ k ≠ 2) :
    overlapWeight n s (s+2) k = 0 := by
  have h : 2 < k := by omega
  simp [overlapWeight, Nat.choose_eq_zero_of_lt h]

/-- Rational Gram/LDL certificate in row form evaluated on the actual
root-conditioned density vector, then averaged. No real eigensolver enters. -/
theorem rooted_sos_nonneg {θ r a : Type*} [Fintype r] [Fintype a]
    (roots : Finset θ) (w : r → ℚ) (hw : ∀ i, 0 ≤ w i)
    (v : r → a → ℚ) (p : θ → a → ℚ) :
    0 ≤ (∑ t ∈ roots, ∑ i, w i * (∑ j, v i j * p t j)^2) / roots.card := by
  apply div_nonneg _ (by positivity)
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)


end Flags

/-! ## Integrality cuts, including their exact diagonal correction -/

/-- The gap between consecutive integers, written as a quadratic cut. -/
theorem lattice_identity (k h : ℤ) :
    4 * (k-h) * (k-h-1) = (2*k - (2*h+1))^2 - 1 := by ring

theorem lattice_nonneg (k h : ℤ) : 0 ≤ 4 * (k-h) * (k-h-1) := by
  by_cases ha : k-h ≤ 0
  · exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by decide) ha) (by omega)
  · exact mul_nonneg (mul_nonneg (by decide) (by omega)) (by omega)

def mean {α : Type*} (S : Finset α) (f : α → ℚ) : ℚ :=
  (∑ i ∈ S, f i) / S.card

/-- Two independent draws, with replacement, not just disjoint draws. -/
def pairMean {α : Type*} (S : Finset α) (F : α → α → ℚ) : ℚ :=
  (∑ i ∈ S, ∑ j ∈ S, F i j) / (S.card : ℚ)^2

theorem pairMean_centered {α : Type*} {S : Finset α} (hs : S.Nonempty) (U : α → ℚ) :
    pairMean S (fun i j => U i * U j - 1) = (mean S U)^2 - 1 := by
  have hc : (S.card : ℚ) ≠ 0 := by exact_mod_cast Finset.card_ne_zero.mpr hs
  simp only [pairMean, mean, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  field_simp


def centeredExtension {N : ℕ} (f : Fin N → ℤ) (h : ℤ) (i : Fin N) : ℚ :=
  2 * (N : ℚ) * f i - (2 * (h : ℚ) + 1)

theorem extension_lattice_identity {N : ℕ} (hN : 0 < N) (f : Fin N → ℤ) (h : ℤ) :
    pairMean Finset.univ (fun i j => centeredExtension f h i * centeredExtension f h j - 1) =
      ((4 * ((∑ i, f i) - h) * ((∑ i, f i) - h - 1) : ℤ) : ℚ) := by
  let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hc : (N : ℚ) ≠ 0 := by positivity
  rw [pairMean_centered Finset.univ_nonempty, lattice_identity]
  simp only [mean, centeredExtension, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

theorem extension_lattice_nonneg {N : ℕ} (hN : 0 < N) (f : Fin N → ℤ) (h : ℤ) :
    0 ≤ pairMean Finset.univ (fun i j => centeredExtension f h i * centeredExtension f h j - 1) := by
  rw [extension_lattice_identity hN]
  exact_mod_cast lattice_nonneg (∑ i, f i) h

/-- Mean on *ordered* pairs of distinct extensions. -/
def offDiagonalMean {N : ℕ} (F : Fin N → Fin N → ℚ) : ℚ :=
  (∑ i, ∑ j ∈ Finset.univ.erase i, F i j) / ((N : ℚ) * (N-1 : ℚ))

theorem pairMean_diagonal_split {N : ℕ} (hN : 2 ≤ N) (F : Fin N → Fin N → ℚ) :
    (N-1 : ℚ) / N * offDiagonalMean F + (1 : ℚ) / N * mean Finset.univ (fun i => F i i) =
      pairMean Finset.univ F := by
  have h1 : (N : ℚ) ≠ 0 := by positivity
  have h2 : (N-1 : ℚ) ≠ 0 := by
    have : (2 : ℚ) ≤ N := by exact_mod_cast hN
    linarith
  have hs (i : Fin N) : ∑ j, F i j = (∑ j ∈ Finset.univ.erase i, F i j) + F i i :=
    (Finset.sum_erase_add _ _ (Finset.mem_univ i)).symm
  simp only [offDiagonalMean, pairMean, mean, Finset.card_univ, Fintype.card_fin,
    hs, Finset.sum_add_distrib]
  field_simp

theorem split_extension_lattice_cut {N : ℕ} (hN : 2 ≤ N) (f : Fin N → ℤ) (h : ℤ) :
    0 ≤ (N-1 : ℚ) / N * offDiagonalMean (fun i j => centeredExtension f h i * centeredExtension f h j - 1) +
      (1 : ℚ) / N * mean Finset.univ (fun i => centeredExtension f h i * centeredExtension f h i - 1) := by
  rw [pairMean_diagonal_split hN (fun i j => centeredExtension f h i * centeredExtension f h j - 1)]
  exact extension_lattice_nonneg (by omega) f h

/-! ## The uniform law of nested coordinate sets -/

section Incidence
variable {α : Type*} [DecidableEq α]

private theorem count_supersets {U S : Finset α} (hS : S ⊆ U) {k : ℕ} (hk : S.card ≤ k) :
    ((U.powersetCard k).filter (fun T => S ⊆ T)).card =
      (U.card - S.card).choose (k - S.card) := by
  classical
  calc
    _ = ((U \ S).powersetCard (k-S.card)).card := by
      refine Finset.card_bij' (fun T _ => T \ S) (fun A _ => A ∪ S) ?_ ?_ ?_ ?_
      · intro T hT
        obtain ⟨hT, hST⟩ := Finset.mem_filter.mp hT
        obtain ⟨hTU, hTk⟩ := Finset.mem_powersetCard.mp hT
        exact Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset_sdiff hTU (fun _ h => h),
          by rw [Finset.card_sdiff_of_subset hST, hTk]⟩
      · intro A hA
        obtain ⟨has, hac⟩ := Finset.mem_powersetCard.mp hA
        have hd : Disjoint A S := Finset.disjoint_left.mpr fun _ ha => (Finset.mem_sdiff.mp (has ha)).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
          ⟨Finset.union_subset (has.trans Finset.sdiff_subset) hS,
            by rw [Finset.card_union_of_disjoint hd, hac]; omega⟩, Finset.subset_union_right⟩
      · intro T hT
        have hST := (Finset.mem_filter.mp hT).2
        ext a
        simp only [Finset.mem_union, Finset.mem_sdiff]
        specialize @hST a
        tauto
      · intro A hA
        have hAS := (Finset.mem_powersetCard.mp hA).1
        ext a
        have h := fun (h : a ∈ A) => (Finset.mem_sdiff.mp (hAS h)).2
        simp only [Finset.mem_sdiff, Finset.mem_union]
        tauto
    _ = _ := by rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hS]

private theorem sum_nested (U : Finset α) {d k : ℕ} (hdk : d ≤ k) (F : Finset α → ℚ) :
    ∑ T ∈ U.powersetCard k, ∑ S ∈ T.powersetCard d, F S =
      ((U.card-d).choose (k-d) : ℚ) * ∑ S ∈ U.powersetCard d, F S := by
  classical
  calc
    _ = ∑ T ∈ U.powersetCard k, ∑ S ∈ U.powersetCard d, if S ⊆ T then F S else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      have hTU := (Finset.mem_powersetCard.mp hT).1
      have hs : T.powersetCard d = (U.powersetCard d).filter (fun S => S ⊆ T) := by
        ext S
        simp only [Finset.mem_powersetCard, Finset.mem_filter]
        exact ⟨fun h => ⟨⟨h.1.trans hTU, h.2⟩, h.1⟩, fun h => ⟨h.2,h.1.2⟩⟩
      rw [hs, Finset.sum_filter]
    _ = ∑ S ∈ U.powersetCard d, ∑ T ∈ U.powersetCard k, if S ⊆ T then F S else 0 := Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      obtain ⟨hSU,hSc⟩ := Finset.mem_powersetCard.mp hS
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul,
        count_supersets hSU (by omega : S.card ≤ k), hSc]

/-- First choose k axes uniformly, then d among them: the marginal is uniform.
This holds for arbitrary labelled observables, not just orbit invariants. -/
theorem mean_nested_coordinates (U : Finset α) {d k : ℕ} (hdk : d ≤ k) (hk : k ≤ U.card)
    (F : Finset α → ℚ) :
    mean (U.powersetCard k) (fun T => mean (T.powersetCard d) F) = mean (U.powersetCard d) F := by
  classical
  have hh : ∀ T ∈ U.powersetCard k, (T.powersetCard d).card = k.choose d := by
    intro T hT
    rw [Finset.card_powersetCard, (Finset.mem_powersetCard.mp hT).2]
  have hnorm := sum_nested U hdk (fun _ => (1 : ℚ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hnorm
  rw [Finset.sum_congr rfl (fun T ht => congrArg Nat.cast (hh T ht))] at hnorm
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_powersetCard] at hnorm
  unfold mean
  rw [Finset.sum_congr rfl (fun T ht => congrArg (fun m : ℕ => (∑ i ∈ T.powersetCard d, F i) / (m : ℚ)) (hh T ht)), ← Finset.sum_div, sum_nested U hdk]
  simp only [Finset.card_powersetCard]
  have h1 : (k.choose d : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hdk).ne'
  have h2 : (U.card.choose k : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hk).ne'
  have h3 : (U.card.choose d : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hdk.trans hk)).ne'
  rw [div_div, div_eq_div_iff (mul_ne_zero h1 h2) h3]
  linear_combination -(∑ S ∈ U.powersetCard d, F S) * hnorm

/-- With the spine edge fixed, each transverse axis labels one square page.
Sampling four available pages and then three of those pages gives the
uniform three-page marginal, for every rational observable on labelled pages. -/
theorem edgeBook_three_of_four_marginal (pages : Finset α) (h : 4 ≤ pages.card)
    (price : Finset α → ℚ) :
    mean (pages.powersetCard 4) (fun T => mean (T.powersetCard 3) price) =
      mean (pages.powersetCard 3) price :=
  mean_nested_coordinates pages (by decide) h price

private theorem sum_axis_incidence (U : Finset α) {r : ℕ} (hr : 0 < r) (f : α → ℚ) :
    ∑ A ∈ U.powersetCard r, ∑ i ∈ A, f i =
      ((U.card-1).choose (r-1) : ℚ) * ∑ i ∈ U, f i := by
  classical
  calc
    _ = ∑ A ∈ U.powersetCard r, ∑ i ∈ U, if i ∈ A then f i else 0 := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [← Finset.sum_filter]
      congr 1
      ext i
      have hAU := (Finset.mem_powersetCard.mp hA).1
      simp only [Finset.mem_filter]
      exact ⟨fun h => ⟨hAU h, h⟩, And.right⟩
    _ = ∑ i ∈ U, ∑ A ∈ U.powersetCard r, if i ∈ A then f i else 0 := Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hs : ({i} : Finset α) ⊆ U := by simpa
      have hh := count_supersets hs (by simpa : ({i} : Finset α).card ≤ r)
      simp only [Finset.card_singleton, Finset.singleton_subset_iff] at hh
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hh]
end Incidence

/-! ## The vertex-root cut and the radius-two marginal -/

/-- Unique legal code for the edge incident with support v in direction i. -/
def incidentCode {n : ℕ} (v : Finset (Fin n)) (i : Fin n) : EdgeCode n := (i, v.erase i)

def incidentBit {n : ℕ} (G : Graph n) (v : Finset (Fin n)) (i : Fin n) : ℤ :=
  if incidentCode v i ∈ G then 1 else 0

def degree {n : ℕ} (G : Graph n) (v : Finset (Fin n)) : ℤ := ∑ i, incidentBit G v i

/-- On two axes this counts the two possible spokes at v, not the opposite edges. -/
def rootEdges {n : ℕ} (G : Graph n) (v S : Finset (Fin n)) : ℤ := ∑ i ∈ S, incidentBit G v i

private theorem mean_congr {α : Type*} {S : Finset α} {f g : α → ℚ}
    (h : ∀ a ∈ S, f a = g a) : mean S f = mean S g := by
  unfold mean
  rw [Finset.sum_congr rfl h]

theorem rootEdges_two_mean {n : ℕ} (hn : 2 ≤ n) (G : Graph n) (v : Finset (Fin n)) :
    mean (Finset.univ.powersetCard 2) (fun S => (rootEdges G v S : ℚ)) =
      2 * (degree G v : ℚ) / n := by
  let U : Finset (Fin n) := Finset.univ
  have hu : U.card = n := by simp [U]
  have hs := sum_axis_incidence U (r := 2) (by decide) (fun i => (incidentBit G v i : ℚ))
  have hc := sum_axis_incidence U (r := 2) (by decide) (fun _ => (1 : ℚ))
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at hc
  have hc' : (U.card.choose 2 : ℚ) * 2 = ((U.card-1 : ℕ) : ℚ) * U.card := by
    rw [Finset.sum_congr rfl (fun A hA => congrArg (fun t : ℕ => (t : ℚ)) (Finset.mem_powersetCard.mp hA).2)] at hc
    simpa [Finset.card_powersetCard, nsmul_eq_mul] using hc
  have hN : (n : ℚ) ≠ 0 := by positivity
  have hC : (U.card.choose 2 : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (hu ▸ hn)).ne'
  change (∑ S ∈ U.powersetCard 2, (rootEdges G v S : ℚ)) / ((U.powersetCard 2).card : ℚ) = _
  simp only [rootEdges, Int.cast_sum, Finset.card_powersetCard, hs, degree]
  norm_num only [Nat.reduceSub, Nat.choose_one_right]
  rw [div_eq_div_iff hC hN]
  have huQ : (n : ℚ) = (U.card : ℚ) := by exact_mod_cast hu.symm
  rw [huQ]
  change _ = 2 * (∑ i ∈ U, (incidentBit G v i : ℚ)) * _
  linear_combination -(∑ i ∈ U, (incidentBit G v i : ℚ)) * hc'

def vertexCenter {n : ℕ} (G : Graph n) (v : Finset (Fin n)) (h : ℤ) (A : Finset (Fin n)) : ℚ :=
  n * (rootEdges G v A : ℚ) - (2 * (h : ℚ) + 1)

theorem vertex_lattice_identity {n : ℕ} (hn : 2 ≤ n) (G : Graph n) (v : Finset (Fin n)) (h : ℤ) :
    pairMean (Finset.univ.powersetCard 2) (fun A B => vertexCenter G v h A * vertexCenter G v h B - 1) =
      ((4 * (degree G v - h) * (degree G v - h - 1) : ℤ) : ℚ) := by
  let P := (Finset.univ : Finset (Fin n)).powersetCard 2
  have hc : 0 < P.card := by simpa [P, Finset.card_powersetCard] using Nat.choose_pos hn
  have hC : (P.card : ℚ) ≠ 0 := by exact_mod_cast hc.ne'
  have hN : (n : ℚ) ≠ 0 := by positivity
  have hv : mean P (vertexCenter G v h) =
      n * mean P (fun S => (rootEdges G v S : ℚ)) - (2*(h:ℚ)+1) := by
    unfold mean vertexCenter
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp
  rw [pairMean_centered (S := P) (Finset.card_pos.mp hc), hv, rootEdges_two_mean hn, lattice_identity]
  push_cast
  field_simp

theorem vertex_lattice_nonneg {n : ℕ} (hn : 2 ≤ n) (G : Graph n) (v : Finset (Fin n)) (h : ℤ) :
    0 ≤ pairMean (Finset.univ.powersetCard 2) (fun A B => vertexCenter G v h A * vertexCenter G v h B - 1) := by
  rw [vertex_lattice_identity hn]
  exact_mod_cast lattice_nonneg (degree G v) h

def flipSupport {n : ℕ} (v : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  if i ∈ v then v.erase i else insert i v

/-- Coordinates remain labelled by ambient axes. The first component records the
spokes; (i,j) in the second records the j-edge from the i-neighbor of the root. -/
abbrev Ball₂ (n : ℕ) := Finset (Fin n) × Finset (Fin n × Fin n)

def ball₂ {n : ℕ} (G : Graph n) (v S : Finset (Fin n)) : Ball₂ n :=
  (S.filter (fun i => incidentCode v i ∈ G),
   (S ×ˢ S).filter (fun p => p.1 ≠ p.2 ∧ incidentCode (flipSupport v p.1) p.2 ∈ G))

def restrictBall {n : ℕ} (B : Ball₂ n) (S : Finset (Fin n)) : Ball₂ n := (B.1 ∩ S, B.2 ∩ (S ×ˢ S))

theorem restrict_ball₂ {n : ℕ} (G : Graph n) (v : Finset (Fin n)) {S T : Finset (Fin n)} (hST : S ⊆ T) :
    restrictBall (ball₂ G v T) S = ball₂ G v S := by
  apply Prod.ext
  · ext i
    simp only [restrictBall, ball₂, Finset.mem_filter, Finset.mem_inter]
    have := @hST i
    tauto
  · ext p
    simp only [restrictBall, ball₂, Finset.mem_filter, Finset.mem_inter, Finset.mem_product]
    have h₁ := @hST p.1
    have h₂ := @hST p.2
    tauto

/-- Exact coupled marginal, conditional on each fixed root. Therefore the two
laws also coincide after choosing the root uniformly, for any price on B₂(Q₄). -/
theorem ball₂_marginal {n : ℕ} (hn : 5 ≤ n) (G : Graph n) (v : Finset (Fin n)) (price : Ball₂ n → ℚ) :
    mean (Finset.univ.powersetCard 5) (fun T =>
      mean (T.powersetCard 4) (fun S => price (restrictBall (ball₂ G v T) S))) =
      mean (Finset.univ.powersetCard 4) (fun S => price (ball₂ G v S)) := by
  rw [← mean_nested_coordinates (U := (Finset.univ : Finset (Fin n))) (d := 4) (k := 5)
    (by decide) (by simpa using hn) (fun S => price (ball₂ G v S))]
  apply mean_congr
  intro T _
  apply mean_congr
  intro S hS
  rw [restrict_ball₂ G v (Finset.mem_powersetCard.mp hS).1]
end Erdos86FlagAlgebra
