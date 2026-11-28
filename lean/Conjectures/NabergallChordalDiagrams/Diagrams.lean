module

public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fin.SuccPred

@[expose] public section

/-!
# Matchings, open fragments, and deletion of the root

A fragment is an involution on the original positions. Fixed points are its
singletons. The right endpoint names a chord. For a singleton we put its
exterior mate *before* the original positions, in the same order as the
singletons. This is the same cyclic order as appending the exterior interval.
No rotation or reflection is quotiented out.
-/

namespace NabergallChordalDiagrams

abbrev Fragment (N : ℕ) := {f : Fin N → Fin N // Function.Involutive f}

def Fragment.mate {N : ℕ} (F : Fragment N) : Fin N → Fin N := F.val

@[simp] theorem Fragment.mate_mate {N} (F : Fragment N) (x) :
    F.mate (F.mate x) = x := F.property x

@[ext] theorem Fragment.ext_mate {N} {F H : Fragment N} (h : ∀ x, F.mate x = H.mate x) :
    F = H := Subtype.ext (funext h)

/-- Fixed-point-free involutions, before specializing the number of endpoints. -/
abbrev Perfect (N : ℕ) := {D : Fragment N // ∀ b, D.mate b ≠ b}

abbrev RootedChordDiagram (n : ℕ) := Perfect (2 * n)

/-- Right endpoints: for a singleton this is its unique original position. -/
abbrev Fragment.Chord {N : ℕ} (F : Fragment N) := {b : Fin N // F.mate b ≤ b}

/-- Strict alternation of the endpoints of two chords with increasing endpoints. -/
def Cross (a b c d : ℕ) : Prop :=
  (a < c ∧ c < b ∧ b < d) ∨ (c < a ∧ a < d ∧ d < b)

def alternationGraph {V : Type*} (lo hi : V → ℕ) : SimpleGraph V where
  Adj x y := Cross (lo x) (hi x) (lo y) (hi y)
  symm := ⟨fun _ _ h => h.elim Or.inr Or.inl⟩
  loopless := ⟨fun _ h => h.elim (fun h => (lt_irrefl _ h.1)) (fun h => (lt_irrefl _ h.1))⟩

/-- The ordinary intersection graph, on the chords of a perfect matching. -/
def crossingGraph {N : ℕ} (D : Perfect N) : SimpleGraph D.val.Chord :=
  alternationGraph (fun c => (D.val.mate c.val).val) (fun c => c.val.val)

theorem chord_left_lt_right {N : ℕ} (D : Perfect N) (c : D.val.Chord) :
    D.val.mate c.val < c.val := lt_of_le_of_ne c.property (D.property _)

/-- Consecutive indices on the oriented circle, in either direction. -/
def CyclicNeighbor {k : ℕ} (i j : Fin k) : Prop :=
  (i.val + 1) % k = j.val ∨ (j.val + 1) % k = i.val

/-- Every cycle of length at least four has a chord: there is no injection
identifying the induced adjacency relation with cyclic adjacency. -/
def Chordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ (k : ℕ), 4 ≤ k → ∀ f : Fin k → V, Function.Injective f →
    ¬ (∀ i j, G.Adj (f i) (f j) ↔ CyclicNeighbor i j)

theorem Chordal.of_induced {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Chordal H) (f : V → W) (hf : Function.Injective f)
    (he : ∀ x y, H.Adj (f x) (f y) ↔ G.Adj x y) : Chordal G :=
  fun k hk g hg cyc => h k hk (f ∘ g) (hf.comp hg) (fun i j => (he _ _).trans (cyc i j))

theorem chordal_iso_iff {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) : Chordal G ↔ Chordal H :=
  ⟨fun h => h.of_induced e.symm e.symm.injective (fun _ _ => e.symm.map_rel_iff),
   fun h => h.of_induced e e.injective (fun _ _ => e.map_rel_iff)⟩

/-- This subtype is the one counted in published Conjecture 8.5. -/
abbrev ConnectedChordalDiagram (n : ℕ) :=
  {D : RootedChordDiagram n // (crossingGraph D).Connected ∧ Chordal (crossingGraph D)}

noncomputable instance (n) : Fintype (ConnectedChordalDiagram n) := Fintype.ofFinite _

def Fragment.singletons {N} (F : Fragment N) : Finset (Fin N) :=
  Finset.univ.filter fun x => F.mate x = x

def Fragment.weight {N} (F : Fragment N) := F.singletons.card

@[simp] theorem Fragment.mem_singletons {N} (F : Fragment N) (x) :
    x ∈ F.singletons ↔ F.mate x = x := by simp [Fragment.singletons]

theorem Fragment.weight_le {N} (F : Fragment N) : F.weight ≤ N := by
  simpa [Fragment.weight] using F.singletons.card_le_univ

theorem Fragment.weight_eq_one_iff {N} (F : Fragment N) :
    F.weight = 1 ↔ ∃ s, ∀ x, F.mate x = x ↔ x = s := by
  rw [Fragment.weight, Finset.card_eq_one]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨s, fun x => by rw [← F.mem_singletons, hs, Finset.mem_singleton]⟩
  · rintro ⟨s, hs⟩
    exact ⟨s, Finset.ext fun x => by simp [hs]⟩

/-- Exterior endpoints use coordinates below `N`, and original endpoints
use coordinates `N+b`. Empty spaces in the exterior do not affect alternation. -/
def Fragment.start {N} (F : Fragment N) (b : Fin N) : ℕ :=
  if F.mate b = b then b.val else N + (F.mate b).val

def Fragment.graph {N} (F : Fragment N) : SimpleGraph F.Chord :=
  alternationGraph (fun c => F.start c.val) (fun c => N + c.val.val)

def Fragment.Valid {N} (F : Fragment N) := F.graph.Connected ∧ Chordal F.graph

/-- A gap is indexed by its first position on the right. -/
def Fragment.Spanned {N} (F : Fragment N) (g : ℕ) : Prop :=
  ∃ b : Fin N, (F.mate b).val < g ∧ g ≤ b.val

def Fragment.Irreducible {N} (F : Fragment N) := ∀ g, 0 < g → g < N → F.Spanned g

abbrev ValidFragment (N k : ℕ) :=
  {F : Fragment N // F.Valid ∧ F.weight = k ∧ 0 < k}

abbrev IrreducibleFragment (N k : ℕ) :=
  {F : ValidFragment N k // F.val.Irreducible}

noncomputable instance (N k) : Fintype (ValidFragment N k) := Fintype.ofFinite _
noncomputable instance (N k) : Fintype (IrreducibleFragment N k) := Fintype.ofFinite _

noncomputable def H_count (N k : ℕ) := Fintype.card (ValidFragment N k)
noncomputable def I_count (N k : ℕ) := Fintype.card (IrreducibleFragment N k)

theorem H_count_zero (N : ℕ) : H_count N 0 = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun F => (Nat.lt_irrefl 0) F.property.2.2⟩

theorem I_count_zero (N : ℕ) : I_count N 0 = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun F => (Nat.lt_irrefl 0) F.val.property.2.2⟩

theorem H_count_support (N k : ℕ) (hk : N < k) : H_count N k = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun F => (not_lt_of_ge (F.property.2.1 ▸ F.val.weight_le)) hk⟩

theorem I_count_support (N k : ℕ) (hk : N < k) : I_count N k = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun F => (not_lt_of_ge (F.val.property.2.1 ▸ F.val.val.weight_le)) hk⟩

namespace RootDeletion

variable {N : ℕ}

def partner (D : Perfect (N+1)) : Fin N := (D.val.mate 0).pred (D.property 0)

@[simp] theorem succ_partner (D : Perfect (N+1)) : (partner D).succ = D.val.mate 0 :=
  Fin.succ_pred _ _

theorem mate_succ_eq_zero_iff (D : Perfect (N+1)) (x : Fin N) :
    D.val.mate x.succ = 0 ↔ x = partner D := by
  constructor
  · intro h
    apply Fin.succ_injective
    rw [succ_partner, ← h, Fragment.mate_mate]
  · rintro rfl
    simp

def dropFun (D : Perfect (N+1)) (x : Fin N) : Fin N :=
  if h : D.val.mate x.succ = 0 then x else (D.val.mate x.succ).pred h

theorem succ_dropFun (D : Perfect (N+1)) (x : Fin N) :
    (dropFun D x).succ = if D.val.mate x.succ = 0 then x.succ else D.val.mate x.succ := by
  by_cases h : D.val.mate x.succ = 0 <;> simp [dropFun, h]

def drop (D : Perfect (N+1)) : Fragment N := ⟨dropFun D, by
  intro x
  by_cases h : D.val.mate x.succ = 0
  · simp [dropFun, h]
  · have e : (dropFun D x).succ = D.val.mate x.succ := by simp [succ_dropFun, h]
    apply Fin.succ_injective
    simp [succ_dropFun, e, Fragment.mate_mate]⟩

theorem drop_fixed_iff (D : Perfect (N+1)) (x : Fin N) :
    (drop D).mate x = x ↔ x = partner D := by
  rw [← mate_succ_eq_zero_iff]
  change dropFun D x = x ↔ _
  by_cases h : D.val.mate x.succ = 0
  · simp [dropFun, h]
  · refine ⟨fun hx => ?_, fun hh => (h hh).elim⟩
    have hh := succ_dropFun D x
    rw [hx, ite_eq_right h] at hh
    exact (D.property _ hh.symm).elim

abbrev One (N : ℕ) := {F : Fragment N // F.weight = 1}

def deleteRoot (D : Perfect (N+1)) : One N :=
  ⟨drop D, (drop D).weight_eq_one_iff.mpr ⟨partner D, drop_fixed_iff D⟩⟩

noncomputable def singletonOf (F : One N) : Fin N :=
  Classical.choose (F.val.weight_eq_one_iff.mp F.property)

theorem fixed_iff (F : One N) (x : Fin N) : F.val.mate x = x ↔ x = singletonOf F :=
  Classical.choose_spec (F.val.weight_eq_one_iff.mp F.property) x

@[simp] theorem mate_singletonOf (F : One N) : F.val.mate (singletonOf F) = singletonOf F :=
  (fixed_iff F _).mpr rfl

@[simp] theorem mate_eq_singleton_iff (F : One N) (x : Fin N) :
    F.val.mate x = singletonOf F ↔ x = singletonOf F := by
  constructor
  · intro h
    have := congrArg F.val.mate h
    simpa only [Fragment.mate_mate, mate_singletonOf] using this
  · rintro rfl
    simp

noncomputable def plugFun (F : One N) : Fin (N+1) → Fin (N+1) :=
  Fin.cases (singletonOf F).succ fun x => if x = singletonOf F then 0 else (F.val.mate x).succ

@[simp] theorem plug_zero (F : One N) : plugFun F 0 = (singletonOf F).succ := rfl

@[simp] theorem plug_succ (F : One N) (x : Fin N) :
    plugFun F x.succ = if x = singletonOf F then 0 else (F.val.mate x).succ := rfl

noncomputable def replaceRoot (F : One N) : Perfect (N+1) :=
  ⟨⟨plugFun F, by
      intro x
      refine Fin.cases (by simp) (fun b => ?_) x
      by_cases hb : b = singletonOf F <;> simp [hb]⟩, by
    intro x
    refine Fin.cases (by exact Fin.succ_ne_zero _) (fun b => ?_) x
    change plugFun F b.succ ≠ b.succ
    by_cases hb : b = singletonOf F <;> simp [hb, fixed_iff, Ne.symm (Fin.succ_ne_zero _)]⟩

@[simp] theorem singleton_drop (D : Perfect (N+1)) :
    singletonOf (deleteRoot D) = partner D :=
  (drop_fixed_iff D _).mp (mate_singletonOf (deleteRoot D))

@[simp] theorem replace_delete (D : Perfect (N+1)) : replaceRoot (deleteRoot D) = D := by
  apply Subtype.ext
  apply Fragment.ext_mate
  intro x
  change plugFun _ x = _
  refine Fin.cases (by simp) (fun b => ?_) x
  by_cases h : b = partner D
  · rw [plug_succ, singleton_drop, ite_eq_left h, (mate_succ_eq_zero_iff D b).mpr h]
  · have hd := (mate_succ_eq_zero_iff D b).not.mpr h
    simp only [plug_succ, singleton_drop, ite_eq_right h]
    exact (succ_dropFun D b).trans (ite_eq_right hd)

@[simp] theorem delete_replace (F : One N) : deleteRoot (replaceRoot F) = F := by
  apply Subtype.ext
  apply Fragment.ext_mate
  intro x
  apply Fin.succ_injective
  rw [show (deleteRoot (replaceRoot F)).val.mate x = dropFun (replaceRoot F) x from rfl,
    succ_dropFun]
  change (if plugFun F x.succ = 0 then x.succ else plugFun F x.succ) = _
  by_cases h : x = singletonOf F <;> simp [h]

noncomputable def rawEquiv (N : ℕ) : Perfect (N+1) ≃ One N where
  toFun := deleteRoot
  invFun := replaceRoot
  left_inv := replace_delete
  right_inv := delete_replace

private theorem end_le_iff (F : One N) (x : Fin N) :
    (replaceRoot F).val.mate x.succ ≤ x.succ ↔ F.val.mate x ≤ x := by
  change plugFun F x.succ ≤ x.succ ↔ _
  by_cases h : x = singletonOf F <;> simp [h]

noncomputable def endMap (F : One N) (c : F.val.Chord) : (replaceRoot F).val.Chord :=
  ⟨c.val.succ, by exact (end_le_iff F c.val).mpr c.property⟩

theorem endMap_bijective (F : One N) : Function.Bijective (endMap F) := by
  refine ⟨fun a b h => Subtype.ext (Fin.succ_injective _ (congrArg Subtype.val h)), ?_⟩
  rintro ⟨b, hb⟩
  have h0 : b ≠ 0 := by
    rintro rfl
    change (singletonOf F).succ ≤ 0 at hb
    exact (Nat.not_succ_le_zero _ hb)
  let x := b.pred h0
  have hx : x.succ = b := Fin.succ_pred _ _
  have hx' : F.val.mate x ≤ x := (end_le_iff F x).mp (hx ▸ hb)
  exact ⟨⟨x, hx'⟩, Subtype.ext hx⟩

private theorem endMap_adj (F : One N) (c d : F.val.Chord) :
    (crossingGraph (replaceRoot F)).Adj (endMap F c) (endMap F d) ↔ F.val.graph.Adj c d := by
  change Cross (plugFun F c.val.succ).val c.val.succ.val (plugFun F d.val.succ).val
    d.val.succ.val ↔ Cross (F.val.start c.val) (N+c.val.val) (F.val.start d.val) (N+d.val.val)
  have hc := c.val.isLt
  have hd := d.val.isLt
  by_cases a : c.val = singletonOf F <;> by_cases b : d.val = singletonOf F <;>
    simp only [plug_succ, Fragment.start, fixed_iff, a, b, ite_true, ite_false,
      Fin.val_zero, Fin.val_succ, mate_singletonOf, Cross] <;> omega

noncomputable def graphIso (F : One N) : F.val.graph ≃g crossingGraph (replaceRoot F) where
  toEquiv := Equiv.ofBijective _ (endMap_bijective F)
  map_rel_iff' := by exact endMap_adj F _ _

theorem delete_valid_iff (D : Perfect (N+1)) :
    (deleteRoot D).val.Valid ↔ (crossingGraph D).Connected ∧ Chordal (crossingGraph D) := by
  have e := graphIso (deleteRoot D)
  exact (and_congr e.connected_iff (chordal_iso_iff e)).trans
    (Iff.of_eq (congrArg (fun d : Perfect (N+1) =>
      (crossingGraph d).Connected ∧ Chordal (crossingGraph d)) (replace_delete D)))

noncomputable def validEquiv (N : ℕ) :
    {D : Perfect (N+1) // (crossingGraph D).Connected ∧ Chordal (crossingGraph D)} ≃
      ValidFragment N 1 where
  toFun D := ⟨(deleteRoot D.val).val, (delete_valid_iff _).mpr D.property,
    (deleteRoot D.val).property, by decide⟩
  invFun F := ⟨replaceRoot ⟨F.val, F.property.2.1⟩,
    let e := graphIso (⟨F.val, F.property.2.1⟩ : One N)
    ⟨e.connected_iff.mp F.property.1.1, (chordal_iso_iff e).mp F.property.1.2⟩⟩
  left_inv D := Subtype.ext (replace_delete D.val)
  right_inv F := Subtype.ext (congrArg (fun x : One N => x.val) (delete_replace ⟨F.val, F.property.2.1⟩))

end RootDeletion

noncomputable def rootDeletionEquiv (n : ℕ) (hn : 1 ≤ n) :
    ConnectedChordalDiagram n ≃ ValidFragment (2*n-1) 1 := by
  have h : 2*n = (2*n-1)+1 := by omega
  unfold ConnectedChordalDiagram RootedChordDiagram
  conv_lhs => rw [h]
  exact RootDeletion.validEquiv _

theorem card_eq_weight_one (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card (ConnectedChordalDiagram n) = H_count (2*n-1) 1 :=
  Fintype.card_congr (rootDeletionEquiv n hn)

end NabergallChordalDiagrams
