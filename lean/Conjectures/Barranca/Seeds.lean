import Conjectures.Barranca.Basic
import Mathlib.Tactic.FinCases

/-! Finite induced-subgraph witnesses for all ten disconnected seeds. -/
namespace Barranca

open SimpleGraph Matrix Polynomial Finset
open scoped BigOperators
set_option linter.unusedSimpArgs false

noncomputable section

section FiniteChecks

/-- Encode simple graphs on Fin n by the bits (min i j) * n + max i j. -/
def bitsGraph (n m : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ m.testBit (min x.val y.val * n + max x.val y.val) = true
  symm := ⟨fun {x y} h => ⟨h.1.symm, by simpa [min_comm,max_comm] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance (n m) : DecidableRel (bitsGraph n m).Adj := fun x y =>
  inferInstanceAs (Decidable (x ≠ y ∧ m.testBit (min x.val y.val * n + max x.val y.val) = true))

def bits (n m : ℕ) : Graph := pack _ (bitsGraph n m)

/-- Little-endian dense integer coefficients. Only zero, minus one and X are
needed as pencil entries. The list operations below have no polynomial oracle. -/
def decode : List ℤ → ℤ[X]
  | [] => 0
  | a :: p => C a + X * decode p

def addCoeffs : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a+b) :: addCoeffs p q

theorem decode_add (p q : List ℤ) : decode (addCoeffs p q) = decode p + decode q := by
  induction p generalizing q with
  | nil => simp [addCoeffs, decode]
  | cons a p ih =>
    cases q <;> simp [addCoeffs, decode, ih] <;> ring

theorem decode_scale (c : ℤ) (p : List ℤ) :
    decode (p.map (c * ·)) = C c * decode p := by
  induction p with
  | nil => simp [decode]
  | cons a p ih => simp [decode, ih]; ring

def sumCoeffs (ps : List (List ℤ)) := ps.foldr addCoeffs []

theorem decode_sum (ps : List (List ℤ)) : decode (sumCoeffs ps) = (ps.map decode).sum := by
  induction ps with
  | nil => rfl
  | cons a ps ih => exact (decode_add a _).trans (congrArg (decode a + ·) ih)

inductive PencilEntry | zero | edge | var

def weight : PencilEntry → ℤ[X]
  | .zero => 0
  | .edge => -1
  | .var => X

def term (s : ℤ) (e : PencilEntry) (p : List ℤ) : List ℤ :=
  match e with
  | .zero => []
  | .edge => p.map ((-s) * ·)
  | .var => 0 :: p.map (s * ·)

theorem decode_term (s : ℤ) (e : PencilEntry) (p : List ℤ) :
    decode (term s e p) = C s * weight e * decode p := by
  cases e with
  | zero => simp [term, weight, decode]
  | edge => rw [term, decode_scale]; simp [weight]
  | var => simp only [term, decode, decode_scale, map_zero, zero_add, weight]; ring

/-- Laplace expansion along row zero; the zero branch discards its minor. -/
def detCoeffs : {n : ℕ} → Matrix (Fin n) (Fin n) PencilEntry → List ℤ
  | 0, _ => [1]
  | n+1, M => sumCoeffs <| (List.finRange (n+1)).map fun j =>
      term ((-1 : ℤ) ^ j.val) (M 0 j) (detCoeffs (M.submatrix Fin.succ j.succAbove))

theorem detCoeffs_correct {n : ℕ} (M : Matrix (Fin n) (Fin n) PencilEntry) :
    decode (detCoeffs M) = (M.map weight).det := by
  induction n with
  | zero => simp [detCoeffs, decode, Matrix.det_fin_zero]
  | succ n ih =>
    rw [detCoeffs, decode_sum, Matrix.det_succ_row_zero, Fin.sum_univ_def]
    simp only [List.map_map, Function.comp_def, decode_term, ih, map_pow, map_neg, map_one]
    rfl

def pencil (n m : ℕ) : Matrix (Fin n) (Fin n) PencilEntry := fun i j =>
  if i = j then .var else if (bitsGraph n m).Adj i j then .edge else .zero

theorem cp_bits (n m : ℕ) : cp (bits n m) = decode (detCoeffs (pencil n m)) := by
  rw [detCoeffs_correct]
  unfold bits
  rw [cp_pack, Matrix.charpoly]
  congr 1
  ext i j
  by_cases h : i = j
  · subst j
    simp [pencil, weight, Matrix.charmatrix_apply_eq]
  · rw [Matrix.charmatrix_apply_ne _ _ _ h]
    by_cases a : (bitsGraph n m).Adj i j <;> simp [pencil, weight, h, a]

def choices {α β : Type} [DecidableEq α] [DecidableEq β]
    (H : SimpleGraph α) (G : SimpleGraph β) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (cand : List β) : List α → List (α × β) → Bool
  | [], _ => true
  | x :: xs, prev => cand.any fun y =>
    (prev.all fun p => decide ((p.1=x ↔ p.2=y) ∧ (H.Adj p.1 x ↔ G.Adj p.2 y))) &&
      choices H G cand xs ((x,y)::prev)

theorem choices_of_embedding {α β : Type} [DecidableEq α] [DecidableEq β]
    {H : SimpleGraph α} {G : SimpleGraph β} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (f : H ↪g G) (cand : List β) (hall : ∀ b, b ∈ cand) (xs : List α) (p : List (α×β))
    (hp : ∀ z ∈ p, f z.1 = z.2) : choices H G cand xs p = true := by
  induction xs generalizing p with
  | nil => rfl
  | cons x xs ih =>
    simp only [choices,List.any_eq_true,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
    refine ⟨f x,hall _,?_,ih _ ?_⟩
    · intro z hz
      rw [← hp z hz]
      exact ⟨f.injective.eq_iff.symm,f.map_rel_iff.symm⟩
    · intro z h
      rcases List.mem_cons.mp h with rfl|hz
      · rfl
      · exact hp z hz

theorem fail_choices {α : Type} [DecidableEq α] {n : ℕ}
    {H : SimpleGraph α} {G : SimpleGraph (Fin n)} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (xs : List α) (h : choices H G (List.finRange n) xs [] = false) : ¬ Nonempty (H ↪g G) := by
  rintro ⟨f⟩
  have := choices_of_embedding f (List.finRange n) (by simp) xs [] (by simp)
  simp_all

def certifiedMap {α β : Type} (H : SimpleGraph α) (G : SimpleGraph β)
    (f : α → β) (h : ∀ x y, (f x = f y ↔ x=y) ∧ (G.Adj (f x) (f y) ↔ H.Adj x y)) :
    H ↪g G where
  toFun := f
  inj' := fun x y => (h x y).1.mp
  map_rel_iff' := (h _ _).2

private instance decSumRel {α β : Type} (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G ⊕g H).Adj
  | Sum.inl x, Sum.inl y => inferInstanceAs (Decidable (G.Adj x y))
  | Sum.inr x, Sum.inr y => inferInstanceAs (Decidable (H.Adj x y))
  | Sum.inl _, Sum.inr _ => isFalse (by simp)
  | Sum.inr _, Sum.inl _ => isFalse (by simp)

private instance decBi (α β : Type) : DecidableRel (completeBipartiteGraph α β).Adj :=
  fun x y => inferInstanceAs (Decidable ((x.isLeft ∧ y.isRight) ∨ (x.isRight ∧ y.isLeft)))

end FiniteChecks

theorem pair_ei : cp (bits 5 792) = cp (bits 5 541200) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 5 792) = [0, 0, 0, -4, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 5 541200) = [0, 0, 0, -4, 0, 1] by decide +kernel).symm

theorem seed_ei : ¬ RS ((clq 2) ⊞ (clq 1)) := by
  intro h
  have hp : Has ((clq 2) ⊞ (clq 1)) (bits 5 792) := by
    exact ⟨certifiedMap ((completeGraph (Fin 2)) ⊕g (completeGraph (Fin 1))) (bitsGraph 5 792) (Sum.elim ![0,3] ![2]) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_ei).mp hp
  exact fail_choices (H := ((completeGraph (Fin 2)) ⊕g (completeGraph (Fin 1)))) (G := bitsGraph 5 541200)
    [.inl 0,.inl 1,.inr 0] (by decide +kernel) hh

theorem seed_ip : ¬ RS ((clq 1) ⊞ (bic 1 2)) := by
  intro h
  have hp : Has ((clq 1) ⊞ (bic 1 2)) (bits 5 792) := by
    exact ⟨certifiedMap ((completeGraph (Fin 1)) ⊕g (completeBipartiteGraph (Fin 1) (Fin 2))) (bitsGraph 5 792) (Sum.elim ![2] (Sum.elim ![0] ![3,4])) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_ei).mp hp
  exact fail_choices (H := ((completeGraph (Fin 1)) ⊕g (completeBipartiteGraph (Fin 1) (Fin 2)))) (G := bitsGraph 5 541200)
    [.inl 0,.inr (.inl 0),.inr (.inr 0),.inr (.inr 1)] (by decide +kernel) hh

theorem pair_ep : cp (bits 6 8521744) = cp (bits 6 3112) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 6 8521744) = [0, 0, 3, 0, -4, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 6 3112) = [0, 0, 3, 0, -4, 0, 1] by decide +kernel).symm

theorem seed_ep : ¬ RS ((clq 2) ⊞ (bic 1 2)) := by
  intro h
  have hp : Has ((clq 2) ⊞ (bic 1 2)) (bits 6 8521744) := by
    exact ⟨certifiedMap ((completeGraph (Fin 2)) ⊕g (completeBipartiteGraph (Fin 1) (Fin 2))) (bitsGraph 6 8521744) (Sum.elim ![0,4] (Sum.elim ![5] ![1,2])) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_ep).mp hp
  exact fail_choices (H := ((completeGraph (Fin 2)) ⊕g (completeBipartiteGraph (Fin 1) (Fin 2)))) (G := bitsGraph 6 3112)
    [.inl 0,.inl 1,.inr (.inl 0),.inr (.inr 0),.inr (.inr 1)] (by decide +kernel) hh

theorem pair_ee : cp (bits 6 199688) = cp (bits 6 545391632) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 6 199688) = [0, 0, 4, 0, -5, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 6 545391632) = [0, 0, 4, 0, -5, 0, 1] by decide +kernel).symm

theorem seed_ee : ¬ RS ((clq 2) ⊞ (clq 2)) := by
  intro h
  have hp : Has ((clq 2) ⊞ (clq 2)) (bits 6 199688) := by
    exact ⟨certifiedMap ((completeGraph (Fin 2)) ⊕g (completeGraph (Fin 2))) (bitsGraph 6 199688) (Sum.elim ![0,3] ![1,4]) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_ee).mp hp
  exact fail_choices (H := ((completeGraph (Fin 2)) ⊕g (completeGraph (Fin 2)))) (G := bitsGraph 6 545391632)
    [.inl 0,.inl 1,.inr 0,.inr 1] (by decide +kernel) hh

theorem pair_et : cp (bits 6 537070600) = cp (bits 6 545262632) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 6 537070600) = [0, 4, 5, -4, -6, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 6 545262632) = [0, 4, 5, -4, -6, 0, 1] by decide +kernel).symm

theorem seed_et : ¬ RS ((clq 2) ⊞ (clq 3)) := by
  intro h
  have hp : Has ((clq 2) ⊞ (clq 3)) (bits 6 537070600) := by
    exact ⟨certifiedMap ((completeGraph (Fin 2)) ⊕g (completeGraph (Fin 3))) (bitsGraph 6 537070600) (Sum.elim ![0,3] ![1,4,5]) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_et).mp hp
  exact fail_choices (H := ((completeGraph (Fin 2)) ⊕g (completeGraph (Fin 3)))) (G := bitsGraph 6 545262632)
    [.inl 0,.inl 1,.inr 0,.inr 1,.inr 2] (by decide +kernel) hh

theorem pair_it : cp (bits 6 545325624) = cp (bits 6 545393704) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 6 545325624) = [-1, 4, 7, -4, -7, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 6 545393704) = [-1, 4, 7, -4, -7, 0, 1] by decide +kernel).symm

theorem seed_it : ¬ RS ((clq 1) ⊞ (clq 3)) := by
  intro h
  have hp : Has ((clq 1) ⊞ (clq 3)) (bits 6 545325624) := by
    exact ⟨certifiedMap ((completeGraph (Fin 1)) ⊕g (completeGraph (Fin 3))) (bitsGraph 6 545325624) (Sum.elim ![1] ![0,4,5]) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_it).mp hp
  exact fail_choices (H := ((completeGraph (Fin 1)) ⊕g (completeGraph (Fin 3)))) (G := bitsGraph 6 545393704)
    [.inl 0,.inr 0,.inr 1,.inr 2] (by decide +kernel) hh

theorem pair_pp : cp (bits 7 17248561232) = cp (bits 7 2216270770256) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 7 17248561232) = [0, -2, 8, 13, -4, -8, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 7 2216270770256) = [0, -2, 8, 13, -4, -8, 0, 1] by decide +kernel).symm

theorem seed_pp : ¬ RS ((bic 1 2) ⊞ (bic 1 2)) := by
  intro h
  have hp : Has ((bic 1 2) ⊞ (bic 1 2)) (bits 7 17248561232) := by
    exact ⟨certifiedMap ((completeBipartiteGraph (Fin 1) (Fin 2)) ⊕g (completeBipartiteGraph (Fin 1) (Fin 2))) (bitsGraph 7 17248561232) (Sum.elim (Sum.elim ![4] ![0,1]) (Sum.elim ![5] ![2,3])) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_pp).mp hp
  exact fail_choices (H := ((completeBipartiteGraph (Fin 1) (Fin 2)) ⊕g (completeBipartiteGraph (Fin 1) (Fin 2)))) (G := bitsGraph 7 2216270770256)
    [.inl (.inl 0),.inl (.inr 0),.inl (.inr 1),.inr (.inl 0),.inr (.inr 0),.inr (.inr 1)] (by decide +kernel) hh

theorem pair_iii : cp (bits 7 2225029789816) = cp (bits 7 2224794910332) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 7 2225029789816) = [0, 6, 8, -15, -32, -16, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 7 2224794910332) = [0, 6, 8, -15, -32, -16, 0, 1] by decide +kernel).symm

theorem seed_iii : ¬ RS (((clq 1) ⊞ (clq 1)) ⊞ (clq 1)) := by
  intro h
  have hp : Has (((clq 1) ⊞ (clq 1)) ⊞ (clq 1)) (bits 7 2225029789816) := by
    exact ⟨certifiedMap (((completeGraph (Fin 1)) ⊕g (completeGraph (Fin 1))) ⊕g (completeGraph (Fin 1))) (bitsGraph 7 2225029789816) (Sum.elim (Sum.elim ![0] ![1]) ![2]) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_iii).mp hp
  exact fail_choices (H := (((completeGraph (Fin 1)) ⊕g (completeGraph (Fin 1))) ⊕g (completeGraph (Fin 1)))) (G := bitsGraph 7 2224794910332)
    [.inl (.inl 0),.inl (.inr 0),.inr 0] (by decide +kernel) hh

theorem pair_pt : cp (bits 8 141289395863712) = cp (bits 8 140738574688416) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 8 141289395863712) = [0, 0, -4, 4, 12, -2, -7, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 8 140738574688416) = [0, 0, -4, 4, 12, -2, -7, 0, 1] by decide +kernel).symm

theorem seed_pt : ¬ RS ((bic 1 2) ⊞ (clq 3)) := by
  intro h
  have hp : Has ((bic 1 2) ⊞ (clq 3)) (bits 8 141289395863712) := by
    exact ⟨certifiedMap ((completeBipartiteGraph (Fin 1) (Fin 2)) ⊕g (completeGraph (Fin 3))) (bitsGraph 8 141289395863712) (Sum.elim (Sum.elim ![6] ![1,2]) ![0,5,7]) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_pt).mp hp
  exact fail_choices (H := ((completeBipartiteGraph (Fin 1) (Fin 2)) ⊕g (completeGraph (Fin 3)))) (G := bitsGraph 8 140738574688416)
    [.inl (.inl 0),.inl (.inr 0),.inl (.inr 1),.inr 0,.inr 1,.inr 2] (by decide +kernel) hh

theorem pair_tt : cp (bits 8 36028937691775024) = cp (bits 8 552178049176) := by
  rw [cp_bits, cp_bits]
  apply congrArg decode
  exact (show detCoeffs (pencil 8 36028937691775024) = [0, 0, 12, 32, 21, -8, -10, 0, 1] by decide +kernel).trans
    (show detCoeffs (pencil 8 552178049176) = [0, 0, 12, 32, 21, -8, -10, 0, 1] by decide +kernel).symm

theorem seed_tt : ¬ RS ((clq 3) ⊞ (clq 3)) := by
  intro h
  have hp : Has ((clq 3) ⊞ (clq 3)) (bits 8 36028937691775024) := by
    exact ⟨certifiedMap ((completeGraph (Fin 3)) ⊕g (completeGraph (Fin 3))) (bitsGraph 8 36028937691775024) (Sum.elim ![0,4,5] ![1,6,7]) (by decide +kernel)⟩
  obtain hh := (h _ _ pair_tt).mp hp
  exact fail_choices (H := ((completeGraph (Fin 3)) ⊕g (completeGraph (Fin 3)))) (G := bitsGraph 8 552178049176)
    [.inl 0,.inl 1,.inl 2,.inr 0,.inr 1,.inr 2] (by decide +kernel) hh



end
end Barranca
