import Conjectures.NabergallChordalDiagrams.Cuts

/-! # Cycles at a clique separator

Deleting the vertices of a clique from an induced long cycle leaves at most
one component. Cut the cycle just after a deleted vertex. Between any two
remaining indices in the resulting linear order, the strict intermediate
indices are not neighbors of that deleted vertex.
-/

namespace NabergallChordalDiagrams

theorem cyclicNeighbor_iff {k : ℕ} (i j : Fin k) : CyclicNeighbor i j ↔
    i.val+1 = j.val ∨ j.val+1 = i.val ∨ (i.val+1=k ∧ j.val=0) ∨ (j.val+1=k ∧ i.val=0) := by
  have wrap (p : Fin k) : (p.val+1)%k = if p.val+1=k then 0 else p.val+1 := by
    split
    · rename_i h; rw [h, Nat.mod_self]
    · apply Nat.mod_eq_of_lt; have := p.isLt; omega
  rw [CyclicNeighbor, wrap, wrap]
  split <;> split <;> have := i.isLt <;> have := j.isLt <;> omega

private def rotate {k : ℕ} (b i : Fin k) : Fin k :=
  ⟨if b.val+i.val < k then b.val+i.val else b.val+i.val-k, by
    have := b.isLt; have := i.isLt; split <;> omega⟩

private theorem rotate_surj {k : ℕ} (b : Fin k) : Function.Surjective (rotate b) := by
  intro i
  have hb := b.isLt
  have hi := i.isLt
  by_cases h : b.val ≤ i.val
  · refine ⟨⟨i.val-b.val, by omega⟩, Fin.ext ?_⟩
    change (if b.val+(i.val-b.val)<k then b.val+(i.val-b.val) else b.val+(i.val-b.val)-k) = i.val
    split <;> omega
  · refine ⟨⟨k-b.val+i.val, by omega⟩, Fin.ext ?_⟩
    change (if b.val+(k-b.val+i.val)<k then b.val+(k-b.val+i.val) else b.val+(k-b.val+i.val)-k) = i.val
    split <;> omega

private theorem rotate_adj {k : ℕ} (b i j : Fin k) :
    CyclicNeighbor (rotate b i) (rotate b j) ↔ CyclicNeighbor i j := by
  simp only [cyclicNeighbor_iff, rotate]
  have := b.isLt; have := i.isLt; have := j.isLt
  split <;> split <;> omega

private theorem transfer_interval {k : ℕ} (Q : Fin k → Prop) {i j : Fin k} (hij : i ≤ j)
    (step : ∀ a b : Fin k, i ≤ a → b ≤ j → a.val+1=b.val → (Q a ↔ Q b)) : Q i ↔ Q j := by
  suffices aux : ∀ d (b : Fin k), b.val = i.val+d → b ≤ j → (Q i ↔ Q b) by
    exact aux (j.val-i.val) j (by change i.val ≤ j.val at hij; omega) le_rfl
  intro d
  induction d with
  | zero =>
      intro b hb _
      have e : b=i := Fin.ext (by simpa using hb)
      rw [e]
  | succ d ih =>
      intro b hb hj
      let a : Fin k := ⟨i.val+d, by have := b.isLt; omega⟩
      have ha : a.val = i.val+d := rfl
      exact (ih a ha (by change _ ≤ j.val at hj ⊢; omega)).trans
        (step a b (by change i.val ≤ _; omega) hj (by omega))

/-- Two sides with no edges between them cannot both occur off a clique
on a single induced cycle. Here `K` and `P` are already pulled back to
the cycle indices. -/
theorem constant_off_cycle_clique {k : ℕ} (K P : Fin k → Prop)
    (cl : ∀ i j, K i → K j → i ≠ j → CyclicNeighbor i j)
    (step : ∀ i j, ¬K i → ¬K j → CyclicNeighbor i j → (P i ↔ P j))
    (i j : Fin k) (hi : ¬ K i) (hj : ¬ K j) : P i ↔ P j := by
  classical
  by_cases existsK : ∃ b, K b
  · obtain ⟨b, hb⟩ := existsK
    have lin (u v : Fin k) (huv : u ≤ v) (hu : ¬ K (rotate b u)) (hv : ¬ K (rotate b v)) :
        P (rotate b u) ↔ P (rotate b v) := by
      have nz : u.val ≠ 0 := by
        intro e
        have eu : rotate b u = b := Fin.ext (by simp [rotate, e, b.isLt])
        exact hu (eu.symm ▸ hb)
      have off (t : Fin k) (hut : u ≤ t) (htv : t ≤ v) : ¬ K (rotate b t) := by
        by_cases e : t=u
        · exact e ▸ hu
        by_cases f : t=v
        · exact f ▸ hv
        have h₁ : u.val < t.val := (lt_of_le_of_ne hut (Ne.symm e) : u < t)
        have h₂ : t.val < v.val := (lt_of_le_of_ne htv f : t < v)
        have hv' := v.isLt
        let z : Fin k := ⟨0, by have := t.isLt; omega⟩
        have ez : rotate b z = b := Fin.ext (by simp [rotate, z, b.isLt])
        intro h
        have hne : b ≠ rotate b t := by
          intro hh
          have hh' := congrArg Fin.val hh
          change b.val = (if b.val+t.val<k then b.val+t.val else b.val+t.val-k) at hh'
          have := b.isLt; have := t.isLt; split at hh' <;> omega
        have nb := cl (rotate b z) (rotate b t) (ez.symm ▸ hb) h (by simpa only [ez] using hne)
        have n := (rotate_adj b z t).mp nb
        rw [cyclicNeighbor_iff] at n
        change 0+1 = t.val ∨ t.val+1=0 ∨ (0+1=k ∧ t.val=0) ∨ (t.val+1=k ∧ 0=0) at n
        omega
      apply transfer_interval (fun t => P (rotate b t)) huv
      intro x y hx hy e
      have hxy : x ≤ y := by change x.val ≤ y.val; omega
      exact step _ _ (off _ hx (hxy.trans hy)) (off _ (hx.trans hxy) hy)
        ((rotate_adj b x y).mpr ((cyclicNeighbor_iff x y).mpr (Or.inl e)))
    obtain ⟨u,rfl⟩ := rotate_surj b i
    obtain ⟨v,rfl⟩ := rotate_surj b j
    rcases le_total u v with huv | hvu
    · exact lin _ _ huv hi hj
    · exact (lin _ _ hvu hj hi).symm
  · have lin (u v : Fin k) (h : u ≤ v) : P u ↔ P v :=
      transfer_interval P h (fun a b _ _ e => step a b
        (fun h => existsK ⟨_,h⟩) (fun h => existsK ⟨_,h⟩)
        ((cyclicNeighbor_iff _ _).mpr (Or.inl e)))
    rcases le_total i j with h | h
    · exact lin _ _ h
    · exact (lin _ _ h).symm

namespace Window

/-- An induced cycle containing an internal chord of a good window lies
entirely on chords touching the window. -/
theorem hole_hits {N L k : ℕ} (W : Window N L) (F : Fragment N)
    (hg : W.Good F) (f : Fin k → F.Chord) (inj : Function.Injective f)
    (cyc : ∀ i j, F.graph.Adj (f i) (f j) ↔ CyclicNeighbor i j)
    {i : Fin k} (hi : W.Internal F (f i)) (j : Fin k) : W.Hits F (f j) := by
  classical
  by_contra! hj
  have start : W.Hits F (f i) := Or.inl hi.1
  have t := constant_off_cycle_clique (fun q => W.Boundary F (f q)) (fun q => W.Hits F (f q))
    (fun a b ha hb hn => (cyc _ _).mp (hg _ ha _ hb (inj.ne hn)))
    (fun a b ha hb nb =>
      let e := (cyc _ _).mpr nb
      ⟨fun hx => W.hits_of_adj_internal F (Classical.byContradiction fun h => ha ⟨hx,h⟩) e,
       fun hy => W.hits_of_adj_internal F (Classical.byContradiction fun h => hb ⟨hy,h⟩) e.symm⟩)
    i j (fun h => h.2 hi) (fun h => hj h.1)
  exact hj (t.mp start)

theorem no_hole_through_internal {N L k : ℕ} (W : Window N L) (F : Fragment N)
    (hg : W.Good F) (ch : Chordal (W.restrict F).graph) (hk : 4 ≤ k)
    (f : Fin k → F.Chord) (inj : Function.Injective f)
    (cyc : ∀ i j, F.graph.Adj (f i) (f j) ↔ CyclicNeighbor i j)
    {i : Fin k} (hi : W.Internal F (f i)) : False := by
  classical
  have hall (j) := (W.hits_iff_image _ _).mp (W.hole_hits F hg f inj cyc hi j)
  choose g h using hall
  exact ch k hk g (fun x y e => inj (by rw [← h x, ← h y, e])) fun a b => by
    rw [← W.adj_map_iff F hg, h, h, cyc]

end Window
end NabergallChordalDiagrams
