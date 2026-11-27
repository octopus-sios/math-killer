import Conjectures.NabergallChordalDiagrams.Polygon
import Conjectures.NabergallChordalDiagrams.Split

/-!
# Existence of an admissible split

In a polygon with a distinguished exterior side, a good diagonal replaces
the block not containing that side by one new side. Follow the subpolygon
incident with the exterior. When it is a triangle, the other two sides
are exactly the required two nonempty intervals.
-/

namespace NabergallChordalDiagrams
namespace Polygon

private def squash {d} (I : Diagonal d) (n : ℕ) :=
  if n < I.s then n else if n < I.e then I.s else n-(I.e-I.s-1)

private theorem squash_mono {d} (I : Diagonal d) : Monotone (squash I) := by
  intro i j h
  have := I.span
  simp only [squash]
  split <;> split <;> (try split) <;> (try split) <;> omega

private theorem squash_eq_pivot {d} (I : Diagonal d) (n : ℕ) :
    squash I n = I.s ↔ I.In n := by
  have := I.span
  simp only [squash, Diagonal.In]; split <;> (try split) <;> omega

private theorem squash_other {d} (I : Diagonal d) (n q : ℕ) (h : q ≠ I.s) :
    squash I n = q → n = (if q < I.s then q else q+(I.e-I.s-1)) := by
  have := I.span
  simp only [squash]; split <;> split <;> (try split) <;> omega

/-- Sector labels on the linearly displayed completion; label zero is
the exterior and the first and last original positions keep their extreme labels. -/
private structure Slice {N} (F : Fragment N) (d : ℕ) where
  tag : ℕ → ℕ
  mono : Monotone tag
  exterior : ∀ p < N, tag p = 0
  first : tag N = 1
  last : tag (N+(N-1)) = d-1
  clique : ∀ s (c e : F.Chord), c ≠ e →
    tag (F.start c.val) < tag (N+c.val.val) → tag (F.start e.val) < tag (N+e.val.val) →
    (tag (F.start c.val)=s ∨ tag (N+c.val.val)=s) →
    (tag (F.start e.val)=s ∨ tag (N+e.val.val)=s) → F.graph.Adj c e

private theorem start_le {N} (F : Fragment N) (c : F.Chord) : F.start c.val ≤ N+c.val.val := by
  have hc := c.property
  change _ ≤ c.val.val at hc
  simp only [Fragment.start]; split <;> omega

private def Slice.system {N d} {F : Fragment N} (T : Slice F d) (hd : 0<d) : Sectors F.graph d where
  lo c := T.tag (F.start c.val)
  hi c := T.tag (N+c.val.val)
  le x := T.mono (start_le F x)
  bound x := by
    have hx := x.val.isLt
    have := T.mono (show N+x.val.val ≤ N+(N-1) by omega)
    rw [T.last] at this; omega
  forces x y h := by
    have ref {i j} (h : T.tag i < T.tag j) : i<j := lt_of_not_ge (fun e => (not_le_of_gt h) (T.mono e))
    rcases h with h|h
    · exact Or.inl ⟨ref h.1,ref h.2.1,ref h.2.2⟩
    · exact Or.inr ⟨ref h.1,ref h.2.1,ref h.2.2⟩
  weak x y h := by
    rcases h with h|h
    · exact .inl ⟨T.mono h.1.le,T.mono h.2.1.le,T.mono h.2.2.le⟩
    · exact .inr ⟨T.mono h.1.le,T.mono h.2.1.le,T.mono h.2.2.le⟩
  sector s c e hc he ne := T.clique s c e ne hc he

private def Slice.contract {N d} {F : Fragment N} (T : Slice F d) (hd : 0<d)
    (I : Diagonal d) (good : (T.system hd).Good I) : Slice F (d-(I.e-I.s-1)) where
  tag n := squash I (T.tag n)
  mono := (squash_mono I).comp T.mono
  exterior p hp := by rw [T.exterior p hp]; simp [squash, I.pos]
  first := by rw [T.first]; have := I.pos; have := I.span; dsimp [squash]; split <;> (try split) <;> omega
  last := by rw [T.last]; have := I.span; have := I.bound; dsimp [squash]; split <;> (try split) <;> omega
  clique s c e ne hc he ic ie := by
    by_cases eq : s = I.s
    · apply good _ _ ne
      all_goals
        rw [eq] at ic ie
      · change ¬(I.In (T.tag (F.start c.val)) ↔ I.In (T.tag (N+c.val.val)))
        rw [← squash_eq_pivot, ← squash_eq_pivot]; omega
      · change ¬(I.In (T.tag (F.start e.val)) ↔ I.In (T.tag (N+e.val.val)))
        rw [← squash_eq_pivot, ← squash_eq_pivot]; omega
    · apply T.clique _ _ _ ne
      · exact lt_of_not_ge fun h => (not_le_of_gt hc) (squash_mono I h)
      · exact lt_of_not_ge fun h => (not_le_of_gt he) (squash_mono I h)
      · exact ic.imp (squash_other I _ _ eq) (squash_other I _ _ eq)
      · exact ie.imp (squash_other I _ _ eq) (squash_other I _ _ eq)

private def initial {N} (F : Fragment N) (hn : 1 ≤ N) : Slice F (N+1) where
  tag x := x+1-N
  mono := fun i j h => by change i+1-N ≤ j+1-N; omega
  exterior p h := by omega
  first := by omega
  last := by omega
  clique s c e ne _ _ ic ie := by
    have ends (c : F.Chord) : N+c.val.val+1-N = c.val.val+1 := by omega
    have lo (c : F.Chord) : F.start c.val+1-N =
        if F.mate c.val = c.val then 0 else (F.mate c.val).val+1 := by
      have := c.val.isLt
      simp only [Fragment.start]; split <;> omega
    rw [lo,ends] at ic ie
    by_cases h : s=0
    · have fix (c : F.Chord)
          (hc : (if F.mate c.val=c.val then 0 else (F.mate c.val).val+1)=s ∨ c.val.val+1=s) :
          F.mate c.val=c.val := by split at hc <;> omega
      exact (F.adj_fixed c e (fix c ic) (fix e ie)).mpr ne
    · have endpoint (c : F.Chord)
          (hc : (if F.mate c.val=c.val then 0 else (F.mate c.val).val+1)=s ∨ c.val.val+1=s) :
          ∃ p : Fin N, p.val+1=s ∧ F.chordAt p=c := by
        rcases hc with hc|hc
        · split at hc
          · omega
          · exact ⟨_,hc,(F.chordAt_mate _).trans (F.chordAt_right c)⟩
        · exact ⟨_,hc,F.chordAt_right c⟩
      obtain ⟨u,hu,eu⟩ := endpoint c ic
      obtain ⟨v,hv,ev⟩ := endpoint e ie
      exact (ne (eu.symm.trans ((congrArg F.chordAt (Fin.ext (by omega) : u=v)).trans ev))).elim

private theorem triangle {N} {F : Fragment N} (T : Slice F 3) (hn : 2 ≤ N) :
    ∃ g, 0<g ∧ g<N ∧ Admissible F g := by
  classical
  have ex : ∃ g, g<N ∧ T.tag (N+g)=2 := ⟨N-1,by omega,T.last⟩
  let g := Nat.find ex
  obtain ⟨glt,tagg⟩ := Nat.find_spec ex
  change g<N at glt
  change T.tag (N+g)=2 at tagg
  have gp : 0<g := by
    by_contra! h; have e : g=0 := by omega
    rw [e,Nat.add_zero,T.first] at tagg; contradiction
  have gr (p : Fin N) : T.tag (N+p.val) = if p.val<g then 1 else 2 := by
    have lo := T.mono (Nat.le_add_right N p.val)
    have hp := p.isLt
    have hi := T.mono (show N+p.val ≤ N+(N-1) by omega)
    rw [T.first] at lo; rw [T.last] at hi
    split
    · rename_i h
      have := Nat.find_min ex h
      omega
    · rename_i h
      have := T.mono (show N+g ≤ N+p.val by omega)
      omega
  have sectors (c : F.Chord) (hc : Central F g c) :
      (T.tag (F.start c.val) = 0 ∧ (T.tag (N+c.val.val)=1 ∨ T.tag (N+c.val.val)=2)) ∨
      (T.tag (F.start c.val) = 1 ∧ T.tag (N+c.val.val)=2) := by
    rcases hc with h | ⟨h₁,h₂⟩
    · left; rw [Fragment.start, ite_eq_left h, T.exterior _ c.val.isLt, gr]; split <;> simp
    · have h : F.mate c.val ≠ c.val := fun e => by rw [e] at h₁; omega
      right; rw [Fragment.start, ite_eq_right h, gr, gr, ite_eq_left h₁, ite_eq_right (not_lt.mpr h₂)]
      exact ⟨rfl,rfl⟩
  refine ⟨g,gp,glt,fun c hc e he ne => ?_⟩
  have cc := sectors c hc; have ee := sectors e he
  have cl : T.tag (F.start c.val)<T.tag (N+c.val.val) := by omega
  have el : T.tag (F.start e.val)<T.tag (N+e.val.val) := by omega
  by_cases h : T.tag (F.start c.val)=T.tag (F.start e.val)
  · exact T.clique _ _ _ ne cl el (.inl h) (.inl rfl)
  by_cases h' : T.tag (N+c.val.val)=T.tag (N+e.val.val)
  · exact T.clique _ _ _ ne cl el (.inr h') (.inr rfl)
  by_cases h'' : T.tag (F.start c.val)=T.tag (N+e.val.val)
  · exact T.clique _ _ _ ne cl el (.inl h'') (.inr rfl)
  exact T.clique _ _ _ ne cl el (.inr (by omega)) (.inl rfl)

end Polygon

/-- Section 2. The sides are initially the individual positions and the
exterior marker block. Repeated good diagonals find the triangle at the
exterior. No assumption about the number of four-cycles suffices here:
chordality was used for an arbitrary-length hole in the separator lemma. -/
theorem exists_admissible {N} (F : Fragment N) (hc : Chordal F.graph) (hn : 2 ≤ N) :
    ∃ g, 0<g ∧ g<N ∧ Admissible F g := by
  suffices h : ∀ d, 3 ≤ d → Polygon.Slice F d → ∃ g, 0<g ∧ g<N ∧ Admissible F g by
    exact h (N+1) (by omega) (Polygon.initial F (by omega))
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd T
    by_cases he : d=3
    · subst d; exact Polygon.triangle T hn
    · have h₄ : 4≤d := by omega
      have pos : 0<d := by omega
      obtain ⟨I,hI⟩ := (T.system pos).exists_good_diagonal h₄ hc
      have := I.pos; have := I.span; have := I.bound; have := I.other
      exact ih _ (show d-(I.e-I.s-1)<d by omega) (by omega) (T.contract pos I hI)

end NabergallChordalDiagrams
