import Conjectures.NabergallChordalDiagrams.Clique
import Mathlib.Data.Finset.Sort

/-! # The three sectors at a split -/

namespace NabergallChordalDiagrams

variable {N L R : ℕ}

def leftWindow (L R : ℕ) : Window (L+R) L := ⟨0, by omega⟩
def rightWindow (L R : ℕ) : Window (L+R) R := ⟨L, le_rfl⟩

/-- The central strands join distinct sectors: some are singletons going to
the exterior and the rest are links crossing the split. -/
def Central (F : Fragment N) (g : ℕ) (c : F.Chord) :=
  F.mate c.val = c.val ∨ ((F.mate c.val).val < g ∧ g ≤ c.val.val)

/-- The clique test for a specified gap. Positive lengths on both sides
are separate from this test. -/
def Admissible (F : Fragment N) (g : ℕ) :=
  ∀ c, Central F g c → ∀ d, Central F g d → c ≠ d → F.graph.Adj c d

section
variable (F : Fragment (L+R))

theorem boundary_leftWindow (c : F.Chord) :
    (leftWindow L R).Boundary F c ↔
      (F.mate c.val = c.val ∧ c.val.val < L) ∨ ((F.mate c.val).val < L ∧ L ≤ c.val.val) := by
  have hc := c.property
  change _ ≤ c.val.val at hc
  simp only [Window.Boundary, Window.Hits, Window.Internal, Window.Contains, leftWindow,
    Nat.zero_le, zero_add, true_and, Fin.ext_iff]
  omega

theorem boundary_rightWindow (c : F.Chord) :
    (rightWindow L R).Boundary F c ↔
      (F.mate c.val = c.val ∧ L ≤ c.val.val) ∨ ((F.mate c.val).val < L ∧ L ≤ c.val.val) := by
  have hc := c.property
  change _ ≤ c.val.val at hc
  have := c.val.isLt; have := (F.mate c.val).isLt
  simp only [Window.Boundary, Window.Hits, Window.Internal, Window.Contains, rightWindow, Fin.ext_iff]
  omega

theorem central_iff_boundary (c : F.Chord) : Central F L c ↔
    (leftWindow L R).Boundary F c ∨ (rightWindow L R).Boundary F c := by
  rw [boundary_leftWindow, boundary_rightWindow, Central]
  omega

theorem admissible_iff_good : Admissible F L ↔ (leftWindow L R).Good F ∧ (rightWindow L R).Good F := by
  refine ⟨fun h => ⟨fun a ha b hb => h a ((central_iff_boundary _ _).mpr (.inl ha)) b
      ((central_iff_boundary _ _).mpr (.inl hb)),
    fun a ha b hb => h a ((central_iff_boundary _ _).mpr (.inr ha)) b
      ((central_iff_boundary _ _).mpr (.inr hb))⟩, ?_⟩
  rintro ⟨hl,hr⟩ c (hc|hc) d (hd|hd) e
  · exact (F.adj_fixed c d hc hd).mpr e
  · by_cases h : c.val.val < L
    · exact hl c ((boundary_leftWindow _ _).mpr (.inl ⟨hc,h⟩)) d ((boundary_leftWindow _ _).mpr (.inr hd)) e
    · exact hr c ((boundary_rightWindow _ _).mpr (.inl ⟨hc,by omega⟩)) d ((boundary_rightWindow _ _).mpr (.inr hd)) e
  · by_cases h : d.val.val < L
    · exact hl c ((boundary_leftWindow _ _).mpr (.inr hc)) d ((boundary_leftWindow _ _).mpr (.inl ⟨hd,h⟩)) e
    · exact hr c ((boundary_rightWindow _ _).mpr (.inr hc)) d ((boundary_rightWindow _ _).mpr (.inl ⟨hd,by omega⟩)) e
  · exact hl c ((boundary_leftWindow _ _).mpr (.inr hc)) d ((boundary_leftWindow _ _).mpr (.inr hd)) e

theorem central_of_not_internal (c : F.Chord) (hl : ¬ (leftWindow L R).Internal F c)
    (hr : ¬ (rightWindow L R).Internal F c) : Central F L c := by
  have hc := c.property
  change _ ≤ c.val.val at hc
  have := c.val.isLt; have := (F.mate c.val).isLt
  simp only [Window.Internal, Window.Contains, leftWindow, rightWindow, Nat.zero_le, zero_add,
    true_and, Fin.ext_iff, Central] at *
  omega

theorem hits_either (c : F.Chord) : (leftWindow L R).Hits F c ∨ (rightWindow L R).Hits F c := by
  by_cases h : c.val.val < L
  · exact .inl (.inl ⟨by exact Nat.zero_le _, by simpa [leftWindow] using h⟩)
  · exact .inr (.inl ⟨by change L ≤ _; omega, c.val.isLt⟩)

theorem chordal_of_restrictions (ha : Admissible F L)
    (hl : Chordal ((leftWindow L R).restrict F).graph)
    (hr : Chordal ((rightWindow L R).restrict F).graph) : Chordal F.graph := by
  intro k hk f inj cyc
  obtain ⟨gl,gr⟩ := (admissible_iff_good F).mp ha
  have hall (i) : Central F L (f i) := central_of_not_internal F _
    ((leftWindow L R).no_hole_through_internal F gl hl hk f inj cyc)
    ((rightWindow L R).no_hole_through_internal F gr hr hk f inj cyc)
  let i : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨2, by omega⟩
  have e : i ≠ j := fun h => by have := congrArg Fin.val h; contradiction
  have hh := (cyc i j).mp (ha _ (hall i) _ (hall j) (inj.ne e))
  rw [cyclicNeighbor_iff] at hh
  change 0+1 = 2 ∨ 2+1=0 ∨ (0+1=k ∧ 2=0) ∨ (2+1=k ∧ 0=0) at hh
  omega

private theorem boundary_from_weight {n} (W : Window (L+R) n) (h : 0 < (W.restrict F).weight) :
    ∃ a : (W.restrict F).Chord, W.Boundary F (W.chordMap F a) := by
  obtain ⟨p,hp⟩ := Finset.card_pos.mp h
  have e := ((W.restrict F).mem_singletons _).mp hp
  exact ⟨⟨p,e.le⟩, (W.boundary_chordMap_iff _ _).mpr e⟩

theorem valid_of_restrictions (ha : Admissible F L)
    (vl : ((leftWindow L R).restrict F).Valid) (vr : ((rightWindow L R).restrict F).Valid)
    (pl : 0 < ((leftWindow L R).restrict F).weight) (pr : 0 < ((rightWindow L R).restrict F).weight) :
    F.Valid := by
  obtain ⟨gl,gr⟩ := (admissible_iff_good F).mp ha
  refine ⟨?_, chordal_of_restrictions F ha vl.2 vr.2⟩
  obtain ⟨a,ha'⟩ := boundary_from_weight F (leftWindow L R) pl
  obtain ⟨b,hb'⟩ := boundary_from_weight F (rightWindow L R) pr
  have ab : F.graph.Reachable ((leftWindow L R).chordMap F a) ((rightWindow L R).chordMap F b) := by
    by_cases e : (leftWindow L R).chordMap F a = (rightWindow L R).chordMap F b
    · rw [e]
    · exact (ha _ ((central_iff_boundary F _).mpr (.inl ha')) _
        ((central_iff_boundary F _).mpr (.inr hb')) e).reachable
  have reach {n} (W : Window (L+R) n) (hg : W.Good F) (conn : (W.restrict F).graph.Connected)
      (x y : (W.restrict F).Chord) : F.graph.Reachable (W.chordMap F x) (W.chordMap F y) :=
    let f : (W.restrict F).graph →g F.graph := ⟨W.chordMap F, fun e => (W.adj_map_iff F hg _ _).mpr e⟩
    (conn x y).map f
  apply (F.graph.connected_iff_exists_forall_reachable).mpr
  refine ⟨(leftWindow L R).chordMap F a, fun c => ?_⟩
  rcases hits_either F c with h | h
  · obtain ⟨x,rfl⟩ := ((leftWindow L R).hits_iff_image F _).mp h
    exact reach _ gl vl.1 a x
  · obtain ⟨x,rfl⟩ := ((rightWindow L R).hits_iff_image F _).mp h
    exact ab.trans (reach _ gr vr.1 b x)

end

end NabergallChordalDiagrams
