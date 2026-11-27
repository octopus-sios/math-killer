import Conjectures.NabergallChordalDiagrams.Diagrams

/-!
# Restriction to an interval with clique boundary

A chord is named by its right endpoint, not by its position in an
enumeration of the chords. Restriction can change which endpoint names a
chord: the map back to the parent is therefore `chordAt`, not just an offset.
-/

namespace NabergallChordalDiagrams

variable {N L : ℕ}

namespace Fragment

/-- The parent chord incident with an arbitrary endpoint. -/
def chordAt (F : Fragment N) (x : Fin N) : F.Chord :=
  ⟨max x (F.mate x), by
    rcases le_total x (F.mate x) with h | h
    · simpa only [max_eq_right h, mate_mate] using h
    · simpa only [max_eq_left h] using h⟩

@[simp] theorem chordAt_val (F : Fragment N) (x : Fin N) :
    (F.chordAt x).val = max x (F.mate x) := rfl

@[simp] theorem mate_chordAt (F : Fragment N) (x : Fin N) :
    F.mate (F.chordAt x).val = min x (F.mate x) := by
  rcases le_total x (F.mate x) with h | h <;>
    simp [h]

@[simp] theorem chordAt_mate (F : Fragment N) (x : Fin N) :
    F.chordAt (F.mate x) = F.chordAt x := by
  apply Subtype.ext
  simp [max_comm]

@[simp] theorem chordAt_right (F : Fragment N) (c : F.Chord) : F.chordAt c.val = c :=
  Subtype.ext (max_eq_left c.property)

theorem chordAt_eq_iff (F : Fragment N) (x y : Fin N) :
    F.chordAt x = F.chordAt y ↔ x = y ∨ x = F.mate y := by
  constructor
  · intro h
    have h₁ := congrArg Subtype.val h
    have h₂ := congrArg (fun c : F.Chord => F.mate c.val) h
    change max x (F.mate x) = max y (F.mate y) at h₁
    simp only [mate_chordAt] at h₂
    rcases le_total x (F.mate x) with hx | hx <;>
      rcases le_total y (F.mate y) with hy | hy <;>
      simp_all
  · rintro (rfl | rfl) <;> simp

theorem start_chordAt (F : Fragment N) (x : Fin N) :
    F.start (F.chordAt x).val =
      if F.mate x = x then x.val else N + min x.val (F.mate x).val := by
  by_cases h : F.mate x = x
  · simp [start, h]
  · have h' : min x (F.mate x) ≠ max x (F.mate x) := by
      rcases lt_or_gt_of_ne h with h | h <;>
        simp [h.le, h.ne]
    unfold start
    rw [mate_chordAt, chordAt_val, ite_eq_right h', ite_eq_right h, Fin.val_min]

/-- For the second chord it is enough to know either one of its endpoints:
a singleton intersects exactly the internal chords that strictly contain it. -/
theorem adj_internal_at (F : Fragment N) (c : F.Chord) (hc : F.mate c.val ≠ c.val)
    (x : Fin N) :
    F.graph.Adj c (F.chordAt x) ↔
      if F.mate x = x then (F.mate c.val < x ∧ x < c.val)
      else Cross (F.mate c.val).val c.val.val (min x.val (F.mate x).val)
        (max x.val (F.mate x).val) := by
  change Cross (F.start c.val) (N + c.val.val) (F.start (F.chordAt x).val)
    (N + (F.chordAt x).val.val) ↔ _
  rw [start_chordAt]
  by_cases h : F.mate x = x <;>
    simp only [start, hc, h, ite_true, ite_false, chordAt_val, Fin.val_max, Cross,
      Fin.lt_def] <;> have := x.isLt <;> omega

theorem adj_fixed (F : Fragment N) (c d : F.Chord) (hc : F.mate c.val = c.val)
    (hd : F.mate d.val = d.val) : F.graph.Adj c d ↔ c ≠ d := by
  change Cross (F.start c.val) (N+c.val.val) (F.start d.val) (N+d.val.val) ↔ _
  have h : c = d ↔ c.val.val = d.val.val := ⟨fun e => e ▸ rfl,
    fun e => Subtype.ext (Fin.ext e)⟩
  simp only [start, hc, hd, ite_true, Cross, ne_eq, h]
  have := c.val.isLt
  have := d.val.isLt
  omega

end Fragment

/-- The half-open interval `[offset, offset+L)` in the parent word. -/
structure Window (N L : ℕ) where
  offset : ℕ
  fits : offset + L ≤ N

namespace Window

variable (W : Window N L)

def pos (x : Fin L) : Fin N := ⟨W.offset + x.val, by have := W.fits; omega⟩
def Contains (x : Fin N) := W.offset ≤ x.val ∧ x.val < W.offset + L
instance (x : Fin N) : Decidable (W.Contains x) := inferInstanceAs (Decidable (_ ∧ _))

@[simp] theorem pos_val (x : Fin L) : (W.pos x).val = W.offset + x.val := rfl
@[simp] theorem contains_pos (x : Fin L) : W.Contains (W.pos x) := by
  have := x.isLt
  simp only [Contains, pos_val]; omega

theorem pos_injective : Function.Injective W.pos := by
  intro a b e; apply Fin.ext; have := congrArg Fin.val e; simpa using this

def localPos (p : Fin N) (h : W.Contains p) : Fin L :=
  ⟨p.val - W.offset, by rcases h with ⟨h₁,h₂⟩; omega⟩

@[simp] theorem pos_localPos (p : Fin N) (h : W.Contains p) : W.pos (W.localPos p h) = p := by
  apply Fin.ext; change W.offset + (p.val - W.offset) = p.val; have := h.1; omega

/-- A pair leaving the window becomes a singleton. -/
def mateIn (F : Fragment N) (x : Fin L) : Fin L :=
  if h : W.Contains (F.mate (W.pos x)) then W.localPos _ h else x

theorem pos_mateIn (F : Fragment N) (x : Fin L) :
    W.pos (W.mateIn F x) =
      if W.Contains (F.mate (W.pos x)) then F.mate (W.pos x) else W.pos x := by
  by_cases h : W.Contains (F.mate (W.pos x)) <;> simp [mateIn, h]

def restrict (F : Fragment N) : Fragment L := ⟨W.mateIn F, by
  intro x
  by_cases h : W.Contains (F.mate (W.pos x))
  · have hx := (W.pos_mateIn F x).trans (ite_eq_left h)
    apply W.pos_injective
    rw [pos_mateIn, hx, Fragment.mate_mate, ite_eq_left (W.contains_pos x)]
  · simp [mateIn, h]⟩

theorem pos_restrict_mate (F : Fragment N) (x : Fin L) :
    W.pos ((W.restrict F).mate x) =
      if W.Contains (F.mate (W.pos x)) then F.mate (W.pos x) else W.pos x :=
  W.pos_mateIn F x

theorem restrict_fixed_iff (F : Fragment N) (x : Fin L) :
    (W.restrict F).mate x = x ↔ F.mate (W.pos x) = W.pos x ∨ ¬ W.Contains (F.mate (W.pos x)) := by
  rw [← W.pos_injective.eq_iff, pos_restrict_mate]
  split <;> simp_all

theorem parent_mate_internal (F : Fragment N) (x : Fin L) (h : (W.restrict F).mate x ≠ x) :
    F.mate (W.pos x) = W.pos ((W.restrict F).mate x) := by
  have hin := (not_or.mp ((W.restrict_fixed_iff F x).not.mp h)).2
  rw [W.pos_restrict_mate, ite_eq_left (not_not.mp hin)]

def chordMap (F : Fragment N) (c : (W.restrict F).Chord) : F.Chord := F.chordAt (W.pos c.val)

theorem chordMap_inj (F : Fragment N) : Function.Injective (W.chordMap F) := by
  intro c d h
  rcases (F.chordAt_eq_iff _ _).mp h with h | h
  · exact Subtype.ext (W.pos_injective h)
  · have din : W.Contains (F.mate (W.pos d.val)) := h ▸ W.contains_pos c.val
    have e : (W.restrict F).mate d.val = c.val := W.pos_injective
      ((W.pos_restrict_mate F d.val).trans ((ite_eq_left din).trans h.symm))
    have e' : (W.restrict F).mate c.val = d.val := e ▸ (W.restrict F).mate_mate d.val
    exact Subtype.ext (le_antisymm (e ▸ d.property) (e' ▸ c.property))

def Hits (F : Fragment N) (c : F.Chord) := W.Contains c.val ∨ W.Contains (F.mate c.val)

def Internal (F : Fragment N) (c : F.Chord) :=
  W.Contains c.val ∧ W.Contains (F.mate c.val) ∧ F.mate c.val ≠ c.val

def Boundary (F : Fragment N) (c : F.Chord) := W.Hits F c ∧ ¬ W.Internal F c

def Good (F : Fragment N) := ∀ c, W.Boundary F c → ∀ d, W.Boundary F d →
  c ≠ d → F.graph.Adj c d

theorem hits_at (F : Fragment N) (p : Fin N) :
    W.Hits F (F.chordAt p) ↔ W.Contains p ∨ W.Contains (F.mate p) := by
  rcases le_total p (F.mate p) with h | h <;>
    simp [Hits, h, or_comm]

theorem internal_at (F : Fragment N) (p : Fin N) :
    W.Internal F (F.chordAt p) ↔ W.Contains p ∧ W.Contains (F.mate p) ∧ F.mate p ≠ p := by
  rcases le_total p (F.mate p) with h | h <;>
    simp [Internal, h, and_comm, and_left_comm, and_assoc, ne_comm]

theorem boundary_chordMap_iff (F : Fragment N) (c : (W.restrict F).Chord) :
    W.Boundary F (W.chordMap F c) ↔ (W.restrict F).mate c.val = c.val := by
  simp only [Boundary, chordMap, hits_at, internal_at, contains_pos, true_and, true_or,
    restrict_fixed_iff]
  tauto

theorem hits_iff_image (F : Fragment N) (c : F.Chord) :
    W.Hits F c ↔ ∃ z, W.chordMap F z = c := by
  constructor
  · rintro (h | h)
    · let x := W.localPos c.val h
      have e : W.pos x = c.val := W.pos_localPos _ _
      have hx : (W.restrict F).mate x ≤ x := by
        have t := W.pos_restrict_mate F x
        rw [e] at t
        have hc := c.property
        split at t <;> have tt := congrArg Fin.val t <;> simp only [pos_val] at tt <;>
          have ee := congrArg Fin.val e <;> simp only [pos_val] at ee <;>
          change (F.mate c.val).val ≤ c.val.val at hc <;> change _ ≤ x.val <;> omega
      exact ⟨⟨x, hx⟩, by change F.chordAt (W.pos x) = c; rw [e, F.chordAt_right]⟩
    · by_cases hc : W.Contains c.val
      · -- Use the right endpoint whenever it lies inside.
        let x := W.localPos c.val hc
        have e : W.pos x = c.val := W.pos_localPos _ _
        have t := W.pos_restrict_mate F x
        rw [e, ite_eq_left h] at t
        have hv := congrArg Fin.val t
        have he := congrArg Fin.val e
        have hr := c.property
        have hx : (W.restrict F).mate x ≤ x := by
          simp only [pos_val] at hv he
          change (F.mate c.val).val ≤ c.val.val at hr
          change _ ≤ x.val; omega
        exact ⟨⟨x, hx⟩, by change F.chordAt (W.pos x) = c; rw [e, F.chordAt_right]⟩
      · let x := W.localPos (F.mate c.val) h
        have e : W.pos x = F.mate c.val := W.pos_localPos _ _
        have hx : (W.restrict F).mate x = x := (W.restrict_fixed_iff F x).mpr
          (Or.inr (by simpa [e] using hc))
        exact ⟨⟨x, hx.le⟩, by change F.chordAt (W.pos x) = c; rw [e, F.chordAt_mate, F.chordAt_right]⟩
  · rintro ⟨z, rfl⟩
    exact (W.hits_at _ _).mpr (Or.inl (W.contains_pos _))

theorem chordMap_internal_val (F : Fragment N) (c : (W.restrict F).Chord)
    (hc : (W.restrict F).mate c.val ≠ c.val) :
    (W.chordMap F c).val = W.pos c.val := by
  rw [chordMap, Fragment.chordAt_val, W.parent_mate_internal _ _ hc]
  exact max_eq_left (by simpa only [Fin.le_def, pos_val, Nat.add_le_add_iff_left] using c.property)

theorem adj_internal_map (F : Fragment N) (c d : (W.restrict F).Chord)
    (hc : (W.restrict F).mate c.val ≠ c.val) :
    F.graph.Adj (W.chordMap F c) (W.chordMap F d) ↔ (W.restrict F).graph.Adj c d := by
  have ec := W.chordMap_internal_val F c hc
  have em := W.parent_mate_internal F c.val hc
  have hn : F.mate (W.chordMap F c).val ≠ (W.chordMap F c).val := by
    rw [ec, em]; exact fun h => hc (W.pos_injective h)
  have child := (W.restrict F).adj_internal_at c hc d.val
  rw [Fragment.chordAt_right] at child
  refine (F.adj_internal_at _ hn (W.pos d.val)).trans (Iff.trans ?_ child.symm)
  rw [ec, em]
  have eh := W.pos_restrict_mate F d.val
  by_cases hin : W.Contains (F.mate (W.pos d.val))
  · rw [ite_eq_left hin] at eh
    rw [← eh]
    simp only [W.pos_injective.eq_iff, Fin.lt_def, pos_val, Cross, Nat.add_lt_add_iff_left,
      Nat.add_min_add_left, Nat.add_max_add_left]
  · have ed : (W.restrict F).mate d.val = d.val := (W.restrict_fixed_iff _ _).mpr (Or.inr hin)
    have hd : F.mate (W.pos d.val) ≠ W.pos d.val := fun e => hin (e.symm ▸ W.contains_pos d.val)
    rw [ite_eq_right hd, ite_eq_left ed]
    have hp := (F.mate (W.pos d.val)).isLt
    have ha := ((W.restrict F).mate c.val).isLt
    have hb := c.val.isLt
    have hx := d.val.isLt
    simp only [Contains, not_and_or, not_le, not_lt] at hin
    simp only [Cross, Fin.lt_def, pos_val]
    omega

theorem adj_map_iff (F : Fragment N) (hg : W.Good F) (c d : (W.restrict F).Chord) :
    F.graph.Adj (W.chordMap F c) (W.chordMap F d) ↔ (W.restrict F).graph.Adj c d := by
  by_cases hc : (W.restrict F).mate c.val = c.val
  · by_cases hd : (W.restrict F).mate d.val = d.val
    · rw [(W.restrict F).adj_fixed _ _ hc hd]
      exact ⟨fun h e => (F.graph.loopless.irrefl _) (e ▸ h),
        fun e => hg _ ((W.boundary_chordMap_iff _ _).mpr hc) _
          ((W.boundary_chordMap_iff _ _).mpr hd) ((W.chordMap_inj F).ne e)⟩
    · exact (F.graph.adj_comm _ _).trans ((W.adj_internal_map F d c hd).trans ((W.restrict F).graph.adj_comm _ _))
  · exact W.adj_internal_map F c d hc

/-- An internal chord cannot intersect a chord missing the interval. -/
theorem hits_of_adj_internal (F : Fragment N) {c d : F.Chord}
    (hi : W.Internal F c) (h : F.graph.Adj c d) : W.Hits F d := by
  classical
  by_contra! hnot
  rcases hi with ⟨⟨h₁,h₂⟩, ⟨h₃,h₄⟩, hne⟩
  have hh := (F.adj_internal_at c hne d.val).mp (by simpa using h)
  have hd := d.property
  have hlo := c.property
  change _ ≤ d.val.val at hd
  change _ ≤ c.val.val at hlo
  simp only [Hits, Contains, not_or, not_and_or, not_le, not_lt] at hnot
  split at hh
  · change _ < d.val.val ∧ _ < c.val.val at hh; omega
  · rw [min_eq_right hd, max_eq_left hd] at hh
    unfold Cross at hh; omega

end Window

/-- A predicate closed under adjacency propagates along any walk. -/
theorem along_reachable {V : Type*} {G : SimpleGraph V} {P : V → Prop}
    (step : ∀ x y, P x → G.Adj x y → P y) {x y : V} (p : G.Reachable x y) : P x → P y := by
  obtain ⟨w⟩ := p
  induction w with
  | nil => exact id
  | cons e _ ih => exact fun hx => ih (step _ _ hx e)

namespace Window

variable (W : Window N L)

/-- A nonempty interval in a connected positive-weight fragment meets a
boundary strand (even without a clique assumption). -/
theorem boundary_exists (F : Fragment N) (hL : 0 < L) (hconn : F.graph.Connected)
    (hk : 0 < F.weight) : ∃ c, W.Boundary F c := by
  classical
  by_contra! h
  have step (x y) (hx : W.Hits F x) (e : F.graph.Adj x y) : W.Hits F y := by
    have hi : W.Internal F x := by by_contra hn; exact h x ⟨hx, hn⟩
    exact W.hits_of_adj_internal F hi e
  let c := F.chordAt (W.pos ⟨0,hL⟩)
  have hc : W.Hits F c := (W.hits_at _ _).mpr (Or.inl (W.contains_pos _))
  obtain ⟨s, hs⟩ := Finset.card_pos.mp hk
  have hs' := (F.mem_singletons _).mp hs
  have ht : W.Hits F (F.chordAt s) := along_reachable step (hconn c _) hc
  exact h _ ⟨ht, by simp [W.internal_at, hs']⟩

theorem restrict_weight_pos (F : Fragment N) (hL : 0 < L) (hconn : F.graph.Connected)
    (hk : 0 < F.weight) : 0 < (W.restrict F).weight := by
  obtain ⟨c,hc⟩ := W.boundary_exists F hL hconn hk
  obtain ⟨d, rfl⟩ := (W.hits_iff_image _ _).mp hc.1
  exact Finset.card_pos.mpr ⟨d.val, ((W.restrict F).mem_singletons _).mpr
    ((W.boundary_chordMap_iff _ _).mp hc)⟩

/-- On a good interval, restriction preserves both graph conditions. -/
theorem restrict_valid (F : Fragment N) (hL : 0 < L) (hk : 0 < F.weight)
    (hv : F.Valid) (hg : W.Good F) : (W.restrict F).Valid := by
  classical
  refine ⟨?_, hv.2.of_induced _ (W.chordMap_inj F) (W.adj_map_iff F hg)⟩
  obtain ⟨c,hc⟩ := W.boundary_exists F hL hv.1 hk
  obtain ⟨a,rfl⟩ := (W.hits_iff_image _ _).mp hc.1
  apply ((W.restrict F).graph.connected_iff_exists_forall_reachable).mpr
  refine ⟨a, fun b => ?_⟩
  let P (x : F.Chord) := ∀ z, W.chordMap F z = x → (W.restrict F).graph.Reachable a z
  have step (x y) (hx : P x) (e : F.graph.Adj x y) : P y := by
    rintro z rfl
    by_cases ht : W.Hits F x
    · obtain ⟨w, rfl⟩ := (W.hits_iff_image _ _).mp ht
      exact (hx w rfl).trans (((W.adj_map_iff F hg w z).mp e).reachable)
    · have hz : W.Boundary F (W.chordMap F z) :=
        ⟨(W.hits_iff_image F _).mpr ⟨z, rfl⟩, fun hi => ht (W.hits_of_adj_internal F hi e.symm)⟩
      by_cases he : a = z
      · exact he ▸ SimpleGraph.Reachable.rfl
      · exact ((W.adj_map_iff F hg a z).mp (hg _ hc _ hz ((W.chordMap_inj F).ne he))).reachable
  have hstart : P (W.chordMap F a) := by
    intro w e; rw [W.chordMap_inj F e]
  exact along_reachable step (hv.1 (W.chordMap F a) (W.chordMap F b)) hstart b rfl

end Window
end NabergallChordalDiagrams
