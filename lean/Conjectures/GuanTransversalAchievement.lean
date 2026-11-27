import Mathlib.Data.Fintype.Prod

/-! # The lower bound in the transversal achievement game

`Defends k X O` describes a defense against an X win during the next
`k` X moves, starting at X's turn. O can end the game by winning.
-/

namespace GuanTransversalAchievement

abbrev Cell (n : ℕ) := Fin n × Fin n
abbrev Stones (n : ℕ) := Finset (Cell n)

inductive Axis | row | col
  deriving DecidableEq

private def other : Axis → Axis | .row => .col | .col => .row

def coord {n : ℕ} : Axis → Cell n → Fin n
  | .row => Prod.fst
  | .col => Prod.snd

private def cell {n : ℕ} : Axis → Fin n → Fin n → Cell n
  | .row, i, j => (i,j)
  | .col, i, j => (j,i)

@[simp] private theorem coord_cell {n} (a : Axis) (i j : Fin n) :
    coord a (cell a i j) = i := by cases a <;> rfl

@[simp] private theorem other_cell {n} (a : Axis) (i j : Fin n) :
    coord (other a) (cell a i j) = j := by cases a <;> rfl

private theorem axes (a b : Axis) : b = a ∨ b = other a := by
  cases a <;> cases b <;> simp [other]

private theorem eq_of_coords {n} (a : Axis) {p q : Cell n}
    (h : coord a p = coord a q) (h' : coord (other a) p = coord (other a) q) :
    p = q := by
  cases a
  · exact Prod.ext h h'
  · exact Prod.ext h' h

/-- A matching has neither a repeated row nor a repeated column. -/
def Matching {n} (M : Stones n) := ∀ a, Set.InjOn (coord a) (M : Set (Cell n))

/-- The player owns a transversal: a subset of n cells in distinct rows and columns. -/
def Wins {n} (S : Stones n) := ∃ T ⊆ S, Matching T ∧ T.card = n

def Legal {n} (X O : Stones n) (p : Cell n) := p ∉ X ∧ p ∉ O

/-- Finite alternating-play predicate. At each X turn quantify over every legal
move; X must not win there. Unless this was the last turn under consideration,
O must have a legal reply that wins or continues the defense. -/
def Defends {n} : ℕ → Stones n → Stones n → Prop
  | 0, _, _ => True
  | k+1, X, O => ∀ x, Legal X O x → ¬ Wins (insert x X) ∧
      (k = 0 ∨ ∃ o, Legal (insert x X) O o ∧
        (Wins (insert o O) ∨ Defends k (insert x X) (insert o O)))

variable {n : ℕ}

private def lines (a : Axis) (S : Stones n) := S.image (coord a)
private def OpenCell (S : Stones n) (p : Cell n) := ∀ a, coord a p ∉ lines a S
private def Clean (X O : Stones n) := ∀ p ∈ X, ¬ OpenCell O p

@[simp] private theorem lines_insert (a : Axis) (p : Cell n) (S : Stones n) :
    lines a (insert p S) = insert (coord a p) (lines a S) := Finset.image_insert ..

private theorem line_mem (a : Axis) {M : Stones n} {p} (hp : p ∈ M) :
    coord a p ∈ lines a M := Finset.mem_image_of_mem _ hp

private theorem open_not_mem {S : Stones n} {p} (hp : OpenCell S p) : p ∉ S :=
  fun h => hp .row (line_mem _ h)

private theorem open_cell {S : Stones n} {a : Axis} {u v}
    (hu : u ∉ lines a S) (hv : v ∉ lines (other a) S) : OpenCell S (cell a u v) := by
  intro b
  obtain rfl | rfl := axes a b
  · simpa using hu
  · simpa using hv

private theorem matching_insert {S : Stones n} {p} (hm : Matching S) (hp : OpenCell S p) :
    Matching (insert p S) := by
  intro a
  apply Finset.card_image_iff.mp
  change (lines a (insert p S)).card = _
  rw [lines_insert, Finset.card_insert_of_notMem (hp a), Finset.card_insert_of_notMem (open_not_mem hp)]
  exact congrArg (· + 1) (Finset.card_image_of_injOn (hm a))

private theorem small_not_win {S : Stones n} (h : S.card < n) : ¬ Wins S := by
  rintro ⟨T, hs, _, ht⟩
  have := Finset.card_le_card hs
  omega

private theorem covers {T : Stones n} (hm : Matching T) (ht : T.card = n)
    (a : Axis) (v : Fin n) : ∃ p ∈ T, coord a p = v := by
  apply Finset.mem_image.mp
  have h := Finset.eq_univ_of_card (s := lines a T)
      (by simp [lines, Finset.card_image_of_injOn (hm a), ht])
  change v ∈ lines a T
  rw [h]
  exact Finset.mem_univ v

private theorem win_uses {S : Stones n} (h : Wins S) (a : Axis) (v : Fin n) :
    v ∈ lines a S := by
  obtain ⟨T, hT, hm, ht⟩ := h
  obtain ⟨p, hp, rfl⟩ := covers hm ht a v
  exact line_mem a (hT hp)

private theorem two_missing {S : Stones n} {a : Axis} (h : (lines a S).card + 2 ≤ n)
    (v : Fin n) : ∃ w, w ∉ lines a S ∧ w ≠ v := by
  have ht : 1 < (lines a S)ᶜ.card := by rw [Finset.card_compl, Fintype.card_fin]; omega
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp ht
  by_cases e : p = v
  · exact ⟨q, Finset.mem_compl.mp hq, e ▸ hpq.symm⟩
  · exact ⟨p, Finset.mem_compl.mp hp, e⟩

private theorem missing {S : Stones n} (a : Axis) (h : (lines a S).card < n) :
    ∃ w, w ∉ lines a S := by
  obtain ⟨w, _, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := lines a S) (t := Finset.univ) (by simpa using h)
  exact ⟨w, hw⟩

private theorem can_move {X O : Stones n} (h : X.card + O.card < n * n) :
    ∃ p, Legal X O p := by
  have hlt : (X ∪ O).card < (Finset.univ : Stones n).card := by
    simpa using lt_of_le_of_lt (Finset.card_union_le X O) h
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨p, by simpa [Legal] using hp⟩

/-- Claim the specified cell if free; otherwise any legal move keeps it unavailable. -/
private theorem block_cell {X O : Stones n} (h : ∃ p, Legal X O p) (q : Cell n) :
    ∃ o, Legal X O o ∧ ¬ Legal X (insert o O) q := by
  by_cases hq : Legal X O q
  · exact ⟨q, hq, fun hf => hf.2 (Finset.mem_insert_self ..)⟩
  · obtain ⟨o,ho⟩ := h
    exact ⟨o, ho, fun hf => hq ⟨hf.1, fun hm => hf.2 (Finset.mem_insert_of_mem hm)⟩⟩

private theorem block_last {X O : Stones n} (h : ∃ p, Legal X O p) (q : Cell n)
    (only : ∀ z, Legal X O z → Wins (insert z X) → z = q) :
    ∃ o, Legal X O o ∧ Defends 1 X (insert o O) := by
  obtain ⟨o, hf, hb⟩ := block_cell h q
  refine ⟨o, hf, fun z hz => ⟨fun hw => ?_, Or.inl rfl⟩⟩
  exact hb ((only z ⟨hz.1, fun hm => hz.2 (Finset.mem_insert_of_mem hm)⟩ hw) ▸ hz)

private theorem room {X O : Stones n} (hn : 4 ≤ n) (hx : X.card ≤ n) (ho : O.card ≤ n) :
    ∃ p, Legal X O p := by
  apply can_move
  have := Nat.mul_le_mul_left n hn
  omega

private theorem before_x {X O : Stones n} {x z} (hz : Legal (insert x X) O z) :
    Legal X O z := ⟨fun h => hz.1 (Finset.mem_insert_of_mem h), hz.2⟩

private theorem axis_ne {p q : Cell n} (h : p ≠ q) : ∃ a, coord a p ≠ coord a q := by
  by_cases hr : p.1 = q.1
  · exact ⟨.col, fun hc => h (Prod.ext hr hc)⟩
  · exact ⟨.row, hr⟩

private theorem other_lines {M : Stones n} (hm : Matching M) (hc : M.card+1=n)
    (a : Axis) {v w : Fin n} (hv : v ∉ lines a M) (hw : w ≠ v) : w ∈ lines a M := by
  have hall : insert v (lines a M) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_insert_of_notMem hv, Fintype.card_fin]
    simpa only [lines, Finset.card_image_of_injOn (hm a)] using hc
  have h : w ∈ insert v (lines a M) := hall ▸ Finset.mem_univ w
  simpa [hw] using h

/-- If one stone supplies a missing line to a transversal, it must be used there. -/
private theorem forced_stone {A T : Stones n} {p : Cell n} (sub : T ⊆ insert p A)
    (hm : Matching T) (ht : T.card=n) {a : Axis} {v} (hv : v ∉ lines a A) :
    p ∈ T ∧ coord a p = v := by
  obtain ⟨q, hq, he⟩ := covers hm ht a v
  obtain hp | hA := Finset.mem_insert.mp (sub hq)
  · exact hp ▸ ⟨hq, he⟩
  · exact False.elim (hv (he ▸ line_mem a hA))

/-- After blocking the missing corner p of an (n-1)-matching, a different
X move x creates at most one completion away from p. -/
private theorem matching_threat {M : Stones n} (hm : Matching M) (hc : M.card+1=n)
    {p x : Cell n} (hp : OpenCell M p) (hx : x ∉ M) (hne : x ≠ p) :
    ¬ Wins (insert x M) ∧
    ∃ q, ∀ z, z ≠ p → Wins (insert z (insert x M)) → z=q := by
  obtain ⟨a, ha⟩ := axis_ne hne
  have hmiss : coord a p ∉ lines a (insert x M) := by simp [Ne.symm ha, hp a]
  refine ⟨fun hw => hmiss (win_uses hw a _), ?_⟩
  obtain ⟨t, ht, he⟩ := Finset.mem_image.mp (other_lines hm hc a (hp a) ha)
  let b := other a
  refine ⟨cell a (coord a p) (coord b t), ?_⟩
  rintro z hzp ⟨T, sub, hT, hnT⟩
  obtain ⟨_, hz⟩ := forced_stone sub hT hnT hmiss
  have hzb : coord b z ≠ coord b p := fun h => hzp (eq_of_coords a hz h)
  have hmiss' : coord b p ∉ lines b (insert z M) := by simp [Ne.symm hzb, hp b]
  have sub' : T ⊆ insert x (insert z M) := by simpa [Finset.insert_comm] using sub
  obtain ⟨hxT, hxb⟩ := forced_stone sub' hT hnT hmiss'
  have hnt : t ∉ T := fun htT => hx ((hT a htT hxT he) ▸ ht)
  obtain ⟨s, hs, hsline⟩ := covers hT hnT b (coord b t)
  have hsz : s = z := by
    obtain h | h := Finset.mem_insert.mp (sub hs)
    · exact h
    obtain h | h := Finset.mem_insert.mp h
    · have eq : coord b t = coord b p := hsline.symm.trans (h ▸ hxb)
      exact False.elim (hp b (eq ▸ line_mem b ht))
    · exact False.elim (hnt ((hm b h ht hsline) ▸ hs))
  apply eq_of_coords a
  · simpa using hz
  · simpa [b] using (hsz ▸ hsline : coord b z = coord b t)

private theorem matching_defense {M O : Stones n} (hn : 4 ≤ n) (hm : Matching M)
    (hc : M.card+1=n) (ho : O.card+2=n) :
    ∃ o, Legal M O o ∧ Defends 2 M (insert o O) := by
  have hless (a : Axis) : (lines a M).card < n := by
    have h := Finset.card_image_le (s := M) (f := coord a)
    change (lines a M).card ≤ _ at h
    omega
  obtain ⟨r, hr⟩ := missing .row (hless _)
  obtain ⟨c, hc'⟩ := missing .col (hless _)
  let p : Cell n := (r,c)
  have hp : OpenCell M p := open_cell (a := .row) hr hc'
  obtain ⟨o, hfo, hb⟩ := block_cell (room (X := M) (O := O) hn (by omega) (by omega)) p
  refine ⟨o, hfo, ?_⟩
  intro x hx
  have hne : x ≠ p := fun e => hb (e ▸ hx)
  obtain ⟨hnw,q,hq⟩ := matching_threat hm hc hp hx.1 hne
  refine ⟨hnw, Or.inr ?_⟩
  have hxf := Finset.card_insert_le x M
  have hof := Finset.card_insert_le o O
  obtain ⟨o',hf',hs⟩ := block_last (X := insert x M) (O := insert o O)
    (room hn (by omega) (by omega)) q
    (fun z hz => hq z (fun e => hb (e ▸ before_x hz)))
  exact ⟨o', hf', Or.inr hs⟩

/-- In O's unused 2-by-2 block, one diagonal avoids the last X stone.
Order it so the *reserved* corner t is outside the specified line d. -/
private theorem free_diagonal {O : Stones n} (holes : ∀ a, (lines a O).card + 2 ≤ n)
    (e : Cell n) (a : Axis) (d : Fin n) :
    ∃ o t, o ≠ e ∧ t ≠ e ∧ OpenCell O o ∧ OpenCell O t ∧
      OpenCell (insert o O) t ∧ coord a t ≠ d := by
  let b := other a
  obtain ⟨j,hj,hjd⟩ := two_missing (holes a) d
  obtain ⟨i,hi,hij⟩ := two_missing (holes a) j
  obtain ⟨v,hv,hve⟩ := two_missing (holes b) (coord b e)
  obtain ⟨w,hw,hwv⟩ := two_missing (holes b) v
  have make (l k : Fin n) (hl : l ∉ lines b O) (hk : k ∉ lines b O) (hkl : k ≠ l)
      (h₁ : cell a i l ≠ e) (h₂ : cell a j k ≠ e) :
      ∃ o t, o ≠ e ∧ t ≠ e ∧ OpenCell O o ∧ OpenCell O t ∧
        OpenCell (insert o O) t ∧ coord a t ≠ d := by
    refine ⟨cell a i l, cell a j k, h₁, h₂, open_cell hi hl, open_cell hj hk, ?_,
      by simpa using hjd⟩
    intro s
    obtain rfl | rfl := axes a s
    · simp [Ne.symm hij, hj]
    · simp [hkl, show k ∉ lines (other a) O from hk]
  by_cases he : coord a e = i
  · apply make v w hv hw hwv
    · intro heq
      exact hve (by simpa [b] using congrArg (coord b) heq)
    · intro heq
      have h : j = coord a e := by simpa using congrArg (coord a) heq
      exact hij (h.trans he).symm
  · apply make w v hw hv hwv.symm
    · intro heq
      exact he (by simpa using congrArg (coord a) heq.symm)
    · intro heq
      exact hve (by simpa [b] using congrArg (coord b) heq)

private theorem must_cover {S : Stones n} {z : Cell n} {a : Axis} {v : Fin n}
    (hv : v ∉ lines a S) (hw : Wins (insert z S)) : coord a z = v := by
  have h := win_uses hw a v
  rw [lines_insert, Finset.mem_insert] at h
  exact (h.resolve_right hv).symm

/-- X with two missing lines on one axis cannot ignore O's counterthreat.
Answering it preserves a missing line on each axis. -/
private theorem collision_defense {X O : Stones n} {e : Cell n} (hn : 4 ≤ n)
    (hc : (insert e X).card+1=n) (ho : O.card+2=n) (hm : Matching O) (cl : Clean X O)
    (a : Axis) (rep : (lines a (insert e X)).card+2 ≤ n) :
    ∃ o, Legal (insert e X) O o ∧ Defends 2 (insert e X) (insert o O) := by
  let M := insert e X
  let b := other a
  change M.card+1=n at hc
  change (lines a M).card+2 ≤ n at rep
  have hless : (lines b M).card < n := by
    have h : (lines b M).card ≤ M.card := Finset.card_image_le
    omega
  obtain ⟨d, hd⟩ := missing b hless
  have holes (s : Axis) : (lines s O).card + 2 ≤ n := by
    change (O.image _).card + 2 ≤ n
    rw [Finset.card_image_of_injOn (hm s), ho]
  obtain ⟨o,t,hoe,hte,hop,htp,htp',htd⟩ := free_diagonal holes e b d
  have freeM (p : Cell n) (hpe : p ≠ e) (hp : OpenCell O p) : p ∉ M := by
    have h : p ∉ X := fun h => cl p h hp
    simpa [M,hpe] using h
  have hfo : Legal M O o := ⟨freeM o hoe hop, open_not_mem hop⟩
  have hft : Legal M (insert o O) t := ⟨freeM t hte htp, open_not_mem htp'⟩
  have hwin : Wins (insert t (insert o O)) := by
    refine ⟨_, Finset.Subset.rfl, matching_insert (matching_insert hm hop) htp', ?_⟩
    rw [Finset.card_insert_of_notMem hft.2, Finset.card_insert_of_notMem hfo.2]
    omega
  refine ⟨o, hfo, ?_⟩
  intro x hx
  obtain ⟨r, hr, hrx⟩ := two_missing rep (coord a x)
  have hr' : r ∉ lines a (insert x M) := by simp [hr, hrx]
  refine ⟨fun h => hr' (win_uses h a r), Or.inr ?_⟩
  by_cases he : x = t
  · subst x
    have hd' : d ∉ lines b (insert t M) := by simp [hd, Ne.symm htd]
    have hxf := Finset.card_insert_le t M
    have hof := Finset.card_insert_le o O
    obtain ⟨o',hf',hs⟩ := block_last (X := insert t M) (O := insert o O)
      (room hn (by omega) (by omega)) (cell a r d) (by
        intro z _ hw
        apply eq_of_coords a
        · simpa using must_cover hr' hw
        · simpa [b] using must_cover hd' hw)
    exact ⟨o', hf', Or.inr hs⟩
  · exact ⟨t, ⟨fun h => (Finset.mem_insert.mp h).elim (Ne.symm he) hft.1, hft.2⟩, Or.inl hwin⟩

/-- O extends its matching in unused lines. Cover the latest X row if it was
unused, and always take an unused column different from the latest X column. -/
private theorem extend_clean {X O : Stones n} (hm : Matching O) (cl : Clean X O)
    (hc : O.card+2 ≤ n) (x : Cell n) :
    ∃ o, Legal (insert x X) O o ∧ Matching (insert o O) ∧ Clean (insert x X) (insert o O) := by
  have hsz (a : Axis) : (lines a O).card + 2 ≤ n := by
    simpa [lines, Finset.card_image_of_injOn (hm a)] using hc
  obtain ⟨c,hc',hne⟩ := two_missing (hsz .col) x.2
  obtain ⟨r,hr,hrx⟩ : ∃ r, r ∉ lines .row O ∧ x.1 ∈ insert r (lines .row O) := by
    by_cases hx : x.1 ∈ lines .row O
    · have h := hsz .row
      obtain ⟨r,hr⟩ := missing .row (by omega : (lines .row O).card < n)
      exact ⟨r, hr, Finset.mem_insert_of_mem hx⟩
    · exact ⟨x.1, hx, Finset.mem_insert_self ..⟩
  let o : Cell n := (r,c)
  have op : OpenCell O o := open_cell (a := .row) hr hc'
  have hxo : o ∉ X := fun h => cl o h op
  have hneq : o ≠ x := fun e => hne (congrArg Prod.snd e)
  refine ⟨o, ⟨by simp [hneq, hxo], open_not_mem op⟩, matching_insert hm op, ?_⟩
  intro p hp hu
  obtain he | hp := Finset.mem_insert.mp hp
  · subst p
    exact hu .row (by rw [lines_insert]; exact hrx)
  · exact cl p hp (fun a h => hu a (by rw [lines_insert]; exact Finset.mem_insert_of_mem h))

private theorem last_three {X O : Stones n} (hn : 4 ≤ n) (hc : X.card+2=n)
    (ho : O.card+2=n) (hm : Matching O) (cl : Clean X O) : Defends 3 X O := by
  intro e he
  have hs : (insert e X).card+1=n := by rw [Finset.card_insert_of_notMem he.1]; omega
  refine ⟨small_not_win (by omega), Or.inr ?_⟩
  by_cases mat : Matching (insert e X)
  · obtain ⟨o,hf,hd⟩ := matching_defense hn mat hs ho
    exact ⟨o,hf,Or.inr hd⟩
  · obtain ⟨a,ha⟩ := Classical.not_forall.mp mat
    have lt : (lines a (insert e X)).card < (insert e X).card :=
      lt_of_le_of_ne Finset.card_image_le (mt Finset.card_image_iff.mp ha)
    obtain ⟨o,hf,hd⟩ := collision_defense hn hs ho hm cl a (by omega)
    exact ⟨o,hf,Or.inr hd⟩

private theorem from_clean (k : ℕ) {X O : Stones n} (hn : 4 ≤ n)
    (hc : X.card+k+2=n) (ho : O.card+k+2=n) (hm : Matching O) (cl : Clean X O) :
    Defends (k+3) X O := by
  induction k generalizing X O with
  | zero => exact last_three hn (by omega) (by omega) hm cl
  | succ k ih =>
    intro x hx
    have hs := Finset.card_insert_of_notMem hx.1
    obtain ⟨o,hf,hm',cl'⟩ := extend_clean hm cl (by omega) x
    have hs' := Finset.card_insert_of_notMem hf.2
    refine ⟨small_not_win (by omega), Or.inr ⟨o, hf, Or.inr ?_⟩⟩
    exact ih (by omega) (by omega) hm' cl'

/-- From the empty board, O has a strategy against *all* legal X moves
preventing X from winning through X's (n+1)-st move (ply 2n+1).
Together with Guan's upper bound this gives optimal winning ply 2n+3. -/
theorem optimalDurationLowerBound (n : ℕ) (hn : 4 ≤ n) : Defends (n+1) (∅ : Stones n) ∅ := by
  rw [show n+1 = (n-2)+3 by omega]
  apply from_clean (n-2) hn
  · simp; omega
  · simp; omega
  · intro a; simp [Set.InjOn]
  · simp [Clean]

end GuanTransversalAchievement
