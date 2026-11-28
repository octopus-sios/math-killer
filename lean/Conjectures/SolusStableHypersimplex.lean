import Conjectures.SolusStableHypersimplex.Midpoint
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi

/-!
# Window-subset counts for the stable second hypersimplices

On the labelled cycle with sites `0,...,n-1`, count the sets of `2*k` sites
with at most `k` selected in each cyclic window of width `r+1`. Every window,
including one crossing the cut at 0, is tested. The connection with the
Ehrhart numerator is the separate coefficient identity in the written proof.
-/

namespace SolusStableHypersimplex

open Finset

/-- Actual sites in the half-open cyclic window starting at `a` and
having width `w` (for `a<n`, `w≤n`). -/
def window (n w a : ℕ) : Finset ℕ :=
  if a+w ≤ n then range (a+w) \ range a
  else (range n \ range a) ∪ range (a+w-n)

/-- The family is enumerated by subsets, not by matchings or rotations. -/
def windowSets (n r k : ℕ) : Finset (Finset ℕ) :=
  (range n).powerset.filter fun s =>
    s.card = 2*k ∧ ∀ a : Fin n, (s ∩ window n (r+1) a.val).card ≤ k

def windowCount (n r k : ℕ) : ℕ := (windowSets n r k).card

private def cum (s : Finset ℕ) (j : ℕ) := (s ∩ range j).card

private theorem cum_step (s : Finset ℕ) (j : ℕ) :
    cum s (j+1) = cum s j + if j ∈ s then 1 else 0 := by
  by_cases hj : j∈s
  · have he : s ∩ range (j+1) = insert j (s ∩ range j) := by
      ext t; rw [range_succ]; simp only [mem_inter, mem_insert]
      constructor
      · rintro ⟨h,h'|h'⟩
        · exact Or.inl h'
        · exact Or.inr ⟨h,h'⟩
      · rintro (rfl|⟨h,h'⟩)
        · exact ⟨hj, Or.inl rfl⟩
        · exact ⟨h, Or.inr h'⟩
    simp [cum, he, hj]
  · have he : s ∩ range (j+1) = s ∩ range j := by
      ext t; rw [range_succ]; simp only [mem_inter, mem_insert]
      grind
    simp [cum, he, hj]

private theorem cum_le (s : Finset ℕ) (j : ℕ) : cum s j ≤ j := by
  simpa [cum] using card_le_card (inter_subset_right (s₁ := s) (s₂ := range j))

private theorem cum_end {s : Finset ℕ} {n : ℕ} (hs : s⊆range n) : cum s n = s.card := by
  simp [cum, inter_eq_left.mpr hs]

private theorem cut (s : Finset ℕ) {a b : ℕ} (hab : a≤b) :
    (s ∩ (range b \ range a)).card + cum s a = cum s b := by
  have eq : s ∩ (range b \ range a) = (s ∩ range b) \ (s ∩ range a) := by
    ext t; simp only [mem_inter,mem_sdiff]; tauto
  rw [eq]; apply card_sdiff_add_card_eq_card
  intro t ht
  simp only [mem_inter,mem_range] at *
  exact ⟨ht.1,lt_of_lt_of_le ht.2 hab⟩

private theorem straight {s : Finset ℕ} {n w a : ℕ} (ha : a+w≤n) :
    (s ∩ window n w a).card + cum s a = cum s (a+w) := by
  simpa [window,ha] using cut s (show a≤a+w by omega)

private theorem wrapped {s : Finset ℕ} {n w a : ℕ} (ha : a<n) (hw : w≤n) (hb : n<a+w) :
    (s ∩ window n w a).card + cum s a = cum s n + cum s (a+w-n) := by
  let S := s ∩ (range n \ range a)
  let T := s ∩ range (a+w-n)
  have dis : Disjoint S T := by
    apply disjoint_left.mpr
    intro t hS hT
    simp only [S,T,mem_inter,mem_range,mem_sdiff] at hS hT
    omega
  have eq : s ∩ window n w a = S ∪ T := by
    ext t; simp only [window, if_neg (Nat.not_le.mpr hb), S,T,mem_inter,mem_union]
    tauto
  have hc := cut s (Nat.le_of_lt ha)
  change S.card + cum s a = cum s n at hc
  rw [eq,card_union_of_disjoint dis]
  change S.card + T.card + cum s a = cum s n + T.card
  omega

/-- Each prefix height lies between zero and the number of sites. -/
abbrev Path (n : ℕ) := Fin (n+1) → Fin (n+1)

private def idx (n j : ℕ) : Fin (n+1) := ⟨min j n, by omega⟩

private def height {n : ℕ} (p : Path n) (j : ℕ) := (p (idx n j)).val

private def encode (n : ℕ) (s : Finset ℕ) : Path n := fun j =>
  ⟨cum s j.val, Nat.lt_of_le_of_lt (cum_le s j.val) j.isLt⟩

private theorem height_encode (n : ℕ) (s : Finset ℕ) (j : ℕ) (bj : j≤n) :
    height (encode n s) j = cum s j := by simp [height,encode,idx,min_eq_left bj]

private def marks {n : ℕ} (p : Path n) : Finset ℕ :=
  (range n).filter fun j => height p j < height p (j+1)

private theorem marks_encode {n : ℕ} {s : Finset ℕ} (bs : s ⊆ range n) :
    marks (encode n s) = s := by
  ext j
  simp only [marks,mem_filter,mem_range]
  by_cases bj : j<n
  · rw [height_encode _ _ _ (by omega),height_encode _ _ _ (by omega),cum_step]
    by_cases hj : j∈s <;> simp [hj,bj]
  · have h : j∉s := fun hj => bj (mem_range.mp (bs hj))
    simp [bj,h]

private structure Layer (n w k : ℕ) (p : Path n) : Prop where
  start : height p 0 = 0
  finish : height p n = 2*k
  step : ∀ j < n, height p j ≤ height p (j+1) ∧ height p (j+1) ≤ height p j + 1
  direct : ∀ a < n, a+w ≤ n → height p (a+w) ≤ height p a + k
  wrap : ∀ a < n, n < a+w → height p (a+w-n) + k ≤ height p a

private theorem layer_iff {n r k : ℕ} (hw : r+1≤n) {s : Finset ℕ} (hs : s⊆range n) :
    Layer n (r+1) k (encode n s) ↔ s ∈ windowSets n r k := by
  simp only [windowSets,mem_filter,mem_powerset]
  constructor
  · intro L
    have e := L.finish
    rw [height_encode _ _ _ (by omega), cum_end hs] at e
    refine ⟨hs,e,?_⟩
    intro a
    by_cases b : a.val+(r+1) ≤ n
    · have h := L.direct a.val a.isLt b
      rw [height_encode _ _ _ b,height_encode _ _ _ (by omega)] at h
      have eq := straight (s:=s) b
      omega
    · have h := L.wrap a.val a.isLt (by omega)
      rw [height_encode _ _ _ (by have := a.isLt; omega),height_encode _ _ _ (by omega)] at h
      have eq := wrapped (s:=s) a.isLt hw (by omega : n<a.val+(r+1))
      rw [cum_end hs] at eq
      omega
  · rintro ⟨_,e,h⟩
    constructor
    · simp [height,encode,idx,cum]
    · rw [height_encode _ _ _ (by omega), cum_end hs,e]
    · intro j bj
      rw [height_encode _ _ _ (by omega),height_encode _ _ _ (by omega),cum_step]
      split <;> omega
    · intro a ba b
      have eq := straight (s:=s) b
      have bound := h ⟨a,ba⟩
      change (s ∩ window n (r+1) a).card ≤ k at bound
      rw [height_encode _ _ _ b,height_encode _ _ _ (by omega)]
      omega
    · intro a ba b
      have eq := wrapped (s:=s) ba hw b
      have bound := h ⟨a,ba⟩
      change (s ∩ window n (r+1) a).card ≤ k at bound
      rw [cum_end hs,e] at eq
      rw [height_encode _ _ _ (by omega),height_encode _ _ _ (by omega)]
      omega

private theorem encode_marks {n w k : ℕ} {p : Path n} (L : Layer n w k p) :
    encode n (marks p) = p := by
  have H (j : ℕ) (bj : j≤n) : cum (marks p) j = height p j := by
    induction j with
    | zero => simpa [cum] using L.start.symm
    | succ j ih =>
      have hj : j<n := by omega
      have step := L.step j hj
      rw [cum_step, ih (by omega)]
      simp only [marks,mem_filter,mem_range, hj,true_and]
      split <;> omega
  funext j
  apply Fin.ext
  have eq := H j.val (by have := j.isLt; omega)
  simpa [height,idx,encode,min_eq_left (show j.val≤n by omega)] using eq

private noncomputable def paths (n w k : ℕ) : Finset (Path n) := by
  classical exact univ.filter (Layer n w k)

private theorem mem_paths {n w k : ℕ} {p : Path n} :
    p∈paths n w k ↔ Layer n w k p := by classical simp [paths]

private theorem count_paths {n r k : ℕ} (hw : r+1≤n) :
    windowCount n r k = (paths n (r+1) k).card := by
  classical
  unfold windowCount
  apply card_bij (fun s _ => encode n s)
  · intro s hs
    have b := mem_powerset.mp (mem_filter.mp hs).1
    exact mem_paths.mpr ((layer_iff hw b).mpr hs)
  · intro s hs t ht eq
    have bs := mem_powerset.mp (mem_filter.mp hs).1
    have bt := mem_powerset.mp (mem_filter.mp ht).1
    simpa only [marks_encode bs, marks_encode bt] using congrArg marks eq
  · intro p hp
    have L := mem_paths.mp hp
    have b : marks p ⊆ range n := filter_subset _ _
    exact ⟨marks p, (layer_iff hw b).mp ((encode_marks L).symm ▸ L), encode_marks L⟩

private def mid {n : ℕ} (x y : Path n) (t : ℕ) (ht : t≤1) : Path n := fun i =>
  ⟨((x i).val+(y i).val+t)/2, by have := (x i).isLt; have := (y i).isLt; omega⟩

private theorem mid_layer {n w k : ℕ} {x y : Path n}
    (A : Layer n w k x) (B : Layer n w (k+2) y) (t : ℕ) (ht : t≤1) :
    Layer n w (k+1) (mid x y t ht) := by
  have val (j : ℕ) : height (mid x y t ht) j = (height x j + height y j + t)/2 := rfl
  constructor
  · rw [val,A.start,B.start]; omega
  · rw [val,A.finish,B.finish]; omega
  · intro j hj
    have hx := A.step j hj; have hy := B.step j hj
    rw [val,val]; omega
  · intro a ha b
    have hx := A.direct a ha b; have hy := B.direct a ha b
    rw [val,val]; omega
  · intro a ha b
    have hx := A.wrap a ha b; have hy := B.wrap a ha b
    rw [val,val]; omega

/-- Log-concavity of the counts of labelled window-admissible subsets,
including triples with a vanishing outer count. No bound on `n` or `k`. -/
theorem windowCount_logConcave (n r k : ℕ) (hw : r+1≤n) :
    windowCount n r k * windowCount n r (k+2) ≤ windowCount n r (k+1)^2 := by
  classical
  let f (j : ℕ) (x : Path n) : ℕ := if x∈paths n (r+1) j then 1 else 0
  have mass (j : ℕ) : (∑ x, f j x) = windowCount n r j := by
    rw [count_paths hw]
    simp [f]
  rw [← mass k,← mass (k+2),← mass (k+1),sq]
  apply Midpoint.box_four_functions
  intro x y
  by_cases hx : x∈paths n (r+1) k <;> by_cases hy : y∈paths n (r+1) (k+2)
  · have hl := mem_paths.mpr (mid_layer (mem_paths.mp hx) (mem_paths.mp hy) 0 (by decide))
    have hu := mem_paths.mpr (mid_layer (mem_paths.mp hx) (mem_paths.mp hy) 1 (by decide))
    have leq : (fun i => Midpoint.lo (x i) (y i)) = mid x y 0 (by decide) := by
      funext; apply Fin.ext; simp [Midpoint.lo,mid]
    have ueq : (fun i => Midpoint.hi (x i) (y i)) = mid x y 1 (by decide) := rfl
    simp [f,hx,hy,leq,ueq,hl,hu]
  all_goals simp [f,hx,hy]

/-- Scale and round a prefix vector: if its endpoint is `2*k`, the new
endpoint is exactly `2*j`. Its increments are still zero or one. -/
private theorem thin_layer {n w k : ℕ} {p : Path n} (L : Layer n w k p)
    (j : ℕ) (hj : j≤k) (hk : 0<k) : ∃ q, Layer n w j q := by
  let scale (a : ℕ) := (a*j)/k
  have move (a b : ℕ) : (a+b*k)/k = a/k+b := Nat.add_mul_div_right _ _ hk
  have mono {a b : ℕ} (h : a≤b) : scale a ≤ scale b :=
    Nat.div_le_div_right (Nat.mul_le_mul_right j h)
  have offset (a : ℕ) : scale (a+k) = scale a+j := by
    unfold scale
    rw [Nat.add_mul,Nat.mul_comm k,move]
  have below (a : ℕ) : scale a ≤ a := by
    calc scale a ≤ (a*k)/k := Nat.div_le_div_right (Nat.mul_le_mul_left a hj)
         _ = a := Nat.mul_div_cancel _ hk
  let q : Path n := fun i => ⟨scale (p i).val, (below _).trans_lt (p i).isLt⟩
  have val (a : ℕ) : height q a = scale (height p a) := rfl
  refine ⟨q,?_⟩
  constructor
  · simp [val,L.start,scale]
  · rw [val,L.finish]
    change 2*k*j/k=2*j
    rw [Nat.mul_right_comm,Nat.mul_div_cancel _ hk]
  · intro a ha
    have s := L.step a ha
    have h : scale (height p (a+1)) ≤ scale (height p a)+1 := by
      unfold scale
      calc _ ≤ (height p a*j + 1*k)/k := by
              apply Nat.div_le_div_right
              have b := Nat.mul_le_mul_right j s.2
              rw [Nat.add_mul,one_mul] at b
              omega
           _ = _ := move _ _
    simpa only [val] using And.intro (mono s.1) h
  · intro a ha b
    have h := mono (L.direct a ha b)
    simpa only [val,offset] using h
  · intro a ha b
    have h := mono (L.wrap a ha b)
    simpa only [val,offset] using h

/-- Strong no-internal-zeros statement: the support is downward closed. -/
theorem windowCount_pos_of_le (n r j k : ℕ) (hw : r+1≤n) (hj : j≤k)
    (h : 0 < windowCount n r k) : 0 < windowCount n r j := by
  by_cases hk : k=0
  · simpa [show j=k by omega] using h
  rw [count_paths hw, card_pos] at h ⊢
  obtain ⟨p,hp⟩ := h
  obtain ⟨q,hq⟩ := thin_layer (mem_paths.mp hp) j hj (by omega)
  exact ⟨q,mem_paths.mpr hq⟩

end SolusStableHypersimplex
