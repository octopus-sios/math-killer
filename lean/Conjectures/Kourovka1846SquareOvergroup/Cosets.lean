import Conjectures.Kourovka1846SquareOvergroup.Chart

/-!
# Seven distinct cosets from three square roots

Transport conjugation along the marked chart. If two short words represented
the same coset, a kernel element would satisfy the compatibility test.
-/

namespace Kourovka1846.D8.Marked

private theorem rotWord_map {A B : Type*} (f : A → B) (m n) (o p : A)
    (hm : ∀ x y, f (m x y) = n (f x) (f y)) (i : ZMod 4) :
    f (rotWord m o p i) = rotWord n (f o) (f p) i := by
  unfold rotWord
  split <;> simp [hm]

private theorem word_map {A B : Type*} (f : A → B) (m n) (o p q x : A)
    (hm : ∀ u v, f (m u v) = n (f u) (f v)) (u : E) :
    f (word m o p q x u) = word n (f o) (f p) (f q) (f x) u := by
  obtain ⟨d,b⟩ := u
  cases d <;> cases b <;> simp [word, hm, rotWord_map f m n o p hm]

private theorem word_self (L : Law) (u : E) : word L.mul e R S T u = u := by
  obtain ⟨k,a⟩ := L
  exact (by decide : ∀ (k : Bool) (a : D) (u : E),
    word (Law.mk k a).mul e R S T u = u) k a u

namespace Chart

variable {H : Type*} [Group H] {K : Subgroup H} {j : D →* K} (C : Chart j)

def val (u : E) : H := C.rep u

theorem vinj : Function.Injective C.val := Subtype.val_injective.comp C.rep.injective

theorem vmul (u v : E) : C.val (C.law.mul u v) = C.val u * C.val v :=
  congrArg Subtype.val (C.mul u v)

theorem vone : C.val e = 1 := by change (C.rep (1, false) : H) = 1; rw [C.base, map_one]; rfl

variable [K.Normal]

noncomputable def images (h : H) : Images :=
  let f (u : E) := C.rep.symm (MulAut.conjNormal h (C.rep u))
  (f R, f S, f T)

theorem images_apply (h : H) (u : E) :
    C.val (transform C.law (C.images h) u) = MulAut.conj h (C.val u) := by
  let f := MulAut.conj h
  have m (z z') : (f ∘ C.val) (C.law.mul z z') =
      (f ∘ C.val) z * (f ∘ C.val) z' := by simp [C.vmul]
  have hg (t : E) : C.val (C.rep.symm (MulAut.conjNormal h (C.rep t))) = (f ∘ C.val) t := by
    change (C.rep (C.rep.symm _) : H) = _
    rw [C.rep.apply_symm_apply]
    rfl
  rw [transform, word_map C.val _ (· * ·) _ _ _ _ C.vmul]
  change word _ _ (C.val (C.rep.symm _)) (C.val (C.rep.symm _)) (C.val (C.rep.symm _)) u = _
  rw [hg, hg, hg]
  have he : (f ∘ C.val) e = C.val e := by simp [C.vone]
  rw [← he, ← word_map (f ∘ C.val) _ _ _ _ _ _ m, word_self]
  rfl

theorem candidates_mem (g : Mark) {h : H} (hh : h ^ 2 = C.val g.pt) :
    C.images h ∈ candidates C.law g := by
  let v := C.images h
  let F := transform C.law v
  have ha (u : E) : C.val (F u) = MulAut.conj h (C.val u) := C.images_apply h u
  have hg : F g.pt = g.pt := C.vinj (by rw [ha, ← hh, MulAut.conj_apply]; group)
  have hq : quick C.law g v.1 v.2.1 = true := by
    have idr (u : E) : C.law.mul u e = u := C.vinj (by rw [C.vmul, C.vone, mul_one])
    cases g with
    | rot => exact beq_iff_eq.mpr hg
    | flip =>
      apply beq_iff_eq.mpr
      change C.law.mul v.2.1 e = S at hg
      rwa [idr] at hg
    | third => exact beq_iff_eq.mpr hg
  have ht : feasible C.law g v = true := by
    simp only [feasible, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    constructor
    · intro u _
      apply C.vinj
      change C.val (C.law.mul (F (F u)) g.pt) = _
      rw [C.vmul, C.vmul, ha, ha, ← hh, MulAut.conj_apply, MulAut.conj_apply]
      simp [pow_two, mul_assoc]
    · intro u _ w _
      apply C.vinj
      change C.val (F (C.law.mul u w)) = C.val (C.law.mul (F u) (F w))
      rw [ha, C.vmul, map_mul, C.vmul, ha, ha]
  unfold candidates
  apply List.mem_flatMap.mpr
  refine ⟨v.1, exhaustive _, List.mem_flatMap.mpr ⟨v.2.1, exhaustive _, ?_⟩⟩
  rw [hq]
  simp only [ite_true]
  exact List.mem_map.mpr ⟨v.2.2, List.mem_filter.mpr ⟨exhaustive _, ht⟩, rfl⟩

end Chart
end Kourovka1846.D8.Marked

namespace Kourovka1846.D8.Marked

def W.value {H : Type*} [Group H] (a b c : H) : W → H
  | .id => 1
  | .a => a
  | .b => b
  | .c => c
  | .ab => a*b
  | .ba => b*a
  | .ac => a*c
  | .bc => b*c
  | .bab => b*a*b⁻¹

private theorem action_word {H : Type*} [Group H] (v : E → H) (a b c : H)
    (f g h : E → E) (fa : ∀ u, v (f u) = MulAut.conj a (v u))
    (fb : ∀ u, v (g u) = MulAut.conj b (v u))
    (fc : ∀ u, v (h u) = MulAut.conj c (v u)) (hb : b ^ 4 = 1) (w : W) (u : E) :
    v ((sample f g h w).act u) = MulAut.conj (W.value a b c w) (v u) := by
  have bi : b⁻¹ = b*(b*b) := calc
    _ = b ^ 4 * b⁻¹ := by rw [hb, one_mul]
    _ = _ := by simp [pow_succ, mul_assoc]
  cases w <;> simp [sample, W.value, fa, fb, fc, MulAut.mul_apply, bi]

private theorem square_word {H : Type*} [Group H] (v : E → H) (a b c : H) (f g h : E → E)
    (ve : v e = 1) (ha : a ^ 2 = v R) (hb : b ^ 2 = v S) (hc : c ^ 2 = v V)
    (fb : ∀ u, v (g u) = MulAut.conj b (v u)) (w : W) (l : E)
    (hl : (sample f g h w).square = some l) : v l = W.value a b c w ^ 2 := by
  cases w <;> simp [sample] at hl <;> subst l
  · simpa [W.value] using ve
  · exact ha.symm
  · exact hb.symm
  · exact hc.symm
  · rw [fb, MulAut.conj_apply, ← ha]
    change _ = (b*a*b⁻¹)^2
    simp [pow_two, mul_assoc]

namespace Chart

variable {H : Type*} [Group H] {K : Subgroup H} [K.Normal] {j : D →* K} (C : Chart j)

private theorem equal_cosets {x y : H} {u v : Sample}
    (au : ∀ i, C.val (u.act i) = MulAut.conj x (C.val i))
    (av : ∀ i, C.val (v.act i) = MulAut.conj y (C.val i))
    (su : ∀ l, u.square = some l → C.val l = x ^ 2)
    (sv : ∀ l, v.square = some l → C.val l = y ^ 2)
    (he : QuotientGroup.mk' K x = QuotientGroup.mk' K y) : apart C.law u v = false := by
  have hk : x*y⁻¹ ∈ K := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' K (x*y⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  let k := C.rep.symm ⟨x*y⁻¹,hk⟩
  have hval : C.val k = x*y⁻¹ := congrArg Subtype.val (C.rep.apply_symm_apply _)
  have matchK : compatible C.law u v k = true := by
    simp only [compatible, Bool.and_eq_true, List.all_eq_true, beq_iff_eq]
    constructor
    · intro i _
      apply C.vinj
      rw [C.vmul, C.vmul, au, av, hval, MulAut.conj_apply, MulAut.conj_apply]
      group
    · cases hu : u.square with
      | none => rfl
      | some l =>
        cases hv : v.square with
        | none => rfl
        | some r =>
          apply beq_iff_eq.mpr
          apply C.vinj
          rw [su l hu, C.vmul, C.vmul, av, hval, sv r hv, MulAut.conj_apply]
          simp [pow_two, mul_assoc]
  have h := List.any_eq_true.mpr ⟨k, exhaustive k, matchK⟩
  simp [apart, h]

/-- Transport the finite test back to the actual quotient. In particular,
an outer automorphism satisfying a formal identity is never assumed to lift:
we use only the three roots supplied in the host. -/
theorem seven_cosets [Finite H] (ck : test C.law = true)
    {a b c : H} (ha : a ^ 2 = C.val R) (hb : b ^ 2 = C.val S) (hc : c ^ 2 = C.val V) :
    7 ≤ K.index := by
  classical
  let f := transform C.law (C.images a)
  let g := transform C.law (C.images b)
  let h := transform C.law (C.images c)
  have ea := C.candidates_mem .rot ha
  have eb := C.candidates_mem .flip hb
  have ec := C.candidates_mem .third hc
  simp only [test, C.ok, Bool.not_true, Bool.false_or, List.all_eq_true] at ck
  have pass := ck _ eb _ ec _ ea
  obtain ⟨ws, hm, hw⟩ := List.any_eq_true.mp pass
  let sampleOf := sample f g h
  have pw : ws.Pairwise (fun i j => apart C.law (sampleOf i) (sampleOf j) = true) :=
    of_decide_eq_true hw
  have hb4 : b ^ 4 = 1 := by
    change b ^ (2*2) = 1
    rw [pow_mul, hb]
    change (C.rep (s, false) : H) ^ 2 = 1
    rw [C.base, ← Subgroup.coe_pow, ← map_pow, show s ^ 2 = 1 by decide, map_one, Subgroup.coe_one]
  let q (w : W) := QuotientGroup.mk' K (W.value a b c w)
  have nd : (ws.map q).Nodup := by
    apply List.pairwise_map.mpr
    apply pw.imp
    intro i j haij eq
    have hfail := C.equal_cosets
      (action_word C.val a b c f g h (C.images_apply a) (C.images_apply b) (C.images_apply c) hb4 i)
      (action_word C.val a b c f g h (C.images_apply a) (C.images_apply b) (C.images_apply c) hb4 j)
      (square_word C.val a b c f g h C.vone ha hb hc (C.images_apply b) i)
      (square_word C.val a b c f g h C.vone ha hb hc (C.images_apply b) j) eq
    exact Bool.noConfusion (haij.symm.trans hfail)
  have hlen : ws.length = 7 := by
    simp only [menus, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with e | e | e <;> subst ws <;> rfl
  let _ := Fintype.ofFinite (H ⧸ K)
  have bound := (ws.map q).toFinset.card_le_univ
  rwa [List.toFinset_card_of_nodup nd, List.length_map, hlen, ← Nat.card_eq_fintype_card] at bound

end Chart
end Kourovka1846.D8.Marked
