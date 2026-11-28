import Conjectures.Kourovka1846SquareOvergroup.Table
import Mathlib.GroupTheory.IndexNormal

/-!
# Normal forms for the order-sixteen kernel

Change the outside representative by an element of the dihedral subgroup to
normalize its action. The resulting chart carries the actual group law.
-/

namespace Kourovka1846.D8.Marked

/-- A multiplication chart on an order-sixteen group containing the marked
dihedral subgroup. The first eight normal forms represent that subgroup. -/
structure Chart {K : Type*} [Group K] (j : D →* K) where
  law : Law
  ok : law.allowed = true
  rep : E ≃ K
  base (d : D) : rep (d, false) = j d
  mul (u v : E) : rep (law.mul u v) = rep u * rep v

private theorem normalize (f : D ≃* D) :
    ∃ (v : D) (k : Bool), v * f r * v⁻¹ = r ∧
      v * f s * v⁻¹ = (if k then (.sr 1 : D) else s) := by
  have hr : (f r) ^ 2 ≠ 1 := by
    rw [← map_pow, ← f.map_one, f.injective.ne_iff]
    decide
  have hs : (f s) ^ 2 = 1 := by rw [← map_pow, show s ^ 2 = 1 by decide, map_one]
  have hn : f s ≠ 1 := by rw [← f.map_one, f.injective.ne_iff]; decide
  have hd : f s ≠ (f r) ^ 2 := by rw [← map_pow, f.injective.ne_iff]; decide
  exact (by decide : ∀ p q : D, p ^ 2 ≠ 1 → q ^ 2 = 1 → q ≠ 1 → q ≠ p ^ 2 →
    ∃ (v : D) (k : Bool), v * p * v⁻¹ = r ∧
      v * q * v⁻¹ = (if k then (.sr 1 : D) else s)) _ _ hr hs hn hd

theorem chart_exists {K : Type*} [Group K] [Finite K]
    (j : D →* K) (hj : Function.Injective j) (hk : Nat.card K = 16) :
    Nonempty (Chart j) := by
  classical
  have hd : Nat.card j.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, DihedralGroup.nat_card]
  have hidx : j.range.index = 2 := by
    have h := j.range.index_mul_card
    rw [hd, hk] at h
    omega
  let _ := Subgroup.normal_of_index_eq_two hidx
  have hprop : ∃ y : K, y ∉ j.range := by
    by_contra! h
    have he := j.range.eq_top_iff'.mpr h
    rw [he, Subgroup.card_top, hk] at hd
    contradiction
  obtain ⟨y, hy⟩ := hprop
  let en := MonoidHom.ofInjective hj
  let f : D ≃* D := (en.trans (MulAut.conjNormal y)).trans en.symm
  have fy (d : D) : j (f d) = y * j d * y⁻¹ := by
    simp only [f, en, MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
      MulAut.conjNormal_apply, MonoidHom.ofInjective_apply]
  obtain ⟨v, k, hp, hq⟩ := normalize f
  let x := j v * y
  have hx : x ∉ j.range := fun h => hy ((j.range.mul_mem_cancel_left ⟨v,rfl⟩).mp h)
  have conj (d : D) : MulAut.conj x (j d) = j (v * f d * v⁻¹) := by
    change (j v * y) * j d * (j v * y)⁻¹ = _
    simp only [j.map_mul, j.map_inv, fy, mul_inv_rev]
    group
  have cr : MulAut.conj x (j r) = j r := (conj r).trans (congrArg j hp)
  have cs := (conj s).trans (congrArg j hq)
  have rot (i : ZMod 4) : MulAut.conj x (j (.r i)) = j (.r i) := by
    have e : (.r i : D) = r ^ i.val := by rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    rw [e, map_pow, map_pow, cr]
  have act (d : D) : MulAut.conj x (j d) = j (twist k d) := by
    cases d with
    | r i => exact rot i
    | sr i =>
      have t : s * (.r i : D) = .sr i := by simp
      calc
        _ = MulAut.conj x (j (s * .r i)) := by rw [t]
        _ = j ((if k then (.sr 1 : D) else s) * .r i) := by rw [j.map_mul, (MulAut.conj x).map_mul, cs, rot, j.map_mul]
        _ = _ := by cases k <;> simp [twist]
  obtain ⟨a, ha⟩ := Subgroup.sq_mem_of_index_two hidx x
  let L : Law := ⟨k,a⟩
  have fs (d : D) : twist k (twist k d) * a = a * d := by
    apply hj
    simp only [j.map_mul, ha, ← act, MulAut.conj_apply, pow_two]
    group
  have fa : twist k a = a := by apply hj; rw [← act, ha, MulAut.conj_apply]; group
  have ok : L.allowed = true := by simp [L, Law.allowed, fa, fs]
  let val (u : E) := j u.1 * (if u.2 then x else 1)
  have flag (u : E) : val u ∈ j.range ↔ u.2 = false := by
    obtain ⟨d,b⟩ := u
    cases b <;> simp [val, j.range.mul_mem_cancel_left (show j d ∈ j.range from ⟨d,rfl⟩), hx]
  have inj : Function.Injective val := by
    rintro ⟨d,b⟩ ⟨t,c⟩ h
    have he : b = false ↔ c = false := by
      change (d,b).2 = false ↔ (t,c).2 = false
      rw [← flag, ← flag, h]
    have e : b = c := by cases b <;> cases c <;> simp_all
    subst c
    exact Prod.ext (hj (mul_right_cancel h)) rfl
  have cE : Nat.card E = 16 := by
    rw [Nat.card_prod, DihedralGroup.nat_card, Nat.card_eq_fintype_card (α := Bool)]
    decide
  have bij := (Nat.bijective_iff_injective_and_card val).mpr ⟨inj,cE.trans hk.symm⟩
  refine ⟨⟨L, ok, Equiv.ofBijective val bij, fun d => by simp [val],
    ?_⟩⟩
  rintro ⟨u,i⟩ ⟨v',b⟩
  change val (L.mul _ _) = val _ * val _
  cases i <;> cases b <;>
    simp [val, L, Law.mul, ha, ← act, MulAut.conj_apply, pow_two] <;> group

end Kourovka1846.D8.Marked
