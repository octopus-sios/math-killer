module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

@[expose] public section

/-!
# Reducing small simultaneous hosts to a normal kernel of order sixteen

A free cyclic action and a conjugacy-class bound force the host order to
be divisible by 32. Two maximal subgroups suffice for the 2-group case;
in order 96 we use the permutation action on three cosets.
-/

namespace Kourovka1846

namespace D8

abbrev D := DihedralGroup 4

abbrev r : D := DihedralGroup.r 1
abbrev s : D := DihedralGroup.sr 0
abbrev z : D := r ^ 2

theorem fourth_power (x : D) : x ^ 4 = 1 := by
  exact (by decide : ∀ x : D, x ^ 4 = 1) x

theorem rot_sq_ne_one : r ^ 2 ≠ 1 := by decide

theorem rot_conj_ne : s * r * s⁻¹ ≠ r := by decide

theorem rot_or_inv (x : D) (hx : x ^ 2 ≠ 1) : x = r ∨ x = r⁻¹ :=
  (by decide : ∀ y : D, y ^ 2 ≠ 1 → y = r ∨ y = r⁻¹) x hx

variable {H : Type*} [Group H] (ι : D →* H) (hi : Function.Injective ι)

include hi in
/-- In a normal copy of the dihedral group, a square cannot invert the
rotation: its conjugation is the square of a permutation of the two
generators of the rotation subgroup. -/
theorem range_not_normal (hs : ∃ h : H, h ^ 2 = ι s) : ¬ ι.range.Normal := by
  rintro hn
  obtain ⟨h, hh⟩ := hs
  let f := MulAut.conj h
  obtain ⟨x, hx⟩ := hn.conj_mem (ι r) (show ι r ∈ ι.range from ⟨r, rfl⟩) h
  change ι x = f (ι r) at hx
  have hx2 : x ^ 2 ≠ 1 := by
    intro he
    apply rot_sq_ne_one
    apply hi
    apply f.injective
    simpa only [map_pow, map_one, hx] using congrArg ι he
  have hfix : f (f (ι r)) = ι r := by
    rcases rot_or_inv x hx2 with e | e
    · have hfr : f (ι r) = ι r := hx.symm.trans (congrArg ι e)
      rw [hfr, hfr]
    · have hfr : f (ι r) = (ι r)⁻¹ := by rw [← hx, e, map_inv]
      rw [hfr, map_inv, hfr, inv_inv]
  have hconj : f (f (ι r)) = (MulAut.conj (ι s)) (ι r) := by
    change (MulAut.conj h * MulAut.conj h) _ = _
    rw [← map_mul, ← pow_two, hh]
  apply rot_conj_ne
  apply hi
  rw [map_mul, map_mul, map_inv]
  exact hconj.symm.trans hfix

end D8
end Kourovka1846

namespace Kourovka1846.D8

open Subgroup

/-- Two cyclic groups of orders eight and four give a free action of the
second on the cosets of the first if their involutions are not conjugate. -/
theorem dvd_32_of_distinct_involutions {H : Type*} [Group H] [Finite H]
    {a b : H} (ha : orderOf a = 8) (hb : orderOf b = 4)
    (hn : ¬ IsConj (b ^ 2) (a ^ 4)) : 32 ∣ Nat.card H := by
  classical
  let A := zpowers a
  let B := zpowers b
  have hb4 : b ^ 4 = 1 := hb ▸ pow_orderOf_eq_one b
  have nofix (q : H ⧸ A) : (b ^ 2) • q ≠ q := by
    induction q using Quotient.inductionOn' with
    | _ y =>
      intro h
      change (QuotientGroup.mk (b ^ 2 * y) : H ⧸ A) = QuotientGroup.mk y at h
      let c := MulAut.conj y⁻¹ (b ^ 2)
      have hc : c ∈ zpowers a := by
        simpa [c, MulAut.conj_apply, mul_assoc] using QuotientGroup.eq.mp h.symm
      have oc : orderOf c = 2 := by
        change orderOf (MulAut.conj y⁻¹ (b ^ 2)) = _
        rw [MulEquiv.orderOf_eq, orderOf_pow, hb]
        decide
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hc)
      have hi8 : i < 8 := ha ▸ Finset.mem_range.mp hi
      have hi2 : 8 ∣ i * 2 := by
        have t := pow_orderOf_eq_one c
        rwa [oc, ← he, ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, ha] at t
      have hi0 : i ≠ 0 := by
        rintro rfl
        simp only [pow_zero] at he
        rw [← he, orderOf_one] at oc
        contradiction
      have hi4 : i = 4 := by omega
      apply hn
      refine isConj_iff.mpr ⟨y⁻¹, ?_⟩
      exact hi4 ▸ he.symm
  have hstab (q : H ⧸ A) : MulAction.stabilizer B q = ⊥ := by
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro ⟨g, hg⟩ hfix
    change g • q = q at hfix
    apply Subtype.ext
    change g = 1
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hg)
    have hi4 : i < 4 := hb ▸ Finset.mem_range.mp hi
    rw [← he] at hfix ⊢
    have hs : ((b ^ i) ^ 2) • q = q := by rw [pow_two, mul_smul, hfix, hfix]
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with h | h | h | h
    · simp [h]
    · exact (nofix q (by simpa [h] using hs)).elim
    · exact (nofix q (h ▸ hfix)).elim
    · have eq : (b ^ 3) ^ 2 = b ^ 2 := by
        rw [← pow_mul, show 3 * 2 = 4 + 2 by decide, pow_add, hb4, one_mul]
      exact (nofix q (by simpa only [h, eq] using hs)).elim
  have ca : Nat.card A = 8 := (Nat.card_zpowers a).trans ha
  have cb : Nat.card B = 4 := (Nat.card_zpowers b).trans hb
  have ct := A.card_eq_card_quotient_mul_card_subgroup
  rw [ca] at ct
  have cd := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  rw [Nat.card_prod, cb] at cd
  omega


private def onClass {H : Type*} [Group H] (c : H) :
    H →* Equiv.Perm (conjugatesOf c) where
  toFun h := {
    toFun x := ⟨MulAut.conj h x.1, x.2.trans (isConj_iff.mpr ⟨h, rfl⟩)⟩
    invFun x := ⟨MulAut.conj h⁻¹ x.1, x.2.trans (isConj_iff.mpr ⟨h⁻¹, rfl⟩)⟩
    left_inv x := Subtype.ext (by simp [MulAut.conj_apply, mul_assoc])
    right_inv x := Subtype.ext (by simp [MulAut.conj_apply, mul_assoc]) }
  map_one' := by ext x; simp
  map_mul' h k := by ext x; simp [MulAut.conj_apply, mul_assoc]

private def invol : Fin 5 → D := ![z, s, DihedralGroup.sr 1, DihedralGroup.sr 2, DihedralGroup.sr 3]

/-- For a host smaller than 128, the rotation's central involution cannot
be conjugate to all four reflections. Its conjugacy class is small, and its
action on that class is an even permutation fixing at least five points. -/
private theorem not_all_fused {H : Type*} [Group H] [Finite H]
    (ι : D →* H) (hi : Function.Injective ι) (hsize : Nat.card H < 128)
    {a : H} (ha : a ^ 2 = ι r) :
    ¬ (∀ i : Fin 5, IsConj (ι z) (ι (invol i))) := by
  classical
  intro hf
  let C := Subgroup.centralizer ({ι z} : Set H)
  have hd : ι.range ≤ C := by
    rintro _ ⟨x, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← map_mul, ← map_mul]
    exact congrArg ι ((by decide : ∀ x : D, x * z = z * x) x)
  have ha4 : a ^ 4 = ι z := by
    change a ^ (2 * 2) = ι (r ^ 2)
    rw [pow_mul, ha, map_pow]
  have haC : a ∈ C := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    rw [← ha4]
    exact (Commute.self_pow a 4).eq
  have haD : a ∉ ι.range := by
    rintro ⟨g, hg⟩
    have hz := (congrArg ι (fourth_power g))
    rw [map_pow, hg, ha4, map_one] at hz
    exact rot_sq_ne_one (hi (hz.trans ι.map_one.symm))
  have hl : ι.range < C := lt_of_le_of_ne hd (fun h => haD (h ▸ haC))
  have ce : Nat.card ι.range = 8 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv, DihedralGroup.nat_card]
  have hdvd := Subgroup.card_dvd_of_le hd
  have hlt := Subgroup.card_lt_of_lt hl
  rw [ce] at hdvd hlt
  have h16 : 16 ≤ Nat.card C := by omega
  let X := ↥(conjugatesOf (ι z))
  let _ : Fintype X := Fintype.ofFinite X
  have hcard : Fintype.card X < 8 := by
    have cf := C.index_mul_card
    change (Subgroup.centralizer {ι z}).index * _ = _ at cf
    rw [Subgroup.index_centralizer_eq_ncard, ← Nat.card_coe_set_eq] at cf
    change Nat.card X * _ = _ at cf
    rw [Nat.card_eq_fintype_card] at cf
    by_contra! he
    have := Nat.mul_le_mul he h16
    omega
  let ρ : H →* Equiv.Perm X := onClass (ι z)
  have fixed (i : Fin 5) : ρ (ι z) (⟨_, hf i⟩ : X) = ⟨_, hf i⟩ := by
    apply Subtype.ext
    change ι z * ι (invol i) * (ι z)⁻¹ = ι (invol i)
    rw [← map_inv, ← map_mul, ← map_mul]
    exact congrArg ι ((by decide : ∀ x : D, z * x * z⁻¹ = x) _)
  let f (i : Fin 5) : ↥((ρ (ι z)).supportᶜ) :=
    ⟨⟨_, hf i⟩, Finset.mem_compl.mpr (Equiv.Perm.notMem_support.mpr (fixed i))⟩
  have hf' : Function.Injective f := by
    intro i j h
    exact (by decide : Function.Injective invol) (hi (congrArg (fun x => x.1.1) h))
  have h5 := Fintype.card_le_of_injective f hf'
  simp only [Fintype.card_fin, Fintype.card_coe, Finset.card_compl] at h5
  have triv : ρ (ι z) = 1 := by
    by_contra hnon
    have hlb := Equiv.Perm.two_le_card_support_of_ne_one hnon
    have sw := Equiv.Perm.card_support_eq_two.mp (show (ρ (ι z)).support.card = 2 by omega)
    obtain ⟨x, y, hxy, he⟩ := sw
    have hsgn := congrArg Equiv.Perm.sign he
    let χ : D →* ℤˣ := Equiv.Perm.sign.comp (ρ.comp ι)
    change χ (r ^ 2) = _ at hsgn
    rw [map_pow, Equiv.Perm.sign_swap hxy] at hsgn
    simp at hsgn
  obtain ⟨k, hk⟩ := isConj_iff.mp (hf 1)
  change k * ι z * k⁻¹ = ι s at hk
  have hs : ρ (ι s) = 1 := by rw [← hk, map_mul, map_mul, map_inv, triv, mul_one, mul_inv_cancel]
  have he := congrArg (fun p : Equiv.Perm X => (p ⟨_, hf 2⟩).1) hs
  change ι s * ι (DihedralGroup.sr 1) * (ι s)⁻¹ = ι (DihedralGroup.sr 1) at he
  rw [← map_inv, ← map_mul, ← map_mul] at he
  exact (by decide : s * DihedralGroup.sr 1 * s⁻¹ ≠ DihedralGroup.sr 1) (hi he)


/-- Odd multiples of 16 (in particular 48, 80 and 112) are excluded at
once by the two cyclic actions. No solvability or classification theorem
is used. -/
theorem dvd_32_of_card_lt {H : Type*} [Group H] [Finite H]
    (ι : D →* H) (hi : Function.Injective ι)
    (hsq : ∀ g : D, ∃ h : H, h ^ 2 = ι g) (hsize : Nat.card H < 128) :
    32 ∣ Nat.card H := by
  classical
  obtain ⟨a, ha⟩ := hsq r
  have ha4 : a ^ 4 = ι z := by
    change a ^ (2 * 2) = ι (r ^ 2)
    rw [pow_mul, ha, map_pow]
  have ha8 : a ^ 8 = 1 := by
    change a ^ (2 * 4) = 1
    rw [pow_mul, ha, ← map_pow, fourth_power, map_one]
  have hoa : orderOf a = 8 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 2) _ ha8
    change a ^ 4 ≠ 1
    exact fun e => rot_sq_ne_one (hi (ha4.symm.trans (e.trans ι.map_one.symm)))
  obtain ⟨i, hn⟩ := Classical.not_forall.mp (not_all_fused ι hi hsize ha)
  obtain ⟨b, hb⟩ := hsq (invol i)
  have hi2 := (by decide : ∀ j, (invol j) ^ 2 = 1 ∧ invol j ≠ 1) i
  have hb4 : b ^ 4 = 1 := by
    change b ^ (2 * 2) = 1
    rw [pow_mul, hb, ← map_pow, hi2.1, map_one]
  have hob : orderOf b = 4 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1) _ hb4
    change b ^ 2 ≠ 1
    exact fun e => hi2.2 (hi (hb.symm.trans (e.trans ι.map_one.symm)))
  apply dvd_32_of_distinct_involutions hoa hob
  rw [ha4, hb]
  exact fun h => hn h.symm


/-- A noncyclic 2-group has two distinct index-two subgroups. Their
intersection is normal of index four and contains every square. -/
theorem two_group_kernel {H : Type*} [Group H] [Finite H]
    (ι : D →* H) (hi : Function.Injective ι)
    (hsq : ∀ g : D, ∃ h : H, h ^ 2 = ι g) (hp : IsPGroup 2 H) :
    ∃ K : Subgroup H, K.Normal ∧ ι.range ≤ K ∧ K.index = 4 := by
  have nc : ¬ IsCyclic H := by
    intro _
    exact DihedralGroup.not_isCyclic (by decide : 4 ≠ 1) (isCyclic_of_injective ι hi)
  let _ := hp.isNilpotent
  obtain ⟨M, N, hn, hm2, hn2⟩ := hp.not_isCyclic_iff_exists_ne_index_eq_prime.mp nc
  let _ := Subgroup.normal_of_index_eq_two hm2
  let _ := Subgroup.normal_of_index_eq_two hn2
  refine ⟨M ⊓ N, inferInstance, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨h, hh⟩ := hsq x
    rw [← hh]
    exact ⟨Subgroup.sq_mem_of_index_two hm2 h, Subgroup.sq_mem_of_index_two hn2 h⟩
  · have hle : ¬ N ≤ M := by
      intro h
      exact hn (Subgroup.eq_of_le_of_card_ge h (by
        have h1 := M.index_mul_card
        have h2 := N.index_mul_card
        rw [hm2] at h1
        rw [hn2] at h2
        omega)).symm
    have hd := Subgroup.relIndex_dvd_index_of_normal M N
    rw [hm2] at hd
    have hne : M.relIndex N ≠ 1 := fun e => hle (Subgroup.relIndex_eq_one.mp e)
    have hri : M.relIndex N = 2 := (Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hne
    rw [Subgroup.index_inf, hri, hn2]

/-- In particular there is no simultaneous host of order 32. -/
theorem card_ne_32 {H : Type*} [Group H] [Finite H] (ι : D →* H)
    (hi : Function.Injective ι) (hsq : ∀ g : D, ∃ h : H, h ^ 2 = ι g) :
    Nat.card H ≠ 32 := by
  intro h
  have hp := IsPGroup.of_card (show Nat.card H = 2 ^ 5 from h)
  obtain ⟨K, hn, hle, hk⟩ := two_group_kernel ι hi hsq hp
  have hcard := K.index_mul_card
  rw [hk, h] at hcard
  have he : ι.range = K := Subgroup.eq_of_le_of_card_ge hle (by
    rw [← Nat.card_congr (MonoidHom.ofInjective hi).toEquiv, DihedralGroup.nat_card]
    omega)
  exact range_not_normal ι hi (hsq s) (he ▸ hn)


/-- At order 96 the action on the three cosets of a subgroup of order 32
kills the marked dihedral group. A cyclic image of order three would even
kill every root, giving a smaller host of order 32. -/
theorem mixed_kernel {H : Type*} [Group H] [Finite H]
    (ι : D →* H) (hi : Function.Injective ι)
    (hsq : ∀ g : D, ∃ h : H, h ^ 2 = ι g) (hc : Nat.card H = 96) :
    ∃ K : Subgroup H, K.Normal ∧ ι.range ≤ K ∧ Nat.card K = 16 := by
  classical
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2
    (n := 5) (by rw [hc]; decide)
  have hPi : P.index = 3 := by have := P.index_mul_card; rw [hc, hP] at this; omega
  let X := H ⧸ P
  let φ := MulAction.toPermHom H X
  have permcard : Nat.card (Equiv.Perm X) = 6 := by
    rw [Nat.card_perm]
    change P.index.factorial = 6
    rw [hPi]; decide
  have hle : φ.ker ≤ P := by
    intro h hm
    have e := congrArg (fun p : Equiv.Perm X => p (QuotientGroup.mk 1)) hm
    change (QuotientGroup.mk (h * 1) : X) = QuotientGroup.mk 1 at e
    simpa only [mul_one, inv_one, one_mul] using QuotientGroup.eq.mp e.symm
  have h3 := Subgroup.index_dvd_of_le hle
  rw [hPi] at h3
  have hd := φ.range.card_subgroup_dvd_card
  rw [permcard, ← Subgroup.index_ker] at hd
  have inc : ι.range ≤ φ.ker := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, hb⟩ := hsq x
    have h8 : orderOf (φ b) ∣ 8 := by
      apply orderOf_dvd_of_pow_eq_one
      change (φ b) ^ (2 * 4) = 1
      rw [← map_pow, pow_mul, hb, ← map_pow, fourth_power, map_one, map_one]
    have h6 := orderOf_dvd_natCard (φ b)
    rw [permcard] at h6
    have h2 : orderOf (φ b) ∣ 2 := Nat.dvd_gcd h8 h6
    change φ (ι x) = 1
    rw [← hb, map_pow]
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  have ks := φ.ker.index_mul_card
  rw [hc] at ks
  have hdiv := Nat.le_of_dvd (by decide : 0 < 6) hd
  have hpos : 0 < φ.ker.index := Nat.pos_of_dvd_of_pos hd (by decide)
  rcases (show φ.ker.index = 3 ∨ φ.ker.index = 6 by omega) with h | h
  · have cardR : Nat.card φ.range = 3 := (Subgroup.index_ker φ).symm.trans h
    let j := ι.codRestrict φ.ker fun g => inc ⟨g, rfl⟩
    have hj : Function.Injective j := fun x y e => hi (congrArg Subtype.val e)
    have roots (g : D) : ∃ b : φ.ker, b ^ 2 = j g := by
      obtain ⟨b, hb⟩ := hsq g
      let y := φ.rangeRestrict b
      have y2 : y ^ 2 = 1 := by
        apply Subtype.ext
        change φ b ^ 2 = 1
        rw [← map_pow, hb]
        exact inc ⟨g, rfl⟩
      have hy := orderOf_dvd_natCard y
      rw [cardR] at hy
      have ho : orderOf y ∣ 1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one y2) hy
      have he := orderOf_eq_one_iff.mp (Nat.dvd_one.mp ho)
      exact ⟨⟨b, congrArg Subtype.val he⟩, Subtype.ext hb⟩
    exact (card_ne_32 j hj roots (by rw [h] at ks; omega)).elim
  · exact ⟨_, inferInstanceAs φ.ker.Normal, inc, by rw [h] at ks; omega⟩

/-- Every hypothetical smaller simultaneous host has a normal subgroup of
order sixteen containing the marked copy. -/
theorem small_host_kernel {H : Type*} [Group H] [Finite H]
    (ι : D →* H) (hi : Function.Injective ι)
    (hsq : ∀ g : D, ∃ h : H, h ^ 2 = ι g) (hc : Nat.card H < 128) :
    ∃ K : Subgroup H, K.Normal ∧ ι.range ≤ K ∧ Nat.card K = 16 := by
  have dh := dvd_32_of_card_lt ι hi hsq hc
  have ne := card_ne_32 ι hi hsq
  have pos := Nat.card_pos (α := H)
  rcases (show Nat.card H = 64 ∨ Nat.card H = 96 by omega) with h | h
  · obtain ⟨K, hn, hle, hk⟩ := two_group_kernel ι hi hsq
        (IsPGroup.of_card (show Nat.card H = 2 ^ 6 from h))
    have ct := K.index_mul_card
    rw [hk, h] at ct
    exact ⟨K, hn, hle, by omega⟩
  · exact mixed_kernel ι hi hsq h

end Kourovka1846.D8
