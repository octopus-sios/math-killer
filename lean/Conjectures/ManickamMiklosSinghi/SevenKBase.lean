import Conjectures.ManickamMiklosSinghi.SevenKReduction
import Conjectures.ManickamMiklosSinghi.SevenKMomentWeights
import Conjectures.ManickamMiklosSinghi.SevenKParams
import Conjectures.ManickamMiklosSinghi.SevenKStart
namespace ManickamMiklosSinghi.SevenK
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Bundle of slice moment identities in the uniform weights consumed by the
sign and bootstrap inequalities. Singleton incidence is included. -/
theorem slice_identities (k : ℕ) (x : α → ℝ) (hk : k ≤ Fintype.card α)
    (hn : 4 ≤ Fintype.card α) (hx : ∑ i, x i=0) (hs : ∑ i, (x i)^2=1) :
    let n := Fintype.card α
    let D : ℝ := n.choose k
    let K := (univ : Finset α).powersetCard k
    let Y := fun S : Finset α => ∑ i ∈ S, x i
    let p := (k:ℝ)/n
    let v := ((n:ℝ)-k)/(n-1)
    let g := ((n:ℝ)-2*k)/(n-2)
    let w := ((k:ℝ)-1)*((n:ℝ)-k-1)/(((n:ℝ)-2)*(n-3))
    let B := 3*w+(1-6*w)*(∑ i, (x i)^4)
    (∑ S ∈ K, (1/D)*Y S) = 0 ∧
    (∑ S ∈ K, (1/D)*(Y S)^2) = p*v ∧
    (∑ S ∈ K, (1/D)*(Y S)^3) = p*v*g*(∑ i, (x i)^3) ∧
    (∑ S ∈ K, (1/D)*(Y S)^4) = p*v*B ∧
    (∀ i : α, (∑ S ∈ K, (1/D)*(if i ∈ S then Y S else 0)) = p*v*x i) := by
  classical
  dsimp only
  let n := Fintype.card α
  let D : ℝ := n.choose k
  let d := Cnt n k
  have hDn : 0 < n.choose k := Nat.choose_pos hk
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast hDn
  have hd0 : d 0=D := by dsimp only [d, Cnt, D]; rw [Nat.sub_zero, Nat.choose_symm hk]
  obtain ⟨e₂,e₃,e₄₁,e₄₂⟩ := moment_weights hk hn
  change d 1-d 2 = d 0*_ * _ at e₂
  change d 1-3*d 2+2*d 3 = d 0*_ * _ * _ at e₃
  change d 2-2*d 3+d 4 = d 0*_ * _ * _ at e₄₁
  change d 1-7*d 2+12*d 3-6*d 4 = d 0*_ * _ * _ at e₄₂
  rw [hd0] at e₂ e₃ e₄₁ e₄₂
  obtain ⟨m1,m2,m3,m4⟩ := centered_raw_moments k hk x hx
  simp only [raw,empty_subset,ite_true,pow_one] at m1 m2 m3 m4
  rw [e₂,hs] at m2
  rw [e₃] at m3
  rw [e₄₁,e₄₂,hs] at m4
  have hD' : (1/D)*D=1 := by field_simp [hD.ne']
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [← Finset.mul_sum,m1,mul_zero]
  · rw [← Finset.mul_sum,m2]
    change (1/D)*(D*_ * _ * 1)=_
    linear_combination ( (k:ℝ)/n * (((n:ℝ)-k)/(n-1)) ) * hD'
  · rw [← Finset.mul_sum,m3]
    change (1/D)*(D*_*_*_*_)=_
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc,hD',one_mul]
  · rw [← Finset.mul_sum,m4]
    change (1/D)*(3*(D*_*_*_)*1^2+(D*_*_*_)*_) = _
    field_simp [hD.ne']
  · intro i
    have hc := raw_one k hk x hx {i}
    simp only [raw,singleton_subset_iff,pow_one,ps,sum_singleton,card_singleton,
      diff,Nat.reduceAdd] at hc
    rw [e₂] at hc
    rw [← Finset.mul_sum,hc]
    change (1/D)*(D*_*_*_)=_
    rw [← mul_assoc, ← mul_assoc, ← mul_assoc,hD',one_mul]

/-- Genuine unconditional 69/100-star density for centered unit lists on
the k-slice when n ≥ 5k and k ≥ 2. -/
theorem centered_five_k (k : ℕ) (x : α → ℝ) (hk : 2 ≤ k)
    (hn : 5*k ≤ Fintype.card α) (hx : ∑ i, x i=0) (hs : ∑ i, (x i)^2=1) :
    69/100 * ((k:ℝ)/Fintype.card α) * ((Fintype.card α).choose k:ℝ) <
      ((good (univ : Finset α) k x).card:ℝ) := by
  classical
  let n := Fintype.card α
  let D : ℝ := n.choose k
  let p := (k:ℝ)/n
  let v := ((n:ℝ)-k)/(n-1)
  let g := ((n:ℝ)-2*k)/(n-2)
  let w := ((k:ℝ)-1)*((n:ℝ)-k-1)/(((n:ℝ)-2)*(n-3))
  let K := (univ : Finset α).powersetCard k
  let Y := fun S : Finset α => ∑ i ∈ S, x i
  let G : ℝ := (good univ k x).card
  let R := G/(p*D)
  let B := 3*w+(1-6*w)*(∑ i, (x i)^4)
  have hn0 : 0 < n := by dsimp only [n]; omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hk' : k ≤ n := by dsimp only [n]; omega
  have hD : 0 < D := by dsimp only [D]; exact_mod_cast Nat.choose_pos hk'
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hnK : 5*(k:ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < p := div_pos (by linarith) hnR
  have hp' : p ≤ 1/5 := (div_le_iff₀ hnR).2 (by linarith)
  have hb := moment_param_bounds n k p v g w 0 (1/5) hkR hnK rfl rfl rfl rfl
    (le_refl _) hp.le hp' (le_refl _)
  obtain ⟨h₁,h₂,h₃,h₄,hsing⟩ := slice_identities k x hk' (by omega) hx hs
  have hR : (∑ S ∈ K, (1/D)*nonnegInd (Y S)) = p*R := by
    have hG : ∑ S ∈ K, nonnegInd (Y S) = G := by
      simp only [K, Y, G, good, nonnegInd, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [← Finset.mul_sum,hG]
    dsimp [R]
    field_simp [hD.ne',hp.ne']
  have hR0 : 0 ≤ R := div_nonneg (Nat.cast_nonneg _) (mul_nonneg hp.le hD.le)
  have H := start_from_moments univ K x Y (fun _ => 1/D) p v w R B hp
    (by linarith only [hp',hb.2.1]) hR0 hb.2.2.2.1 hb.2.2.2.2.2.1
    (fun _ _ => by positivity) hs h₁ h₂ h₄ rfl (fun i _ => hsing i) hR
  change 69/100*p*D<G
  have h := (lt_div_iff₀ (mul_pos hp hD)).mp H
  nlinarith only [h]

end ManickamMiklosSinghi.SevenK
