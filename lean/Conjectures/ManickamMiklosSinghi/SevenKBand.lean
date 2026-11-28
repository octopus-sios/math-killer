import Conjectures.ManickamMiklosSinghi.SevenKGap
import Conjectures.ManickamMiklosSinghi.SevenKCaps
import Conjectures.ManickamMiklosSinghi.SevenKNormalize
import Conjectures.ManickamMiklosSinghi.SevenKBootstrap
namespace ManickamMiklosSinghi.SevenK
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- One bootstrap row, with its complement hypothesis applied to actual
nonnegative-total residual lists. -/
theorem band_centered (k : ℕ) (hk : 2 ≤ k) (hn : 5*k ≤ Fintype.card α)
    (x : α → ℝ) (hx : ∑ i,x i=0) (hs : ∑ i,(x i)^2=1)
    (b : Band) (hrw : b=row1 ∨ b=row2 ∨ b=row3 ∨ b=row4)
    (l : ℝ) (hl : 0 ≤ l) (hGl : b.gHi=(1-2*l)/(1-l))
    (hpL : l ≤ (k:ℝ)/Fintype.card α) (hpP : (k:ℝ)/Fintype.card α ≤ b.P)
    (small : ∀ V : Finset α, V.card=Fintype.card α-k → 0 ≤ ∑ i ∈ V,x i →
      b.rc*((k:ℝ)/V.card) ≤ av (V.powersetCard k) (score x)) :
    b.r*((k:ℝ)/Fintype.card α) ≤ av (univ.powersetCard k) (score x) := by
  classical
  let n := Fintype.card α
  let p := (k:ℝ)/n
  let v := ((n:ℝ)-k)/(n-1)
  let g := ((n:ℝ)-2*k)/(n-2)
  let w := ((k:ℝ)-1)*((n:ℝ)-k-1)/(((n:ℝ)-2)*(n-3))
  let t := (k:ℝ)/((n:ℝ)-k)
  let K := (univ : Finset α).powersetCard k
  let G := score x
  let R := av K G/p
  obtain ⟨hb,_⟩ := rows_certified b hrw
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hnR : 5*(k:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith only [hkR,hnR]
  have hnk : 0 < (n:ℝ)-k := by linarith only [hkR,hnR]
  obtain ⟨hp,hv,_,hw,hw',hw6,hg,hg'⟩ := moment_param_bounds n k p v g w l b.P hkR hnR
    rfl rfl rfl rfl hl hpL hpP hb.P_le
  have hP1 : b.P < 1 := by linarith only [hb.P_le]
  have hp1 := hpP.trans_lt hP1
  have hpt : (1-p)*t=p := by
    dsimp only [p,t]
    field_simp [hn0.ne',hnk.ne']
  have ht0 : 0 ≤ t := div_nonneg (Nat.cast_nonneg _) hnk.le
  have htT : t ≤ b.T := by
    change t ≤ b.P/(1-b.P)
    rw [show t=p/(1-p) from (eq_div_iff (sub_pos.mpr hp1).ne').2 (by rwa [mul_comm]),
      div_le_div_iff₀ (sub_pos.mpr hp1) (sub_pos.mpr hP1)]
    linarith only [hpP]
  by_contra! hgoal
  change av K G < b.r*p at hgoal
  have hR : R < b.r := (div_lt_iff₀ hp).2 hgoal
  have hpr : p*R = av K G := by rw [mul_comm]; exact div_mul_cancel₀ _ hp.ne'
  have hne : (univ : Finset α).Nonempty := card_pos.mp (by rw [card_univ]; omega)
  obtain ⟨i,_,hi⟩ := exists_max_image univ x hne
  obtain ⟨j,_,hj⟩ := exists_min_image univ x hne
  have hi0 : 0 ≤ x i := by
    by_contra! h
    exact (sum_neg (fun q hq => (hi q hq).trans_lt h) hne).ne hx
  have hj0 : x j ≤ 0 := by
    by_contra! h
    exact (sum_pos (fun q hq => h.trans_le (hj q hq)) hne).ne' hx
  let U := (univ : Finset α).erase i
  let F := fun T => 1-G (insert i T)
  let bad := av (U.powersetCard (k-1)) F
  have hU : U.card=n-1 := by simp [U,n]
  have hF : BitOn (U.powersetCard (k-1)) F := by
    intro T _; dsimp [F,G,score,nonnegInd]; split_ifs <;> norm_num
  have hG : BitOn (U.powersetCard k) G := by
    intro T _; dsimp [G,score,nonnegInd]; split_ifs <;> simp
  have hgood : av (U.powersetCard (k-1)) (fun T => G (insert i T)) = 1-bad := by
    dsimp only [bad,F]
    rw [av_sub,av_const (slice_ne _ (by rw [hU]; dsimp only [n]; omega))]
    ring
  have hexp : p*R = p*(1-bad)+(1-p)*av (U.powersetCard k) G := by
    rw [hpr,← hgood]
    exact star_split k hk (by omega) i G
  have hcmp (T : Finset α) (hT : T ∈ U.powersetCard (k-1)) (hB : F T=1) :
      t*b.rc ≤ av ((U \ T).powersetCard k) G := by
    obtain ⟨ht,hc⟩ := mem_powersetCard.mp hT
    have hcard : (U \ T).card=n-k := by rw [card_sdiff_of_subset ht,hc,hU]; dsimp only [n]; omega
    have hneg : ∑ q ∈ insert i T,x q < 0 := by
      by_contra! h
      simp [F,G,score,nonnegInd,h] at hB
    have he : U \ T = (insert i T)ᶜ := by ext q; simp [U]
    have hsum := (sum_add_sum_compl (insert i T) x).trans hx
    have htot : 0 ≤ ∑ q ∈ U \ T,x q := by rw [he]; linarith only [hsum,hneg]
    have H := small _ hcard htot
    rw [hcard,Nat.cast_sub (show k ≤ n by dsimp only [n]; omega)] at H
    simpa only [t,mul_comm] using H
  obtain ⟨hbad,hbad',hgap,hmix⟩ := gap_from_complement U n k hU hk (by dsimp only [n]; omega)
    F G hF hG p t R b.r b.rc hp hp1 rfl hpt hR hb.r_le hcmp hexp
  obtain ⟨hvar,hm,hcs,hneg,htot⟩ := cap_data k hk hn x hx hs i j hi0 hj0 b.r hgoal.le
  have hkn : k ≤ Fintype.card α := by omega
  obtain ⟨m₁,m₂,m₃,m₄,_⟩ := slice_identities k x hkn (by omega) hx hs
  have hd : (K.card:ℝ) = (n.choose k:ℝ) := by simp [K,n]
  have dens : (∑ S ∈ K,(1/(n.choose k:ℝ))*G S) = p*R := by
    rw [← hd,weighted_mean,hpr]
  have hA := single_le_sum (s:=univ) (fun q (_ : q ∈ (univ : Finset α)) => sq_nonneg (x q)) (mem_univ i)
  rw [hs] at hA
  exact bootstrap_band K univ j (mem_univ _) (fun _ => 1/(n.choose k:ℝ))
    (fun S => ∑ q ∈ S,x q) x b hrw p v w g R (-x j) (x i) bad t _ _ _ hp hpP
    (by linarith only [hv,hpP]) hR hw hw' hw6 hg (hGl ▸ hg') (neg_nonneg.mpr hj0) hA
    (neg_neg _).symm (by simpa only [neg_neg] using hj) hi hs (fun _ _ => by positivity)
    m₁ m₂ m₃ m₄ dens hbad hbad' hgap ht0 htT hmix hvar hm hcs hneg htot

end ManickamMiklosSinghi.SevenK
