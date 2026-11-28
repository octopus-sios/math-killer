import Conjectures.ManickamMiklosSinghi.Foundation

/-! # Sharp Bernoulli exceedance bounds
The probability space is the explicitly weighted Boolean cube.
-/

namespace ManickamMiklosSinghi

open Finset
open scoped BigOperators
noncomputable section

def strictExceedance {m : ℕ} (w : Fin m → ℝ) (p : ℝ) : ℝ :=
  ∑ v : Fin m → Bool, if p < ∑ i ∈ support v, w i then
    p ^ (support v).card * (1-p) ^ (m - (support v).card) else 0

namespace Bernoulli

private def hit {m q : ℕ} (r : Fin q) (c : Fin m → Fin q) (i : Fin m) : Bool :=
  decide (c i = r)

/-- Multiplicity of a specified Boolean pattern under a specified color. -/
private theorem hit_count {m q : ℕ} (r : Fin q) (v : Fin m → Bool) :
    (univ.filter (fun c : Fin m → Fin q => hit r c = v)).card =
      (q-1) ^ (m - (support v).card) := by
  classical
  let cell (i : Fin m) : Finset (Fin q) :=
    if v i = true then {r} else univ.erase r
  have he : (univ.filter (fun c : Fin m → Fin q => hit r c = v)) = Fintype.piFinset cell := by
    ext c
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
    apply forall_congr'
    intro i
    cases h : v i <;> simp [cell,hit,h]
  have cc (i : Fin m) : (cell i).card = if i ∈ (support v)ᶜ then q-1 else 1 := by
    cases h : v i <;> simp [cell,support,h]
  rw [he, Fintype.card_piFinset]
  simp_rw [cc]
  rw [← prod_filter, show univ.filter (fun i => i ∈ (support v)ᶜ) = (support v)ᶜ by ext; simp,
    prod_const, card_compl, Fintype.card_fin]

private theorem scale_mass {m q : ℕ} (hq : 0 < q) (v : Fin m → Bool) :
    (q : ℝ)^m * ((1/(q:ℝ))^(support v).card * (1-1/(q:ℝ))^(m-(support v).card)) =
      ((q:ℝ)-1)^(m-(support v).card) := by
  have h : (q:ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hs : (support v).card ≤ m := by simpa using card_le_univ (support v)
  rw [show 1-1/(q:ℝ) = ((q:ℝ)-1)/q by field_simp, div_pow, div_pow, one_pow,
    div_mul_div_comm, one_mul, ← pow_add, Nat.add_sub_of_le hs, mul_div_cancel₀ _ (pow_ne_zero _ h)]

end Bernoulli

open _root_.ManickamMiklosSinghi.Bernoulli in
/-- For reciprocal integer bias, at least one color class in every coloring meets
the average. Counting colorings gives the exact Bernoulli product masses.
No positivity assumption on the weights is needed for this argument. -/
theorem bernoulli_exceedance_unit_fraction {m q : ℕ} (hq : 0 < q)
    (w : Fin m → ℝ) (hw : ∑ i, w i = 1) :
    1/(q:ℝ) ≤ exceedance w (1/(q:ℝ)) := by
  classical
  let _ : NeZero q := ⟨hq.ne'⟩
  have hq' : 0 < (q:ℝ) := by exact_mod_cast hq
  let p : ℝ := 1/(q:ℝ)
  let F (v : Fin m → Bool) : ℝ := if p ≤ ∑ i ∈ support v, w i then 1 else 0
  have F0 v : 0 ≤ F v := by dsimp only [F]; split <;> norm_num
  have hbins (c : Fin m → Fin q) : ∑ r, ∑ i ∈ support (hit r c), w i = 1 := by
    simp only [support, hit, decide_eq_true_eq, sum_filter]
    rw [sum_comm]
    simpa using hw
  have wins (c : Fin m → Fin q) : 1 ≤ ∑ r, F (hit r c) := by
    have he : ∃ r, p ≤ ∑ i ∈ support (hit r c), w i := by
      by_contra! hh
      have H := sum_lt_sum_of_nonempty (s := (univ : Finset (Fin q))) univ_nonempty
        (fun r _ => hh r)
      rw [hbins] at H
      simp [p,nsmul_eq_mul, hq'.ne'] at H
    obtain ⟨r,hr⟩ := he
    simpa only [F, ite_eq_left hr] using
      (single_le_sum (s := univ) (f := fun j => F (hit j c)) (fun j _ => F0 _) (mem_univ r))
  have marginal (r : Fin q) : ∑ c : Fin m → Fin q, F (hit r c) =
      (q:ℝ)^m * exceedance w p := by
    calc
      _ = ∑ c : Fin m → Fin q, ∑ v : Fin m → Bool, if hit r c = v then F v else 0 := by simp
      _ = ∑ v : Fin m → Bool, ∑ c : Fin m → Fin q, if hit r c = v then F v else 0 := sum_comm
      _ = _ := by
        unfold exceedance
        rw [mul_sum]
        refine sum_congr rfl fun v _ => ?_
        rw [← sum_filter, sum_const, nsmul_eq_mul, hit_count]
        dsimp only [F]
        split
        · rw [mul_one, Nat.cast_pow, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]
          exact (scale_mass hq v).symm
        · simp
  have H : (q:ℝ)^m * 1 ≤ (q:ℝ)^m * (exceedance w p * q) := calc
    _ = ∑ _c : Fin m → Fin q, (1:ℝ) := by simp
    _ ≤ ∑ c : Fin m → Fin q, ∑ r, F (hit r c) := sum_le_sum fun c _ => wins c
    _ = ∑ r, ∑ c : Fin m → Fin q, F (hit r c) := sum_comm
    _ = _ := by simp_rw [marginal]; simp [nsmul_eq_mul]; ring
  exact (div_le_iff₀ hq').mpr (le_of_mul_le_mul_left H (pow_pos hq' m))

end
end ManickamMiklosSinghi
namespace ManickamMiklosSinghi.Bernoulli
noncomputable section
open Finset
abbrev Cube (n : ℕ) := Fin n → Bool
def mass {n} (p : ℝ) (v : Cube n) := ∏ i, if v i = true then p else 1-p
def E {n} (p : ℝ) (f : Cube n → ℝ) := ∑ v, mass p v * f v
def ind (P : Prop) [Decidable P] : ℝ := if P then 1 else 0
theorem ind_bounds (P : Prop) [Decidable P] : 0 ≤ ind P ∧ ind P ≤ 1 := by
  by_cases h : P <;> simp [ind,h]
theorem mass_nn {n} {p : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1) (v : Cube n) : 0 ≤ mass p v := by
  apply prod_nonneg
  intro i _
  split <;> linarith
theorem E_congr {n} (p : ℝ) {f g : Cube n → ℝ} (h : ∀ v, f v = g v) : E p f = E p g :=
  congrArg (E p) (funext h)
theorem E_mono {n} {p : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1) {f g : Cube n → ℝ}
    (h : ∀ v, f v ≤ g v) : E p f ≤ E p g :=
  sum_le_sum fun v _ => mul_le_mul_of_nonneg_left (h v) (mass_nn hp hq v)
theorem E_add {n} (p : ℝ) (f g : Cube n → ℝ) :
    E p (fun v => f v + g v) = E p f + E p g := by simp [E,mul_add,sum_add_distrib]
theorem E_sub {n} (p : ℝ) (f g : Cube n → ℝ) :
    E p (fun v => f v - g v) = E p f - E p g := by simp [E,mul_sub,sum_sub_distrib]
theorem E_mul {n} (p a : ℝ) (f : Cube n → ℝ) :
    E p (fun v => a * f v) = a * E p f := by
  simp only [E, mul_sum]
  exact sum_congr rfl fun _ _ => by ring
theorem E_const {n} (p a : ℝ) : E p (fun _ : Cube n => a) = a := by
  unfold E mass
  rw [← sum_mul, ← Fintype.prod_sum (fun (_ : Fin n) (b : Bool) => if b = true then p else 1-p)]
  simp
theorem E_nn {n} {p : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1) {f : Cube n → ℝ}
    (h : ∀ v, 0 ≤ f v) : 0 ≤ E p f := sum_nonneg fun v _ => mul_nonneg (mass_nn hp hq v) (h v)
theorem E_ind_bounds {n} {p : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1) (P : Cube n → Prop)
    [DecidablePred P] : 0 ≤ E p (fun v => ind (P v)) ∧ E p (fun v => ind (P v)) ≤ 1 :=
  ⟨E_nn hp hq (fun _ => (ind_bounds _).1),
   (E_mono hp hq (fun v => (ind_bounds (P v)).2)).trans_eq (E_const _ _)⟩
theorem E_sum {n} {ι : Type*} (p : ℝ) (s : Finset ι) (f : ι → Cube n → ℝ) :
    E p (fun v => ∑ i ∈ s, f i v) = ∑ i ∈ s, E p (f i) := by
  simp only [E, mul_sum]
  exact sum_comm
theorem E_zero_cube (p : ℝ) (f : Cube 0 → ℝ) : E p f = f Fin.elim0 := by
  have h v : v = (Fin.elim0 : Cube 0) := funext (fun i => i.elim0)
  simpa only [E_const] using (E_congr p (fun v => congrArg f (h v)))
theorem E_succ {n} (p : ℝ) (f : Cube (n+1) → ℝ) :
    E p f = E p (fun v : Cube n => (1-p)*f (Fin.cons false v) + p*f (Fin.cons true v)) := by
  classical
  let e := Fin.consEquiv (fun _ : Fin (n+1) => Bool)
  have h (z : Bool × Cube n) : e z = Fin.cons z.1 z.2 := rfl
  unfold E
  rw [← Equiv.sum_comp e (fun v => mass p v * f v), Fintype.sum_prod_type]
  simp only [h, mass, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [Fintype.sum_bool, ← sum_add_distrib]
  exact sum_congr rfl fun v _ => by simp; ring
theorem E_cs {n} {p : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1) (f g : Cube n → ℝ) :
    (E p (fun v => f v * g v))^2 ≤ E p (fun v => (f v)^2) * E p (fun v => (g v)^2) := by
  let F v := Real.sqrt (mass p v) * f v
  let G v := Real.sqrt (mass p v) * g v
  have hfg : E p (fun v => f v*g v) = ∑ v, F v * G v := by
    apply sum_congr rfl; intro v _
    dsimp only [F,G]
    rw [show √(mass p v) * f v * (√(mass p v) * g v) = (√(mass p v))^2 * (f v * g v) by ring, Real.sq_sqrt (mass_nn hp hq v)]
  have hs (u : Cube n → ℝ) : E p (fun v => (u v)^2) =
      ∑ v, (Real.sqrt (mass p v) * u v)^2 := by
    apply sum_congr rfl; intro v _
    rw [mul_pow, Real.sq_sqrt (mass_nn hp hq v)]
  rw [hfg, hs, hs]
  exact sum_mul_sq_le_sq_mul_sq univ F G
theorem variance {n} (p : ℝ) (f : Cube n → ℝ) (a : ℝ) :
    E p (fun v => (f v-a)^2) = E p (fun v => (f v)^2) - 2*a*E p f + a^2 := by
  calc
    _ = E p (fun v => ((f v)^2 - (2*a)*f v) + a^2) := E_congr p (fun _ => by ring)
    _ = _ := by rw [E_add,E_sub,E_mul,E_const]
theorem ind_sq {n} (p : ℝ) (P : Cube n → Prop) [DecidablePred P] :
    E p (fun v => ind (P v)^2) = E p (fun v => ind (P v)) := by
  apply E_congr; intro v; by_cases h : P v <;> simp [ind,h]

def atom (b : Bool) : ℝ := if b = true then 1 else 0
def Z {n} (w : Fin n → ℝ) (p : ℝ) (v : Cube n) := ∑ i, w i * (atom (v i) - p)
def W {n} (w : Fin n → ℝ) (j : ℕ) := ∑ i, (w i)^j
theorem Z_cons {n} (w : Fin (n+1) → ℝ) (p : ℝ) (b : Bool) (v : Cube n) :
    Z w p (Fin.cons b v) = w 0 * (atom b-p) + Z (fun i => w i.succ) p v := by
  simp only [Z,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
theorem W_succ {n} (w : Fin (n+1) → ℝ) (j : ℕ) :
    W w j = (w 0)^j + W (fun i => w i.succ) j := Fin.sum_univ_succ _
theorem moments {n} (w : Fin n → ℝ) (p : ℝ) :
    E p (Z w p) = 0 ∧ E p (fun v => (Z w p v)^2) = p*(1-p)*W w 2 ∧
    E p (fun v => (Z w p v)^4) =
      3*(p*(1-p)*W w 2)^2 + (p*(1-p)*(1-6*(p*(1-p))))*W w 4 := by
  induction n with
  | zero => simp [E_zero_cube, Z,W]
  | succ n ih =>
    let u := fun i : Fin n => w i.succ
    let y := Z u p
    let a := w 0
    let d := p*(1-p)
    obtain ⟨h1,h2,h4⟩ := ih u
    change E p y = 0 at h1
    change E p (fun v => (y v)^2) = d*W u 2 at h2
    change E p (fun v => (y v)^4) = 3*(d*W u 2)^2 + (d*(1-6*d))*W u 4 at h4
    have splitZ (j : ℕ) : E p (fun v => (Z w p v)^j) =
      E p (fun v => (1-p)*(y v-p*a)^j + p*(y v+(1-p)*a)^j) := by
      rw [E_succ]
      apply E_congr; intro v
      simp only [Z_cons,atom,Bool.false_eq_true,ite_false,ite_true,zero_sub]
      dsimp only [y,u,a]
      ring
    constructor
    · calc
        _ = E p (fun v => (Z w p v)^1) := by simp
        _ = E p y := (splitZ 1).trans (E_congr _ fun _ => by ring)
        _ = _ := h1
    constructor
    · rw [splitZ, W_succ w]
      calc
        _ = E p (fun v => (y v)^2 + d*a^2) := E_congr _ (fun _ => by dsimp only [d]; ring)
        _ = _ := by rw [E_add, E_const, h2]; dsimp only [d,u,a]; ring
    · rw [splitZ,W_succ w 2,W_succ w 4]
      calc
        _ = E p (fun v => ((y v)^4 + (6*d*a^2)*(y v)^2) +
              (4*d*(1-2*p)*a^3)*y v + d*(1-3*d)*a^4) :=
          E_congr _ (fun _ => by dsimp only [d]; ring)
        _ = _ := by rw [E_add,E_add,E_add,E_mul,E_mul,E_const,h1,h2,h4]; dsimp only [d,u,a]; ring

/-- A quartic minorant for the strict sign. The upper-side sum of squares is
(x²-15b²/8)² + (3/4)b²(x-4b/3)². -/
theorem quartic_sign (x b : ℝ) (hb : 0 ≤ b) :
    (3*b^2)*x^2 + (2*b^3)*x ≤ x^4 + ((931/192)*b^4)*ind (0 < x) := by
  by_cases hx : 0 < x
  · rw [ind, ite_eq_left hx]
    nlinarith only [sq_nonneg (x^2-15*b^2/8),
      mul_nonneg (sq_nonneg b) (sq_nonneg (x-4*b/3))]
  · rw [ind, ite_eq_right hx]
    have h := mul_nonneg (mul_nonneg (neg_nonneg.mpr (le_of_not_gt hx))
      (show 0 ≤ 2*b-x by linarith)) (sq_nonneg (x+b))
    nlinarith only [h]

theorem positive_moment_bound {n} {p : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1)
    (y : Cube n → ℝ) (hm : E p y = 0) (hv : 0 < E p (fun v => (y v)^2)) :
    (23/50) * (E p (fun v => (y v)^2))^2 <
      E p (fun v => ind (0 < y v)) * E p (fun v => (y v)^4) := by
  let V := E p (fun v => (y v)^2)
  let K := E p (fun v => (y v)^4)
  let P := E p (fun v => ind (0 < y v))
  change 0 < V at hv
  change (23/50)*V^2 < P*K
  have hcs := E_cs hp hq (fun v => (y v)^2) (fun _ => 1)
  have hk : 0 < K := by
    simp only [mul_one, one_pow, E_const] at hcs
    change V^2 ≤ E p (fun v => ((y v)^2)^2) at hcs
    have he : E p (fun v => ((y v)^2)^2) = K := E_congr _ fun _ => by ring
    rw [he] at hcs
    exact (sq_pos_of_pos hv).trans_le hcs
  let b := Real.sqrt (2*K/(3*V))
  have hb : b^2 = 2*K/(3*V) := Real.sq_sqrt (by positivity)
  have h := E_mono hp hq (fun v => quartic_sign (y v) b (Real.sqrt_nonneg _))
  rw [E_add,E_mul,E_mul,hm,E_add,E_mul] at h
  change 3*b^2*V + 2*b^3*0 ≤ K + (931/192*b^4)*P at h
  rw [show b^4 = (b^2)^2 by ring, hb] at h
  field_simp at h
  by_contra! hn
  have h' := mul_le_mul_of_nonneg_right hn hk.le
  nlinarith only [h, h', mul_pos (sq_pos_of_pos hv) hk]

end
end ManickamMiklosSinghi.Bernoulli

namespace ManickamMiklosSinghi.Bernoulli
noncomputable section
open Finset
def mask {n} (a c : Cube n) : Cube n := fun i => !(a i) && c i
def T {n} (r : ℝ) (f : Cube n → ℝ) (a : Cube n) :=
  E r (fun c => f (mask a c))
def bar {n} (p : ℝ) (f : Cube (n+1) → ℝ) (v : Cube n) :=
  (1-p)*f (Fin.cons false v) + p*f (Fin.cons true v)
def delta {n} (f : Cube (n+1) → ℝ) (v : Cube n) :=
  f (Fin.cons true v) - f (Fin.cons false v)
theorem mask_cons {n} (a c : Cube n) (b d : Bool) :
    mask (Fin.cons b a) (Fin.cons d c) = Fin.cons ((!b) && d) (mask a c) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [mask]
theorem T_cons {n} (r : ℝ) (f : Cube (n+1) → ℝ) (a : Cube n) (b : Bool) :
    T r f (Fin.cons b a) = (1-r)*T r (fun v => f (Fin.cons false v)) a +
      r*T r (fun v => f (Fin.cons (!b) v)) a := by
  unfold T
  rw [E_succ]
  simp only [mask_cons,Bool.and_false,Bool.and_true,E_add,E_mul]
theorem delta_T {n} (r : ℝ) (f : Cube (n+1) → ℝ) (a : Cube n) :
    delta (T r f) a = -r*T r (delta f) a := by
  unfold delta
  simp only [T_cons,Bool.not_true,Bool.not_false]
  unfold T
  rw [E_sub]
  ring
theorem bar_T {n} {p r : ℝ} (h : (1-p)*r=p) (f : Cube (n+1) → ℝ) :
    bar p (T r f) = T r (bar p f) := by
  funext a
  unfold bar
  simp only [T_cons,Bool.not_true,Bool.not_false]
  unfold T
  rw [E_add,E_mul,E_mul]
  linear_combination
    (E r (fun c => f (Fin.cons true (mask a c))) -
     E r (fun c => f (Fin.cons false (mask a c)))) * h
theorem E_bar {n} (p : ℝ) (f : Cube (n+1) → ℝ) : E p f = E p (bar p f) := E_succ _ _
theorem square_split {n} (p : ℝ) (f : Cube (n+1) → ℝ) :
    E p (fun v => (f v)^2) = E p (fun v => (bar p f v)^2) +
      (p*(1-p))*E p (fun v => (delta f v)^2) := by
  rw [E_succ, ← E_mul, ← E_add]
  exact E_congr _ fun _ => by unfold bar delta; ring
theorem E_T {n} {p r : ℝ} (h : (1-p)*r=p) (f : Cube n → ℝ) : E p (T r f) = E p f := by
  induction n with
  | zero =>
    simp only [E_zero_cube,T]
    exact congrArg f (Subsingleton.elim _ _)
  | succ n ih => rw [E_bar p (T r f), bar_T h, ih, ← E_bar]
theorem E_T_jensen {n} {p r : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hr : 0 ≤ r)
    (hr' : r ≤ 1) (h : (1-p)*r=p) (f : Cube n → ℝ) :
    E p (fun a => (T r f a)^2) ≤ E p (fun v => (f v)^2) := by
  rw [← E_T h (fun v => (f v)^2)]
  apply E_mono hp hp'
  intro a
  simpa only [mul_one,one_pow,E_const,T] using
    E_cs hr hr' (fun c => f (mask a c)) (fun _ => 1)
/-- Maximal correlation tensorizes. Decompose each coordinate into its
mean and contrast. The contrast picks up exactly a factor -r. -/
theorem noise_sq {n} {p r : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hr : 0 ≤ r)
    (hr' : r ≤ 1) (h : (1-p)*r=p) (f : Cube n → ℝ) :
    E p (fun a => (T r f a)^2) ≤ r^2*E p (fun v => (f v)^2) + (1-r^2)*(E p f)^2 := by
  induction n with
  | zero =>
    have he : ∀ v : Cube 0, v=Fin.elim0 := fun _ => Subsingleton.elim _ _
    simp only [E_zero_cube,T,he (mask _ _)]
    exact le_of_eq (by ring)
  | succ n ih =>
    have hd := E_T_jensen hp hp' hr hr' h (delta f)
    have hc : 0 ≤ p*(1-p)*r^2 := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) (sq_nonneg r)
    calc
      _ = E p (fun a => (T r (bar p f) a)^2) +
            (p*(1-p)*r^2)*E p (fun a => (T r (delta f) a)^2) := by
        rw [square_split p (T r f), bar_T h]
        simp_rw [delta_T, mul_pow, neg_sq, E_mul]
        ring
      _ ≤ (r^2*E p (fun v => (bar p f v)^2) + (1-r^2)*(E p (bar p f))^2) +
            (p*(1-p)*r^2)*E p (fun v => (delta f v)^2) :=
        add_le_add (ih (bar p f)) (mul_le_mul_of_nonneg_left hd hc)
      _ = _ := by rw [square_split p f, E_bar p f]; ring

theorem covariance {n} {p r : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (hr : 0 ≤ r)
    (hr' : r ≤ 1) (h : (1-p)*r=p) (P Q : Cube n → Prop) [DecidablePred P] [DecidablePred Q] :
    let f := fun v => ind (P v)
    let g := fun v => ind (Q v)
    let L := E p f
    let H := E p g
    let J := E p (fun a => f a * T r g a)
    (J-L*H)^2 ≤ (L*(1-L)) * (r^2*(H*(1-H))) := by
  intro f g L H J
  have htg : E p (T r g) = H := E_T h _
  have hff : E p (fun v => (f v)^2) = L := ind_sq _ _
  have hgg : E p (fun v => (g v)^2) = H := ind_sq _ _
  have hf := E_ind_bounds hp hp' P
  have hv : 0 ≤ L*(1-L) := mul_nonneg hf.1 (sub_nonneg.mpr hf.2)
  have hn := noise_sq hp hp' hr hr' h g
  rw [hgg] at hn
  have htv : E p (fun a => (T r g a-H)^2) ≤ r^2*(H*(1-H)) := by
    rw [variance,htg]
    change E p (fun a => (T r g a)^2) ≤ r^2*H + (1-r^2)*H^2 at hn
    linarith only [hn]
  have hc := E_cs hp hp' (fun a => f a-L) (fun a => T r g a-H)
  have hx : E p (fun a => (f a-L)*(T r g a-H)) = J-L*H := by
    calc
      _ = E p (fun a => (f a*T r g a - H*f a) - L*T r g a + L*H) :=
        E_congr _ fun _ => by ring
      _ = _ := by rw [E_add,E_sub,E_sub,E_mul,E_mul,E_const,htg]; change J-H*L-L*H+L*H=_; ring
  rw [hx, variance p f L, hff] at hc
  change (J-L*H)^2 ≤ (L-2*L*L+L^2)*_ at hc
  rw [show L-2*L*L+L^2 = L*(1-L) by ring] at hc
  exact hc.trans (mul_le_mul_of_nonneg_left htv hv)
end
end ManickamMiklosSinghi.Bernoulli

namespace ManickamMiklosSinghi.Bernoulli
noncomputable section
open Finset
def win {n} (w : Fin n → ℝ) (p : ℝ) := E p (fun v => ind (0 < Z w p v))
theorem win_div {n} (w : Fin n → ℝ) (p a : ℝ) (ha : 0 < a) :
    win (fun i => w i/a) p = win w p := by
  apply E_congr
  intro v
  have hz : Z (fun i => w i/a) p v = Z w p v/a := by
    simp [Z,div_mul_eq_mul_div,← sum_div]
  simp [hz,ind,div_pos_iff_of_pos_right ha]
theorem win_perm {n} (w : Fin n → ℝ) (p : ℝ) (e : Equiv.Perm (Fin n)) :
    win (fun i => w (e i)) p = win w p := by
  let perm : Equiv.Perm (Cube n) :=
    { toFun := fun v i => v (e i)
      invFun := fun v i => v (e.symm i)
      left_inv := fun _ => funext (fun _ => by simp)
      right_inv := fun _ => funext (fun _ => by simp) }
  have hm v : mass p (perm v) = mass p v := Equiv.prod_comp e (fun i => if v i = true then p else 1-p)
  have hz v : Z (fun i => w (e i)) p (perm v) = Z w p v :=
    Equiv.sum_comp e (fun i => w i * (atom (v i)-p))
  unfold win E
  rw [← Equiv.sum_comp perm (fun v => mass p v * ind (0 < Z (fun i => w (e i)) p v))]
  exact sum_congr rfl fun v _ => by rw [hm,hz]

theorem reduce_peak {n} (w : Fin n → ℝ) (p : ℝ) (hw : ∀ i, 0 ≤ w i)
    (hpos : ∃ i, 0 < w i) :
    ∃ (k : ℕ) (u : Fin k → ℝ) (a : ℝ), 0 < a ∧ (∃ i, w i = a) ∧
      (∀ j, 0 ≤ u j ∧ u j ≤ 1) ∧ win w p = win (Fin.cons 1 u) p ∧
      ∑ i, w i = a*(1+∑ j, u j) := by
  cases n with
  | zero => obtain ⟨i,_⟩ := hpos; exact i.elim0
  | succ n =>
    obtain ⟨i,hi⟩ := hpos
    obtain ⟨j,_,hj⟩ := univ.exists_max_image w ⟨i,mem_univ _⟩
    let a := w j
    have ha : 0 < a := hi.trans_le (hj i (mem_univ _))
    let e := Equiv.swap (0 : Fin (n+1)) j
    let t := fun i => w (e i) / a
    let u : Fin n → ℝ := fun i => t i.succ
    have ht : t = Fin.cons 1 u := by
      funext x
      refine Fin.cases ?_ (fun _ => rfl) x
      simp [t,e,a,ha.ne']
    refine ⟨n,u,a,ha,⟨j,rfl⟩,fun s => ⟨div_nonneg (hw _) ha.le,
      (div_le_one ha).mpr (hj _ (mem_univ _))⟩,?_,?_⟩
    · rw [← ht]
      exact ((win_div (fun b => w (e b)) p a ha).trans (win_perm w p e)).symm
    · have h : (∑ i, t i) = (∑ i, w i)/a := by rw [show t = _ from rfl,← sum_div,Equiv.sum_comp e w]
      rw [ht,Fin.sum_univ_succ] at h
      simp only [Fin.cons_zero,Fin.cons_succ] at h
      linarith only [(eq_div_iff ha.ne').mp h]

theorem win_split {n} (u : Fin n → ℝ) (p : ℝ) :
    win (Fin.cons 1 u) p =
      p*(1-E p (fun v => ind (Z u p v ≤ -(1-p)))) +
      (1-p)*E p (fun v => ind (p < Z u p v)) := by
  unfold win
  rw [E_succ]
  have he (b : Bool) (v : Cube n) :
      Z (Fin.cons 1 u) p (Fin.cons b v) = atom b - p + Z u p v := by
    simp only [Z_cons,Fin.cons_zero,Fin.cons_succ,one_mul]
  have h₀ v : ind (0 < Z (Fin.cons 1 u) p (Fin.cons false v)) = ind (p < Z u p v) := by
    rw [he]; simp only [atom, Bool.false_eq_true,ite_false]; unfold ind
    congr 1; exact propext (by constructor <;> intro h <;> linarith)
  have h₁ v : ind (0 < Z (Fin.cons 1 u) p (Fin.cons true v)) = 1-ind (Z u p v ≤ -(1-p)) := by
    rw [he]
    by_cases h : Z u p v ≤ -(1-p)
    · simp only [atom,ite_true,ind,ite_eq_left h,
        ite_eq_right (show ¬ 0 < 1-p+Z u p v by linarith),sub_self]
    · simp only [atom,ite_true,ind,ite_eq_right h,
        ite_eq_left (show 0 < 1-p+Z u p v by linarith),sub_zero]
  simp_rw [h₀,h₁]
  rw [E_add,E_mul,E_mul,E_sub,E_const]
  ring

/-- The fourth moment suffices whenever the squared mass S is large compared
to the square of each individual weight (here scaled to at most 1). -/
theorem diffuse {n} (w : Fin n → ℝ) {p C M : ℝ} (hp : 0 < p) (hp' : p ≤ 1/6)
    (hw : ∀ i, 0 ≤ w i ∧ w i ≤ 1) (hM : 0 < M) (hS : M ≤ W w 2) (hC : 0 ≤ C)
    (hslope : 0 ≤ 23/50-3*C*p)
    (hbase : C*(1-6*(p*(1-p))) < (23/50-3*C*p)*(1-p)*M) : C*p < win w p := by
  let S := W w 2
  let d := p*(1-p)
  let V := d*S
  let K := E p (fun v => (Z w p v)^4)
  have hq : 0 < 1-p := by linarith
  have hd : 0 < d := mul_pos hp hq
  have hv : 0 < V := mul_pos hd (hM.trans_le hS)
  have hc : 0 ≤ 1-6*d := by dsimp [d]; nlinarith only [hp',sq_nonneg p]
  have hw4 : W w 4 ≤ S := by
    apply sum_le_sum
    intro i _
    obtain ⟨hw₀,hw₁⟩ := hw i
    have hh : (w i)^2 ≤ 1 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hw₁) (by linarith : 0 ≤ 1+w i)]
    nlinarith only [mul_nonneg (sq_nonneg (w i)) (sub_nonneg.mpr hh)]
  obtain ⟨h1,h2,h4⟩ := moments w p
  change E p (fun v => (Z w p v)^2) = V at h2
  change K = 3*V^2 + d*(1-6*d)*W w 4 at h4
  have ht := positive_moment_bound hp.le (by linarith : p≤1) (Z w p) h1 (h2.symm ▸ hv)
  rw [h2] at ht
  change 23/50*V^2 < win w p*K at ht
  have hk : 0 ≤ K := E_nn hp.le (by linarith) fun _ => by positivity
  have hub : K ≤ (3*V+(1-6*d))*V := by
    rw [h4]
    have hh := mul_le_mul_of_nonneg_left hw4 (mul_nonneg hd.le hc)
    dsimp only [V]; nlinarith only [hh]
  have hline : C*(3*V + (1-6*d)) < 23/50*(1-p)*S := by
    have hh := mul_le_mul_of_nonneg_left hS (mul_nonneg hslope hq.le)
    change _ ≤ (23/50-3*C*p)*(1-p)*S at hh
    dsimp only [V,d]
    nlinarith only [hbase,hh]
  by_contra! h
  have hh := (mul_le_mul_of_nonneg_right h hk).trans (mul_le_mul_of_nonneg_left hub (mul_nonneg hC hp.le))
  have h' := mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hline hp) hv
  dsimp only [V,d] at ht hh h'
  linarith only [ht,hh,h']

/-- Cantelli with a fixed shift, for the coarse auxiliary success bound. -/
theorem coarse_heavy {n} (u : Fin n → ℝ) {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1/6)
    (hs : W u 2 ≤ 5/3) : (3/4)*p ≤ win (Fin.cons 1 u) p := by
  let q := 1-p
  let y := Z u p
  let L := E p (fun v => ind (y v ≤ -q))
  let H := E p (fun v => ind (p < y v))
  have hq : 0 < q := by dsimp [q]; linarith
  have hH : 0 ≤ H := E_nn hp.le (by linarith) fun v => (ind_bounds _).1
  have point (x : ℝ) : (16*q^2)*ind (x ≤ -q) ≤ 9*x^2 - (6*q)*x + q^2 := by
    by_cases hx : x ≤ -q
    · rw [ind,ite_eq_left hx]
      nlinarith only [mul_nonneg (by linarith : 0 ≤ -q-x) (by linarith : 0 ≤ 7*q-3*x)]
    · rw [ind,ite_eq_right hx]; nlinarith only [sq_nonneg (3*x-q)]
  have h := E_mono hp.le (by linarith : p ≤ 1) fun v => point (y v)
  rw [E_mul,E_add,E_sub,E_mul,E_mul,E_const] at h
  obtain ⟨h1,h2,_⟩ := moments u p
  change E p y = 0 at h1
  change E p (fun v => (y v)^2) = p*q*W u 2 at h2
  rw [h1,h2] at h
  have hV := mul_le_mul_of_nonneg_left hs (mul_nonneg hp.le hq.le)
  have hs' : 5*p ≤ q := by dsimp [q]; linarith
  have hh : (16*L)*q^2 ≤ 4*q^2 := by
    change 16*q^2*L ≤ _ at h
    nlinarith only [h,hV,mul_le_mul_of_nonneg_right hs' hq.le]
  have hL := le_of_mul_le_mul_right hh (sq_pos_of_pos hq)
  rw [win_split]
  change 3/4*p ≤ p*(1-L)+q*H
  nlinarith only [mul_le_mul_of_nonneg_right hL hp.le,mul_nonneg hq.le hH]

theorem auxiliary {n} (w : Fin n → ℝ) {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1/6)
    (hw : ∀ i, 0 ≤ w i) (hn : ∃ i, 0 < w i) : (3/4)*p ≤ win w p := by
  obtain ⟨k,u,_,_,_,hu,he,_⟩ := reduce_peak w p hw hn
  rw [he]
  by_cases hs : 8/3 ≤ W (Fin.cons 1 u) 2
  · apply le_of_lt (diffuse _ hp hp' ?_ (by norm_num : 0 < (8/3:ℝ)) hs
      (by norm_num : 0 ≤ (3/4:ℝ)) (by linarith) ?_)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp
      · simpa using hu j
    · have hh := mul_le_mul (show (5/6:ℝ) ≤ 1-p by linarith)
          (show (23/50:ℝ)-9/16*(1/6) ≤ 23/50-9/16*p by linarith)
          (by norm_num) (by linarith)
      nlinarith only [hh]
  · apply coarse_heavy _ hp hp'
    rw [W_succ] at hs
    simp only [Fin.cons_zero,Fin.cons_succ,one_pow] at hs
    linarith
end
end ManickamMiklosSinghi.Bernoulli

namespace ManickamMiklosSinghi.Bernoulli
noncomputable section
open Finset
def rest {n} (u : Fin n → ℝ) (a : Cube n) (i : Fin n) := if a i = true then 0 else u i
theorem mask_center {n} (u : Fin n → ℝ) {p r : ℝ} (h : (1-p)*r=p) (a c : Cube n) :
    Z u p (mask a c) = Z (rest u a) r c - r*Z u p a := by
  unfold Z
  rw [mul_sum,← sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  cases ha : a i <;> simp [mask,rest,atom,ha] <;> nlinarith only [congrArg (fun t : ℝ => u i*t) h]
theorem rest_exists {n} (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) {p : ℝ} (hp : p < 1)
    (a : Cube n) (h : Z u p a ≤ -(1-p)) : ∃ i, 0 < rest u a i := by
  by_contra! hh
  have hn : 0 ≤ Z u p a := by
    apply sum_nonneg
    intro i _
    cases hbit : a i
    · have he : u i = 0 := le_antisymm (by simpa [rest,hbit] using hh i) (hu i)
      simp [he]
    · exact mul_nonneg (hu _) (by simp [atom]; linarith)
  linarith

/-- A low-weight first sample forces an auxiliary positive-tail event on
the unselected coordinates of the second sample. -/
theorem coupled_lower {n} (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) {p r : ℝ}
    (hp : 0 ≤ p) (hp' : p < 1) (hr : 0 < r) (hr' : r ≤ 1/6) (h : (1-p)*r=p) :
    let f := fun a => ind (Z u p a ≤ -(1-p))
    let g := fun a => ind (p < Z u p a)
    (3/4*r)*E p f ≤ E p (fun a => f a*T r g a) := by
  intro f g
  rw [← E_mul]
  apply E_mono hp hp'.le
  intro a
  by_cases hl : Z u p a ≤ -(1-p)
  · have hn := rest_exists u hu hp' a hl
    have hnn i : 0 ≤ rest u a i := by unfold rest; split <;> first | exact le_rfl | exact hu i
    have hw := auxiliary (rest u a) hr hr' hnn hn
    have ht : win (rest u a) r ≤ T r g a := by
      apply E_mono hr.le (by linarith)
      intro c
      by_cases hc : 0 < Z (rest u a) r c
      · have hh : p < Z u p (mask a c) := by
          rw [mask_center u h]
          nlinarith only [mul_le_mul_of_nonneg_left hl hr.le,h,hc]
        simp [ind,hc,g,hh]
      · simpa only [g,ind,ite_eq_right hc] using (ind_bounds (p < Z u p (mask a c))).1
    simpa only [f,ind,ite_eq_left hl,mul_one,one_mul] using hw.trans ht
  · simp only [f,ind,ite_eq_right hl,mul_zero,zero_mul,le_refl]

theorem no_deficit {n} (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) {p r : ℝ}
    (hp : 0 < p) (hp' : p ≤ 1/7) (hr : 0 < r) (hr' : r ≤ 1/6)
    (h : (1-p)*r=p) (hs : W u 2 ≤ 9) :
    let L := E p (fun a => ind (Z u p a ≤ -(1-p)))
    let H := E p (fun a => ind (p < Z u p a))
    0 < L → r*L < H := by
  intro L H hL
  by_contra! hHL
  let f := fun a => ind (Z u p a ≤ -(1-p))
  let g := fun a => ind (p < Z u p a)
  let J := E p (fun a => f a*T r g a)
  have hp1 : p ≤ 1 := by linarith
  have hH0 := (E_ind_bounds hp.le hp1 (fun a => p < Z u p a)).1
  change 0 ≤ H at hH0
  have hlo := coupled_lower u hu hp.le (by linarith) hr hr' h
  change (3/4*r)*L ≤ J at hlo
  have hco := covariance hp.le hp1 hr.le (by linarith) h
    (fun a => Z u p a ≤ -(1-p)) (fun a => p < Z u p a)
  change (J-L*H)^2 ≤ L*(1-L)*(r^2*(H*(1-H))) at hco
  have point (x : ℝ) : (7*ind (x ≤ -(1-p)) + 6*x - 6*p) - 9*ind (p < x) ≤
      (x^2-(2*p)*x)+p^2 := by
    by_cases h₁ : x ≤ -(1-p)
    · rw [ind,ite_eq_left h₁,ind,ite_eq_right (by linarith)]
      nlinarith only [mul_nonneg (by linarith : 0 ≤ -1-(x-p)) (by linarith : 0 ≤ 7-(x-p))]
    · rw [ind,ite_eq_right h₁]
      by_cases h₂ : p < x
      · rw [ind,ite_eq_left h₂]; nlinarith only [sq_nonneg (x-p-3)]
      · rw [ind,ite_eq_right h₂]; nlinarith only [sq_nonneg (x-p), not_lt.mp h₂]
  have hU := E_mono hp.le hp1 (fun a => point (Z u p a))
  simp only [E_add,E_sub,E_mul,E_const] at hU
  obtain ⟨hy,hy₂,_⟩ := moments u p
  rw [hy,hy₂] at hU
  change 7*L+6*0-6*p-9*H ≤ p*(1-p)*W u 2-2*p*0+p^2 at hU
  have hsmall : L < 3/8 := by
    have hv := mul_le_mul_of_nonneg_left hs (mul_nonneg hp.le (sub_nonneg.mpr hp1))
    have hh := mul_le_mul_of_nonneg_right hr' hL.le
    have hc := mul_nonneg (sub_nonneg.mpr hp') (show 0 ≤ 15-8*(1/7+p) by linarith)
    nlinarith only [hv,hU,hHL,hh,hc]
  have hgap : r*L*(3/4-L) ≤ J-L*H := by
    nlinarith only [hlo,mul_le_mul_of_nonneg_left hHL hL.le]
  have hsq := pow_le_pow_left₀
    (mul_nonneg (mul_nonneg hr.le hL.le) (by linarith : 0 ≤ 3/4-L)) hgap 2
  have hh : H*(1-H) ≤ r*L := by nlinarith only [hHL,sq_nonneg H]
  have ht := mul_le_mul_of_nonneg_left hh
    (mul_nonneg (mul_nonneg hL.le (by linarith : 0 ≤ 1-L)) (sq_nonneg r))
  have hc : (r*L)^2 * (3/4-L)^2 ≤ (r*L)^2 * (r*(1-L)) := by
    nlinarith only [hsq,hco,ht]
  have hh' := le_of_mul_le_mul_left hc (sq_pos_of_pos (mul_pos hr hL))
  have h' := mul_le_mul_of_nonneg_right hr' (show 0 ≤ 1-L by linarith)
  nlinarith only [hh',h',mul_nonneg (sub_nonneg.mpr hsmall.le)
    (show 0 ≤ 4/3-3/8-L by linarith)]

theorem win_head {n} (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i ∧ u i ≤ 1)
    {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1/7) :
    p ≤ win (Fin.cons 1 u) p ∧
      (p/(1-p) < ∑ i, u i → p < win (Fin.cons 1 u) p) := by
  let r := p/(1-p)
  have hq : 0 < 1-p := by linarith
  have hr : 0 < r := div_pos hp hq
  have hr' : r ≤ 1/6 := (div_le_iff₀ hq).mpr (by linarith)
  have hb : (1-p)*r = p := mul_div_cancel₀ _ hq.ne'
  by_cases hs : 10 ≤ W (Fin.cons 1 u) 2
  · have ht : (1:ℝ)*p < win (Fin.cons 1 u) p := by
      apply diffuse _ hp (by linarith) ?_ (by norm_num : (0:ℝ)<10) hs (by norm_num) (by linarith) ?_
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simpa using hu j
      · have hh := mul_le_mul (show (6/7:ℝ) ≤ 1-p by linarith)
            (show (23/50:ℝ)-(12/5)*(1/7) ≤ 23/50-(12/5)*p by linarith)
            (by norm_num) (by linarith)
        nlinarith only [hh]
    rw [one_mul] at ht
    exact ⟨ht.le,fun _ => ht⟩
  let L := E p (fun a => ind (Z u p a ≤ -(1-p)))
  let H := E p (fun a => ind (p < Z u p a))
  have hH0 : 0 ≤ H := E_nn hp.le (by linarith) fun _ => (ind_bounds _).1
  have hL0 : 0 ≤ L := E_nn hp.le (by linarith) fun _ => (ind_bounds _).1
  rw [win_split]
  change p ≤ p*(1-L)+(1-p)*H ∧ (_ → p < p*(1-L)+(1-p)*H)
  rcases hL0.eq_or_lt with hl | hl
  · rw [← hl,sub_zero,mul_one]
    refine ⟨le_add_of_nonneg_right (mul_nonneg hq.le hH0),?_⟩
    intro hfull
    have hall : p < Z u p (fun _ => true) := by
      have hz : Z u p (fun _ => true) = (∑ i, u i)*(1-p) := by simp [Z,atom,sum_mul]
      rw [hz]
      exact (div_lt_iff₀ hq).mp hfull
    have hpos : 0 < H := by
      apply sum_pos'
      · intro a _
        exact mul_nonneg (mass_nn hp.le (by linarith) _) (ind_bounds _).1
      · refine ⟨fun _ => true, mem_univ _,?_⟩
        simp only [ind,ite_eq_left hall,mul_one]
        exact prod_pos (fun i _ => by simp [hp])
    linarith only [mul_pos hq hpos]
  · have hw : W u 2 ≤ 9 := by
      rw [W_succ] at hs
      simp only [Fin.cons_zero,Fin.cons_succ,one_pow] at hs
      linarith
    have hh := no_deficit u (fun i => (hu i).1) hp hp' hr hr' hb hw hl
    change r*L < H at hh
    have hhh := mul_lt_mul_of_pos_left hh hq
    rw [← mul_assoc,hb] at hhh
    exact ⟨by linarith,fun _ => by linarith⟩

end
end ManickamMiklosSinghi.Bernoulli

namespace ManickamMiklosSinghi
noncomputable section
open Finset _root_.ManickamMiklosSinghi.Bernoulli

private theorem mass_eq {m} (v : Cube m) (p : ℝ) :
    mass p v = p^(support v).card*(1-p)^(m-(support v).card) := by
  classical
  have h : univ.filter (fun i => ¬ v i = true) = (support v)ᶜ := by ext; simp [support]
  simp only [mass,prod_ite,prod_const,h,card_compl,Fintype.card_fin,support]
private theorem centered_score {m} (w : Fin m → ℝ) (hw : ∑ i, w i = 1) (p : ℝ) (v : Cube m) :
    Z w p v = (∑ i ∈ support v, w i)-p := by
  simp only [Z,mul_sub,sum_sub_distrib,← sum_mul,hw,one_mul]
  simp only [atom,mul_ite,mul_one,mul_zero,support,sum_filter]
private theorem strict_eq_win {m} (w : Fin m → ℝ) (hw : ∑ i, w i = 1) (p : ℝ) :
    strictExceedance w p = win w p := by
  unfold strictExceedance win E
  apply sum_congr rfl
  intro v _
  dsimp only
  rw [mass_eq,centered_score w hw]
  simp [ind,sub_pos,mul_ite]
private theorem le_inclusive {m} (w : Fin m → ℝ) {p : ℝ} (hp : 0 ≤ p) (hq : p ≤ 1) :
    strictExceedance w p ≤ exceedance w p := by
  apply sum_le_sum
  intro v _
  split_ifs with ht hl
  · rfl
  · exact (hl ht.le).elim
  · positivity
  · rfl
private theorem positive_site {m} (w : Fin m → ℝ) (h : ∑ i, w i = 1) : ∃ i, 0 < w i := by
  by_contra! hh
  have hz := sum_nonpos (s := univ) (fun i _ => hh i)
  linarith

/-- The inclusive Milojević–Sudakov inequality on the whole real interval
[0,1/7], for the explicitly defined Bernoulli product measure. -/
theorem bernoulli_exceedance_one_seventh {m : ℕ} (w : Fin m → ℝ) {p : ℝ}
    (hp : 0 ≤ p) (hp' : p ≤ 1/7) (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1) :
    p ≤ exceedance w p := by
  rcases hp.eq_or_lt with h | h
  · subst p
    apply sum_nonneg
    intro v _
    split <;> positivity
  · obtain ⟨_,u,_,_,_,hu,he,_⟩ := reduce_peak w p (fun i => (hw i).le) (positive_site w hs)
    apply le_trans _ (le_inclusive w h.le (by linarith))
    rw [strict_eq_win w hs,he]
    exact (win_head u hu h hp').1

/-- Strict surplus, for strict exceedance, if no coordinate exceeds the bias. -/
theorem bernoulli_strict_exceedance_one_seventh {m : ℕ} (w : Fin m → ℝ) {p : ℝ}
    (hp : 0 < p) (hp' : p ≤ 1/7) (hw : ∀ i, 0 < w i) (hs : ∑ i, w i = 1)
    (hcap : ∀ i, w i ≤ p) : p < strictExceedance w p := by
  obtain ⟨_,u,a,ha,⟨i,hi⟩,hu,he,hSum⟩ :=
    reduce_peak w p (fun i => (hw i).le) (positive_site w hs)
  rw [strict_eq_win w hs,he]
  apply (win_head u hu hp hp').2
  have hr : p/(1-p) ≤ 1/6 := (div_le_iff₀ (by linarith : 0 < 1-p)).mpr (by linarith)
  by_contra! hh
  have hU := mul_le_mul_of_nonneg_left (add_le_add_left (hh.trans hr) 1) ha.le
  rw [hs] at hSum
  linarith only [hSum,hU,hi,hcap i,hp']

end
end ManickamMiklosSinghi
