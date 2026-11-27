import Conjectures.NabergallChordalDiagrams.Factors
import Mathlib.Data.Finset.NatAntidiagonal

/-! # Counting the unique decompositions

For a fixed pair of lengths, first forget the child weights in a tagged
production. Restriction and gluing identify this data with a parent marked
at its canonical split. Finally forget the mark: the earliest gap is unique.
The two rules differ only in the permitted link counts and in which parents
have a mark.
-/

namespace NabergallChordalDiagrams
namespace Counting

noncomputable section
open scoped Classical

inductive Rule where
  | sequence
  | linked

def Rule.allowed : Rule → ℕ → ℕ → Prop
  | .sequence,t,_ => t=0
  | .linked,t,j => 0<t ∧ t<j

def Rule.parent {n} : Rule → Fragment n → Prop
  | .sequence,F => ¬ F.Irreducible
  | .linked,F => F.Irreducible ∧ 2≤n

def Rule.selected {n} : Rule → Fragment n → ℕ → Prop
  | .sequence,F,g => FirstFree F g
  | .linked,F,g => Earliest F g

abbrev Target (m : Rule) (n k : ℕ) := {F : ValidFragment n k // m.parent F.val}

abbrev Marked (m : Rule) (n k g : ℕ) := {F : Target m n k //
  0<g ∧ g<n ∧ m.selected F.val.val g}

structure Regular (m : Rule) {l r} (k : ℕ) (A : Fragment l) (B : Fragment r) (t : ℕ) : Prop where
  va : A.Valid
  vb : B.Valid
  pa : 0<A.weight
  pb : 0<B.weight
  irr : A.Irreducible
  rule : m.allowed t B.weight
  weight : A.weight+B.weight-2*t=k

abbrev Data (m : Rule) (l r k : ℕ) := {S : Assembly l r // Regular m k S.left S.right S.t}

private structure MarkProp (m : Rule) {l r} (k : ℕ) (F : Fragment (l+r)) : Prop where
  valid : F.Valid
  weight : F.weight=k
  pos : 0<k
  parent : m.parent F
  lp : 0<l
  rp : 0<r
  selected : m.selected F l

private theorem selected_admissible {m : Rule} {n g : ℕ} {F : Fragment n} (h : m.selected F g) : Admissible F g := by
  cases m with
  | sequence => exact admissible_of_free _ h.1
  | linked => exact h.1

private theorem regular_iff {l r k t m} {A : Fragment l} {B : Fragment r} (P : LinkPlan A B t) :
    Regular m k A B t ↔ MarkProp m k P.glue := by
  constructor
  · intro reg
    have va := P.valid reg.va reg.vb reg.pa reg.pb
    have wt := P.weight_glue.trans reg.weight
    have hl : 0<l := lt_of_lt_of_le reg.pa A.weight_le
    have hr : 0<r := lt_of_lt_of_le reg.pb B.weight_le
    have lt := P.le_left
    cases m with
    | sequence =>
      have z : t=0 := reg.rule
      have free := P.firstFree_iff.mpr ⟨z,reg.irr⟩
      have pos : 0<k := by have := reg.weight; have := reg.pa; omega
      exact ⟨va,wt,pos,fun h => free.1 (h l hl (by omega)),hl,hr,free⟩
    | linked =>
      obtain ⟨tpos,lim⟩ := reg.rule
      have pos : 0<k := by have := reg.weight; omega
      have pp : 0<P.glue.weight := wt.symm ▸ pos
      exact ⟨va,wt,pos,⟨(P.irreducible_iff va pp hl hr).mpr tpos, by omega⟩,hl,hr,
        (P.earliest_iff tpos pp reg.va).mpr ⟨reg.irr,lim⟩⟩
  · intro mp
    obtain ⟨hg,hg'⟩ := (admissible_iff_good P.glue).mp P.admissible
    have pp : 0<P.glue.weight := mp.weight.symm ▸ mp.pos
    have lp : 0<A.weight := by
      simpa only [P.restrict_left] using
        (leftWindow l r).restrict_weight_pos P.glue mp.lp mp.valid.1 pp
    have rp : 0<B.weight := by
      simpa only [P.restrict_right] using
        (rightWindow l r).restrict_weight_pos P.glue mp.rp mp.valid.1 pp
    have va : A.Valid := by
      simpa only [P.restrict_left] using
        (leftWindow l r).restrict_valid P.glue mp.lp pp mp.valid hg
    have vb : B.Valid := by
      simpa only [P.restrict_right] using
        (rightWindow l r).restrict_valid P.glue mp.rp pp mp.valid hg'
    have wt := P.weight_glue.symm.trans mp.weight
    cases m with
    | sequence =>
      have ⟨hz,hi⟩ := P.firstFree_iff.mp mp.selected
      exact ⟨va,vb,lp,rp,hi,hz,wt⟩
    | linked =>
      have tpos := (P.irreducible_iff mp.valid pp mp.lp mp.rp).mp mp.parent.1
      have ⟨hi,ht⟩ := (P.earliest_iff tpos pp va).mp mp.selected
      exact ⟨va,vb,lp,rp,hi,⟨tpos,ht⟩,wt⟩

private theorem toMarkProp {m l r k} (x : Marked m (l+r) k l) : MarkProp m k x.val.val.val :=
  ⟨x.val.val.property.1,x.val.val.property.2.1,x.val.val.property.2.2,x.val.property,
   x.property.1,by have := x.property.2.1; omega,x.property.2.2⟩

private def markOf {m l r k} {F : Fragment (l+r)} (h : MarkProp m k F) : Marked m (l+r) k l :=
  ⟨⟨⟨F,h.valid,h.weight,h.pos⟩,h.parent⟩,h.lp,by have := h.rp; omega,h.selected⟩

private def specified (m : Rule) (l r k : ℕ) : Marked m (l+r) k l ≃ Data m l r k where
  toFun x :=
    let f := x.val.val.val
    let z : {F : Fragment (l+r) // Admissible F l} := ⟨f,selected_admissible x.property.2.2⟩
    let S := (assemblyEquiv l r) z
    have e : S.glue=f := congrArg Subtype.val ((assemblyEquiv l r).left_inv z)
    ⟨S,(regular_iff S.plan).mpr (show MarkProp m k S.glue by rw [e]; exact toMarkProp x)⟩
  invFun S := markOf ((regular_iff S.val.plan).mp S.property)
  left_inv x := Subtype.ext (Subtype.ext (Subtype.ext (congrArg (fun z : {F : Fragment (l+r) // Admissible F l} => z.val)
    ((assemblyEquiv l r).left_inv ⟨_,selected_admissible x.property.2.2⟩))))
  right_inv S := Subtype.ext ((assemblyEquiv l r).right_inv S.val)

private theorem unique_gap {m : Rule} {n : ℕ} {F : Fragment n} {i j : ℕ} (hi : 0 < i) (hj : 0 < j)
    (si : m.selected F i) (sj : m.selected F j) : i=j := by
  rcases lt_trichotomy i j with h|h|h
  · cases m with
    | sequence => exact (si.1 (sj.2 i hi h)).elim
    | linked => exact (sj.2 i hi h si.1).elim
  · exact h
  · cases m with
    | sequence => exact (sj.1 (si.2 j hj h)).elim
    | linked => exact (si.2 j hj h sj.1).elim

private def forgetMarks (m : Rule) (n k : ℕ) :
    (Σ ab : ↥(Finset.antidiagonal n), Marked m n k ab.val.1) ≃ Target m n k :=
  Equiv.ofBijective (fun Z => Z.2.val) (by
    constructor
    · rintro ⟨⟨⟨a,b⟩,hab⟩,⟨F,hF⟩⟩ ⟨⟨⟨c,d⟩,hcd⟩,⟨J,hJ⟩⟩ e
      change F=J at e
      subst J
      have e₁ : a=c := unique_gap hF.1 hJ.1 hF.2.2 hJ.2.2
      have ab : a+b=n := Finset.mem_antidiagonal.mp hab
      have cd : c+d=n := Finset.mem_antidiagonal.mp hcd
      have e₂ : b=d := by omega
      subst c d; rfl
    · intro F
      have ex : ∃ g, 0<g ∧ g<n ∧ m.selected F.val.val g := by
        cases m with
        | sequence => exact exists_firstFree F.property
        | linked => exact exists_earliest F.val.property.1 F.property.2
      obtain ⟨g,hp,hn,h⟩ := ex
      exact ⟨⟨⟨(g,n-g),Finset.mem_antidiagonal.mpr (by change g+(n-g)=n; omega)⟩,⟨F,hp,hn,h⟩⟩,rfl⟩)

abbrev Choice (m : Rule) (i j k : ℕ) :=
  {t : Fin (min i j + 1) // m.allowed t.val j ∧ i+j-2*t.val=k}

abbrev Terms (m : Rule) (l r k : ℕ) :=
  Σ i : Fin l, Σ j : Fin r,
    IrreducibleFragment l (i.val+1) × ValidFragment r (j.val+1) × Choice m (i.val+1) (j.val+1) k

private def forgetWeights {m l r k} (z : Terms m l r k) : Data m l r k := by
  obtain ⟨i,j,A,B,t⟩ := z
  have wa := A.val.property.2.1
  have wb := B.property.2.1
  have bnd := t.val.isLt
  refine ⟨⟨A.val.val,B.val,t.val.val,by omega,by omega⟩,?_,?_,?_,?_,?_,?_,?_⟩
  · exact A.val.property.1
  · exact B.property.1
  · exact lt_of_lt_of_le (Nat.succ_pos _) wa.ge
  · exact lt_of_lt_of_le (Nat.succ_pos _) wb.ge
  · exact A.property
  · simpa only [wb] using t.property.1
  · simpa only [wa,wb] using t.property.2

private def weightEquiv (m : Rule) (l r k : ℕ) : Terms m l r k ≃ Data m l r k :=
  Equiv.ofBijective forgetWeights (by
    constructor
    · rintro ⟨i,j,A,B,t⟩ ⟨i',j',A',B',t'⟩ e
      have hl : A.val.val = A'.val.val := congrArg (fun z => z.val.left) e
      have hr : B.val = B'.val := congrArg (fun z => z.val.right) e
      have ht : t.val.val = t'.val.val := congrArg (fun z => z.val.t) e
      have ei : i=i' := Fin.ext (by
        have := A.val.property.2.1.symm.trans ((congrArg Fragment.weight hl).trans A'.val.property.2.1); omega)
      have ej : j=j' := Fin.ext (by
        have := B.property.2.1.symm.trans ((congrArg Fragment.weight hr).trans B'.property.2.1); omega)
      subst i' j'
      have eA : A=A' := Subtype.ext (Subtype.ext hl)
      have eB : B=B' := Subtype.ext hr
      have et : t=t' := Subtype.ext (Fin.ext ht)
      subst A' B' t'; rfl
    · rintro ⟨S,reg⟩
      let i : Fin l := ⟨S.left.weight-1,by have := S.left.weight_le; have := reg.pa; omega⟩
      let j : Fin r := ⟨S.right.weight-1,by have := S.right.weight_le; have := reg.pb; omega⟩
      have ei : S.left.weight=i.val+1 := by change _ = _-1+1; have := reg.pa; omega
      have ej : S.right.weight=j.val+1 := by change _ = _-1+1; have := reg.pb; omega
      let A : IrreducibleFragment l (i.val+1) := ⟨⟨S.left,reg.va,ei,Nat.succ_pos _⟩,reg.irr⟩
      let B : ValidFragment r (j.val+1) := ⟨S.right,reg.vb,ej,Nat.succ_pos _⟩
      let t : Choice m (i.val+1) (j.val+1) k := ⟨⟨S.t,by have := S.le_left; have := S.le_right; omega⟩,
        ej ▸ reg.rule,by change (i.val+1)+(j.val+1)-2*S.t=k; rw [← ei,← ej]; exact reg.weight⟩
      exact ⟨⟨i,j,A,B,t⟩,Subtype.ext (Assembly.ext rfl rfl rfl)⟩)

/-- The nontrivial parents are counted by length split, positive weights
of the two children, the children themselves, and a legal link count. -/
def decomposition (m : Rule) (n k : ℕ) :
    Target m n k ≃ (Σ ab : ↥(Finset.antidiagonal n), Terms m ab.val.1 ab.val.2 k) :=
  (forgetMarks m n k).symm.trans (Equiv.sigmaCongrRight (by
    rintro ⟨⟨l,r⟩,hab⟩
    have e : l+r=n := Finset.mem_antidiagonal.mp hab
    subst n
    exact (specified m l r k).trans (weightEquiv m l r k).symm))

end
end Counting
end NabergallChordalDiagrams
