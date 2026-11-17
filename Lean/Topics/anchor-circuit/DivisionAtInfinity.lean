import BoundedTest

namespace AnchorCircuit.Division
open Lean.Grind StructuralReduction

variable {K : Type} [Field K] (v : Place K)

private theorem prod_ne {a b : K} (ha : a≠0) (hb : b≠0) : a*b≠0 :=
  fun z => (Field.of_mul_eq_zero z).elim ha hb

private theorem add_depth {n : Int} {a b : K} (ha : deep v n a) (hb : deep v n b) :
    deep v n (a+b) := by
  rcases ha with e|h
  · simpa only [e,AddCommMonoid.zero_add] using hb
  rcases hb with e|k
  · rw [e,AddCommMonoid.add_zero]; exact Or.inr h
  by_cases za : a=0
  · rw [za,AddCommMonoid.zero_add]; exact Or.inr k
  by_cases zb : b=0
  · rw [zb,AddCommMonoid.add_zero]; exact Or.inr h
  by_cases z : a+b=0
  · exact Or.inl z
  · have bound := v.add za zb z
    exact Or.inr (by omega)

private theorem mul_depth {i j : Int} {a b : K} (ha : deep v i a) (hb : deep v j b) :
    deep v (i+j) (a*b) := by
  by_cases za : a=0
  · exact Or.inl (by rw [za,Semiring.zero_mul])
  by_cases zb : b=0
  · exact Or.inl (by rw [zb,Semiring.mul_zero])
  have aa := ha.resolve_left za
  have bb := hb.resolve_left zb
  exact Or.inr (by rw [v.mul za zb]; omega)

private theorem neg_depth {n : Int} {a : K} (ha : deep v n a) : deep v n (-a) := by
  by_cases z : a=0
  · exact Or.inl (by rw [z,AddCommGroup.neg_zero])
  have nz : -a≠0 := fun e => z (by grobner)
  have eq : (-a)*(-a)=a*a := by grobner
  have ord := congrArg v.v eq
  rw [v.mul nz nz,v.mul z z] at ord
  have := ha.resolve_left z
  exact Or.inr (by omega)

private theorem weaken {i j : Int} {a : K} (h : i≤j) (ha : deep v j a) : deep v i a :=
  ha.imp_right (fun t=>Int.le_trans h t)

private theorem div_order {a b : K} (ha : a≠0) (hb : b≠0) :
    a/b≠0 ∧ v.v (a/b)=v.v a-v.v b := by
  have eq : (a/b)*b=a := Field.div_mul_cancel hb
  have nz : a/b≠0 := fun e=>ha (by rw [←eq,e,Semiring.zero_mul])
  have ord := congrArg v.v eq
  rw [v.mul nz hb] at ord
  exact ⟨nz,by omega⟩

private theorem one_plus {a : K} (h : deep v 1 a) :
    1+a≠0 ∧ v.v (1+a)=0 := by
  have one_ne : (1:K)≠0 := Ne.symm Field.zero_ne_one
  by_cases za : a=0
  · simpa only [za,AddCommMonoid.add_zero] using And.intro one_ne v.one
  have high := h.resolve_left za
  have result := v.unequal one_ne za (by rw [v.one]; omega)
  rw [v.one,Int.min_eq_left (by omega)] at result
  exact result

/-- A unit congruent to one, including its precise residue statement. -/
def principal (a : K) : Prop := a≠0 ∧ v.v a=0 ∧ deep v 1 (a-1)

private theorem ratio {a b : K} (ha : deep v 1 a) (hb : deep v 1 b) :
    principal v ((1+b)/(1+a)) := by
  obtain ⟨an,av⟩ := one_plus v ha
  obtain ⟨bn,bv⟩ := one_plus v hb
  obtain ⟨nz,val⟩ := div_order v bn an
  have clear : ((1+b)/(1+a))*(1+a)=1+b := Field.div_mul_cancel an
  have diff : (((1+b)/(1+a))-1)*(1+a)=b+(-a) := by grobner
  have dep := add_depth v hb (neg_depth v ha)
  refine ⟨nz,by rw [val,av,bv]; decide,?_⟩
  by_cases z : (1+b)/(1+a)-1=0
  · exact Or.inl z
  · have nn := prod_ne z an
    rw [←diff] at dep
    have hh := dep.resolve_left nn
    rw [v.mul z an,av] at hh
    exact Or.inr (by omega)

private theorem reconstruction {q m y a b : K} (ha : deep v 1 a) (hb : deep v 1 b)
    (eq : y*(1+a)=(q*m^2)*(1+b)) :
    ∃ u, principal v u ∧ y=(q*m^2)*u := by
  have nz := (one_plus v ha).1
  have clear : ((1+b)/(1+a))*(1+a)=1+b := Field.div_mul_cancel nz
  refine ⟨_,ratio v ha hb,?_⟩
  have zero : (y-q*m^2*((1+b)/(1+a)))*(1+a)=0 := by grobner
  have diff := (Field.of_mul_eq_zero zero).resolve_right nz
  grobner

/-- Reversed division polynomials are 1+qA and m²+qB at q=1/x.
    The strict inequality compares the leading denominator term to its tail. -/
theorem leading {q m y A B : K} (qn : q≠0) (mn : m≠0)
    (positive : 0<v.v q) (strict : 2*v.v m<v.v q)
    (ai : deep v 0 A) (bi : deep v 0 B) (eq : y*(1+q*A)=q*(m^2+q*B)) :
    ∃ u, principal v u ∧ y=(q*m^2)*u := by
  have ms : m^2=m*m := by grobner
  have sn : m^2≠0 := ms ▸ prod_ne mn mn
  have sv : v.v (m^2)=2*v.v m := by rw [ms,v.mul mn mn]; omega
  obtain ⟨_,rv⟩ := div_order v qn sn
  have qr : deep v 1 (q/m^2) := Or.inr (by omega)
  have qa := mul_depth v (Or.inr (by omega) : deep v 1 q) ai
  have qb := mul_depth v qr bi
  apply reconstruction v (a:=q*A) (b:=(q/m^2)*B) qa qb
  have cancel : (q/m^2)*m^2=q := Field.div_mul_cancel sn
  grobner

/-- The symmetry x ↦ −x on this curve makes both reversed polynomials even.
    One strict inequality works for all multipliers, including the first tripling. -/
theorem even_leading {q m y A B : K} (qn : q≠0) (mn : m≠0)
    (positive : 0<v.v q) (strict : v.v m<v.v q)
    (ai : deep v 0 A) (bi : deep v 0 B) (eq : y*(1+q^2*A)=q*(m^2+q^2*B)) :
    ∃ u, principal v u ∧ y=(q*m^2)*u := by
  have hq : q^2=q*q := by grobner
  have qm : q^2≠0 := hq ▸ prod_ne qn qn
  have qv : v.v (q^2)=2*v.v q := by rw [hq,v.mul qn qn]; omega
  have hm : m^2=m*m := by grobner
  have mm : m^2≠0 := hm ▸ prod_ne mn mn
  have mv : v.v (m^2)=2*v.v m := by rw [hm,v.mul mn mn]; omega
  have dv := (div_order v qm mm).2
  have qa := mul_depth v (Or.inr (by omega) : deep v 1 (q^2)) ai
  have qb := mul_depth v (Or.inr (by omega) : deep v 1 (q^2/m^2)) bi
  apply reconstruction v (a:=q^2*A) (b:=(q^2/m^2)*B) qa qb
  have cancel : (q^2/m^2)*m^2=q^2 := Field.div_mul_cancel mm
  grobner

/-- At three the denominator of the tripling map is (3−6s−s²)²,
    s=Dq². The estimate still holds at v(q)=2v(3). -/
theorem critical_three {q y D A : K} (qn : q≠0) (tn : (3:K)≠0)
    (positive : 0<v.v q) (strict : v.v (3:K)<2*v.v q)
    (di : deep v 0 D) (ai : deep v 0 A)
    (eq : y*(1+q*A)=q*(3-6*(D*q^2)-(D*q^2)^2)^2) :
    ∃ u, principal v u ∧ y=(q*(3:K)^2)*u := by
  let s := D*q^2
  have q2 : q^2=q*q := by grobner
  have sqn : q^2≠0 := q2 ▸ prod_ne qn qn
  have sqv : v.v (q^2)=2*v.v q := by rw [q2,v.mul qn qn]; omega
  have hv := (div_order v sqn tn).2
  have sr := mul_depth v di (Or.inr (by omega) : deep v 1 (q^2))
  have dr := mul_depth v di (Or.inr (by omega) : deep v 1 (q^2/3))
  let r := D*(q^2/3)
  have sh : deep v 1 s := sr
  have rh : deep v 1 r := dr
  have r3 : r*3=s := by
    have c : q^2/(3:K)*3=q^2 := Field.div_mul_cancel tn
    dsimp [r,s]; grobner
  let b := -(s+s+s*r)
  have bh : deep v 1 b :=
    neg_depth v (add_depth v (add_depth v sh sh) (mul_depth v sh (weaken v (by decide : (0:Int)≤1) rh)))
  have bh2 := add_depth v (add_depth v bh bh) (mul_depth v bh (weaken v (by decide : (0:Int)≤1) bh))
  have qa := mul_depth v (Or.inr (by omega) : deep v 1 q) ai
  apply reconstruction v (a:=q*A) (b:=b+b+b*b) qa bh2
  change y*(1+q*A)=q*(3-6*s-s^2)^2 at eq
  dsimp only [b]
  grobner

/-- Principal units multiply, so the residue information survives every prime step. -/
theorem principal_mul {a b : K} (ha : principal v a) (hb : principal v b) :
    principal v (a*b) := by
  obtain ⟨an,av,ar⟩ := ha
  obtain ⟨bn,bv,br⟩ := hb
  refine ⟨prod_ne an bn,by rw [v.mul an bn,av,bv]; decide,?_⟩
  have cross := mul_depth v ar (weaken v (by decide : (0:Int)≤1) br)
  have h := add_depth v (add_depth v ar br) cross
  rwa [show a-1+(b-1)+(a-1)*(b-1)=a*b-1 by grobner] at h

/-- Iteration keeps the residue of the normalized reciprocal abscissa equal to one. -/
theorem prime_powers (q : Nat → K) (p : K)
    (step : ∀ i, ∃ u, principal v u ∧ q (i+1)=q i*p^2*u) (k : Nat) :
    ∃ u, principal v u ∧ q k=q 0*(p^k)^2*u := by
  induction k with
  | zero =>
    refine ⟨1,⟨Ne.symm Field.zero_ne_one,v.one,Or.inl (by grobner)⟩,?_⟩
    rw [Semiring.pow_zero]; grobner
  | succ i ih =>
    obtain ⟨a,au,ae⟩ := ih
    obtain ⟨b,bu,be⟩ := step i
    refine ⟨a*b,principal_mul v au bu,?_⟩
    rw [be,ae,Semiring.pow_succ]; grobner

/-- A last multiplication by a unit can be appended to the prime-power calculation. -/
theorem combine {q r s a b : K}
    (h : ∃ u, principal v u ∧ r=q*a^2*u) (k : ∃ u, principal v u ∧ s=r*b^2*u) :
    ∃ u, principal v u ∧ s=q*(a*b)^2*u := by
  obtain ⟨u,uu,hu⟩ := h
  obtain ⟨w,wu,hw⟩ := k
  exact ⟨u*w,principal_mul v uu wu,by rw [hw,hu]; grobner⟩

#print axioms leading
#print axioms even_leading
#print axioms critical_three
#print axioms prime_powers
#print axioms combine
end AnchorCircuit.Division
