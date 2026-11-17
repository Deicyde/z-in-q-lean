import KummerLaw

namespace EllipticOrbit.AbscissaClass
open WeierstrassCurve.Affine
open EllipticOrbit.Law (curve)

variable {F : Type*} [Field F]

/-- Equality in the squareclass group, expressed without choosing coset representatives. -/
def Same (a b : F) : Prop := ∃ s : F, s≠0 ∧ a=b*s^2

theorem Same.refl (a : F) : Same a a := ⟨1,one_ne_zero,by simp⟩

theorem Same.trans {a b c : F} (ab : Same a b) (bc : Same b c) : Same a c := by
  obtain ⟨s,ns,hs⟩:=ab
  obtain ⟨t,nt,ht⟩:=bc
  exact ⟨s*t,mul_ne_zero ns nt,by rw [hs,ht]; ring⟩

theorem Same.mul {a b c d : F} (ab : Same a b) (cd : Same c d) : Same (a*c) (b*d) := by
  obtain ⟨s,ns,hs⟩:=ab
  obtain ⟨t,nt,ht⟩:=cd
  exact ⟨s*t,mul_ne_zero ns nt,by rw [hs,ht]; ring⟩

variable [DecidableEq F]

def finiteValue (D x : F) := if x=0 then -D else x

def value {D : F} : (curve D).Point → F
  | .zero => 1
  | .some (x:=x) _ => finiteValue D x

theorem finite_ne {D : F} (nd : D≠0) (x : F) : finiteValue D x≠0 := by
  by_cases h : x=0 <;> simp [finiteValue,h,nd]

theorem value_ne {D : F} (nd : D≠0) (P : (curve D).Point) : value P≠0 := by
  cases P with
  | zero => exact one_ne_zero
  | some => exact finite_ne nd _

private theorem root_zero {D a b : F} (nd : D≠0) (ab : a*b= -D) :
    finiteValue D 0*finiteValue D a*finiteValue D b=(-D)^2 := by
  have nab : a*b≠0 := ab ▸ neg_ne_zero.mpr nd
  rw [finiteValue,if_pos rfl,finiteValue,if_neg (left_ne_zero_of_mul nab),finiteValue,
    if_neg (right_ne_zero_of_mul nab),mul_assoc,ab,pow_two]

private theorem corrected {D x u z m c : F} (nd : D≠0)
    (pairs : x*u+x*z+u*z= -D-2*m*c) (triple : x*u*z=c^2) :
    ∃ s : F, s≠0 ∧ finiteValue D x*finiteValue D u*finiteValue D z=s^2 := by
  by_cases hc : c=0
  · subst c
    simp only [mul_zero,sub_zero,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] at pairs triple
    refine ⟨-D,neg_ne_zero.mpr nd,?_⟩
    rcases mul_eq_zero.mp triple with first|rfl
    · rcases mul_eq_zero.mp first with rfl|rfl
      · exact root_zero nd (by simpa using pairs)
      · simpa only [mul_comm (finiteValue D x) (finiteValue D 0)] using root_zero nd
          (a:=x) (b:=z) (by simpa using pairs)
    · simpa only [mul_comm (finiteValue D x*finiteValue D u) (finiteValue D 0),mul_assoc] using
        root_zero nd (a:=x) (b:=u) (by simpa using pairs)
  · have nz : x*u*z≠0 := triple ▸ pow_ne_zero 2 hc
    have nu:=left_ne_zero_of_mul nz
    exact ⟨c,hc,by simpa [finiteValue,left_ne_zero_of_mul nu,right_ne_zero_of_mul nu,
      right_ne_zero_of_mul nz] using triple⟩

private theorem coefficients {D x u y v : F} (hp : (curve D).Nonsingular x y)
    (hq : (curve D).Nonsingular u v) (nv : ¬(x=u ∧ y=(curve D).negY u v)) :
    let m:=(curve D).slope x u y v
    let z:=(curve D).addX x u m
    let c:=y-m*x
    x*u+x*z+u*z= -D-2*m*c ∧ x*u*z=c^2 := by
  have eq:=addPolynomial_slope hp.1 hq.1 nv
  rw [addPolynomial_eq,neg_inj,Cubic.prod_X_sub_C_eq,Cubic.toPoly_injective] at eq
  have C:=congrArg Cubic.c eq
  have B:=congrArg Cubic.d eq
  dsimp only [curve] at C B ⊢
  constructor
  · linear_combination -C
  · linear_combination B

/-- The abscissa class preserves the actual Mathlib group law. The polynomial
    factorization includes tangent intersections counted with multiplicity. -/
theorem value_add {D : F} (nd : D≠0) (P Q : (curve D).Point) :
    Same (value (P+Q)) (value P*value Q) := by
  cases P with
  | zero => simpa [value] using Same.refl (value Q)
  | @some x y hp =>
    cases Q with
    | zero => simpa [value] using Same.refl (value (.some hp))
    | @some u v hq =>
      by_cases vert : x=u ∧ y=(curve D).negY u v
      · rw [Point.add_of_Y_eq vert.1 vert.2]
        change Same 1 (finiteValue D x*finiteValue D u)
        rw [vert.1]
        refine ⟨(finiteValue D u)⁻¹,inv_ne_zero (finite_ne nd _),?_⟩
        field_simp [finite_ne nd u]
      · rw [Point.add_some vert]
        let m:=(curve D).slope x u y v
        let z:=(curve D).addX x u m
        obtain ⟨sm,pr⟩:=coefficients hp hq vert
        obtain ⟨s,ns,eq⟩:=corrected nd sm pr
        change Same (finiteValue D z) (finiteValue D x*finiteValue D u)
        let B:=finiteValue D x*finiteValue D u
        have nB : B≠0 := mul_ne_zero (finite_ne nd x) (finite_ne nd u)
        change B*finiteValue D z=s^2 at eq
        refine ⟨s/B,div_ne_zero ns nB,?_⟩
        change finiteValue D z = B*(s/B)^2
        field_simp [nB]
        linear_combination eq

theorem value_double {D : F} (nd : D≠0) (Q : (curve D).Point) : Same (value ((2:ℤ) • Q)) 1 := by
  rw [two_zsmul]
  exact (value_add nd Q Q).trans ⟨value Q,value_ne nd Q,by simp [pow_two]⟩

end EllipticOrbit.AbscissaClass

#print axioms EllipticOrbit.AbscissaClass.value_add
#print axioms EllipticOrbit.AbscissaClass.value_double
