import ThreeCoordinates

namespace WitnessTransfer.FixedZero

/-- The fixed-zero preparation t=0, U=b in the original four equations. -/
def PsiZero (b : Rat) : Prop :=
  let B := 17*b
  ∃ e p q s : Rat, p^2=B*(1-e)*(1+3*e) ∧
    B*q^2=(s^2-B*(e*(B-b^2)))*(s^2+3*(B*(e*(B-b^2))))

private theorem cancel {a c m : Rat} (hm : m≠0) (eq : a*m=c*m) : a=c := by grind

/-- Division-free realization from the two-conic predicate. -/
theorem from_weak (b : Rat) (h : ReviewedPole.Weak (17*b) (289-17*b)) : PsiZero b := by
  obtain ⟨e,s,v,p,q,first,link,last⟩ := h
  refine ⟨e,(17*b)*p,b^2*s*q,b*s,?_,?_⟩
  · grobner
  · have A : (b*s)^2-(17*b)*(e*(17*b-b^2))=b^2*s*(s-v) := by grobner
    have D : (b*s)^2+3*((17*b)*(e*(17*b-b^2)))=b^2*s*(s+3*v) := by grobner
    rw [A,D]
    calc
      (17*b)*(b^2*s*q)^2 = (b^2*s)^2*((17*b)*q^2) := by grobner
      _ = (b^2*s*(s-v))*(b^2*s*(s+3*v)) := by rw [←last]; grobner

private theorem square_sextic (B a : Rat) (equal : B=a^2) :
    ThreeCoordinates.Sextic B (289-B) := by
  exact ⟨0,a,0,by rw [equal]; grobner⟩

private theorem minus_three_sextic (B a : Rat) (equal : B= -3*a^2) :
    ThreeCoordinates.Sextic B (289-B) := by
  exact ⟨0,a,0,by rw [equal]; grobner⟩

/-- Positive and signed exceptions, zero ordinates, b=0, and b=17 are all included. -/
theorem to_weak (b : Rat) (witness : PsiZero b) : ReviewedPole.Weak (17*b) (289-17*b) := by
  let B := 17*b
  let d := 289-B
  change ReviewedPole.Weak B d
  obtain ⟨e,p,q,s,first,second⟩ := witness
  change p^2=B*(1-e)*(1+3*e) at first
  let C := B*(e*(B-b^2))
  change B*q^2=(s^2-C)*(s^2+3*C) at second
  have scale : C=b^2*d*e := by dsimp [B,C,d]; grobner
  by_cases hz : b=0
  · have e0 : B=0^2 := by dsimp [B]; rw [hz]; grobner
    exact (ThreeCoordinates.weak_iff_sextic B).mpr (square_sextic B 0 e0)
  have hB : B≠0 := by dsimp [B]; grind
  by_cases hs : s=0
  · have relation : B*q^2= -3*C^2 := by rw [hs] at second; grobner
    apply (ThreeCoordinates.weak_iff_sextic B).mpr
    by_cases hq : q=0
    · have c2 : C*C=0 := by rw [hq] at relation; grobner
      have c0 : C=0 := by rcases Rat.mul_eq_zero.mp c2 with h|h <;> exact h
      have cases : e=0 ∨ B-b^2=0 :=
        Rat.mul_eq_zero.mp ((Rat.mul_eq_zero.mp (show B*(e*(B-b^2))=0 from c0)).resolve_left hB)
      rcases cases with he|hb
      · apply square_sextic B p
        rw [he] at first; grobner
      · exact square_sextic B b (by grobner)
    · let a := C/q
      have aq : a*q=C := Rat.div_mul_cancel hq
      apply minus_three_sextic B a
      apply cancel (m:=q^2) (by grind)
      calc
        B*q^2 = -3*C^2 := relation
        _ = (-3*a^2)*q^2 := by rw [←aq]; grobner
  · let S := s/b
    let v := b*d*e/s
    let P := p/B
    let Q := q/(b*s)
    have sB : S*b=s := Rat.div_mul_cancel hz
    have vs : v*s=b*d*e := Rat.div_mul_cancel hs
    have pb : P*B=p := Rat.div_mul_cancel hB
    have qb : Q*(b*s)=q := Rat.div_mul_cancel (by grind)
    refine ⟨e,S,v,P,Q,?_,?_,?_⟩
    · apply cancel (m:=B) hB
      calc
        ((1-e)*(1+3*e))*B = p^2 := by grobner
        _ = (B*P^2)*B := by rw [←pb]; grobner
    · apply cancel (m:=b*s) (by grind)
      calc
        (S*v)*(b*s) = (S*b)*(v*s) := by grobner
        _ = (d*e)*(b*s) := by rw [sB,vs]; grobner
    · have u : (S-v)*(b*s)=s^2-C := by
        calc
          _ = (S*b)*s-b*(v*s) := by grobner
          _ = _ := by rw [sB,vs,scale]; grobner
      have w : (S+3*v)*(b*s)=s^2+3*C := by
        calc
          _ = (S*b)*s+3*b*(v*s) := by grobner
          _ = _ := by rw [sB,vs,scale]; grobner
      apply cancel (m:=(b*s)^2) (by grind)
      calc
        ((S-v)*(S+3*v))*(b*s)^2 = ((S-v)*(b*s))*((S+3*v)*(b*s)) := by grobner
        _ = B*q^2 := by rw [u,w,←second]
        _ = (B*Q^2)*(b*s)^2 := by rw [←qb]; grobner

theorem exact_weak (b : Rat) : PsiZero b ↔ ReviewedPole.Weak (17*b) (289-17*b) :=
  ⟨to_weak b,from_weak b⟩

theorem exact_sextic (b : Rat) :
    PsiZero b ↔ ∃ U V J : Rat,
      J^2*(U^2-17*b)*(U^2+3*(17*b))=(289-17*b)*(17*b-V^2)*(17*b+3*V^2) :=
  (exact_weak b).trans (ThreeCoordinates.weak_iff_sextic (17*b))

#print axioms from_weak
#print axioms to_weak
#print axioms exact_weak
#print axioms exact_sextic
end WitnessTransfer.FixedZero
