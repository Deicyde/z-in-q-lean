import ThreeCoordinates

namespace ProgressionWitnesses.SingleContactPole

/-- Glazer's four signed equations, with the original rational abscissa b. -/
def Seven (b : Rat) : Prop :=
  let B := 17*b
  ∃ t U e p q s H : Rat,
    U*(1+b*t^2)=b*(1-b*t^2) ∧ p^2=B*(1-e)*(1+3*e) ∧ H=e*(B-U^2) ∧
    B*q^2=(s^2-B*H)*(s^2+3*B*H)

theorem input_factors (b : Rat) :
    (17*b)*(17*b-b^2)=b^2*(289-17*b) ∧ (289-17*b)=289*(1-b/17) := by
  constructor <;> grobner

/-- Fixed t=0 and U=b provide a division-free map, including the endpoint s=0. -/
theorem weak_to_seven (b : Rat) (hw : ReviewedPole.Weak (17*b) (289-17*b)) : Seven b := by
  obtain ⟨e,s,v,p,q,first,link,last⟩ := hw
  refine ⟨0,b,e,(17*b)*p,b^2*s*q,b*s,e*(17*b-b^2),?_,?_,rfl,?_⟩
  · grobner
  · grobner
  · have A : (b*s)^2-(17*b)*(e*(17*b-b^2)) = b^2*s*(s-v) := by grobner
    have D : (b*s)^2+3*(17*b)*(e*(17*b-b^2)) = b^2*s*(s+3*v) := by grobner
    rw [A,D]
    calc (17*b)*(b^2*s*q)^2 = (b^2*s)^2*((17*b)*q^2) := by grobner
         _ = (b^2*s*(s-v))*(b^2*s*(s+3*v)) := by rw [←last];grobner

theorem sextic_to_seven (b : Rat) (h : ThreeCoordinates.Sextic (17*b) (289-17*b)) : Seven b :=
  weak_to_seven b ((ThreeCoordinates.weak_iff_sextic (17*b)).mpr h)

#print axioms input_factors
#print axioms weak_to_seven
#print axioms sextic_to_seven
end ProgressionWitnesses.SingleContactPole
