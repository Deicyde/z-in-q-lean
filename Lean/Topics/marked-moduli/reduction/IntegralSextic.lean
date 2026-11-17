import ClusterParameters
import RationalModel

/-! A binary sextic over the integers for the six-contact family. -/
namespace ZInQBlueprint.IntegralSextic
open ZInQBlueprint.ResidualFactors ZInQBlueprint.SexticConjugation
open ZInQBlueprint.SixContact
variable {R : Type*} [CommRing R]
def m (A B : R) := 3*A*(A+20*B)*(A+30*B)
def n (A B : R) := 10*(A+15*B)*(A+24*B)*(A+60*B)
def hForm (A B : R) := (A^2-60*A*B-1800*B^2)*(13*A^2+480*A*B+3600*B^2)*(11*A^2+600*A*B+7200*B^2)

theorem parameter_identities (A B : R) :
    m A B*n A B=30*contactProduct A B ∧
    (poleForm A B)^3=27*(m A B)^2+(n A B)^2 ∧
    hForm A B=27*(m A B)^2-(n A B)^2 := by
  unfold m n contactProduct poleForm hForm
  refine ⟨?_,?_,?_⟩ <;> ring

def alpha (X Z : R) := X*(X+3*Z)
def beta (X Z : R) := Z*(X+2*Z)
def gamma (X Z : R) := X^2+4*X*Z+6*Z^2
def form (a b X Z : R) := a^2*(alpha X Z)^3-a*b*alpha X Z*beta X Z*gamma X Z+b^2*(beta X Z)^3
def integralEquation (δ A B X Z : R) := -6*δ*poleForm A B*form (m A B) (n A B) X Z

theorem reciprocal (a b X Z : R) : form a b (6*Z) X = 8*form b (27*a) X Z := by
  unfold form alpha beta gamma; ring


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 5000 in
/-- On the moduli conic the descended polynomial is linear in 1, r and h. -/
theorem expansion {d r h : R} (hd : d^2=6) (ht : 9*(d*r)^2-32 = -32*h^2) (X Z : R) :
    RationalModel.equation d r h X Z = 2^23*h^6*
      (4*(1+h)*(alpha X Z)^3-27*r*alpha X Z*beta X Z*gamma X Z+108*(1-h)*(beta X Z)^3) := by
  unfold RationalModel.equation binary alpha beta gamma
  rw [ht]
  have h3 : d^3 = 6*d := by linear_combination d^1*hd
  have h4 : d^4 = 36 := by linear_combination d^2*hd + 6*hd
  have h5 : d^5 = 36*d := by linear_combination d^3*hd + 6*h3
  have h6 : d^6 = 216 := by linear_combination d^4*hd + 6*h4
  have h7 : d^7 = 216*d := by linear_combination d^5*hd + 6*h5
  have h8 : d^8 = 1296 := by linear_combination d^6*hd + 6*h6
  have h9 : d^9 = 1296*d := by linear_combination d^7*hd + 6*h7
  have h10 : d^10 = 7776 := by linear_combination d^8*hd + 6*h8
  have h11 : d^11 = 7776*d := by linear_combination d^9*hd + 6*h9
  have h12 : d^12 = 46656 := by linear_combination d^10*hd + 6*h10
  have h13 : d^13 = 46656*d := by linear_combination d^11*hd + 6*h11
  have h14 : d^14 = 279936 := by linear_combination d^12*hd + 6*h12
  have h15 : d^15 = 279936*d := by linear_combination d^13*hd + 6*h13
  have h16 : d^16 = 1679616 := by linear_combination d^14*hd + 6*h14
  ring_nf
  simp only [hd,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16]
  ring

/-- Multiplying the equation by G³ clears its parameter denominators. -/
theorem cleared {d r h A B : R} (hd : d^2=6) (ht : 9*(d*r)^2-32 = -32*h^2)
    (hr : (poleForm A B)^3*r=240*contactProduct A B)
    (hh : (poleForm A B)^3*h=hForm A B) (X Z : R) :
    (poleForm A B)^3*RationalModel.equation d r h X Z =
      2^25*54*h^6*form (m A B) (n A B) X Z := by
  obtain ⟨hf,hg,hH⟩ := parameter_identities A B
  rw [expansion hd ht]
  unfold form
  linear_combination
    (2^23*h^6*4*(alpha X Z)^3-2^23*h^6*108*(beta X Z)^3)*(hh+hH) +
    (2^23*h^6*4*(alpha X Z)^3+2^23*h^6*108*(beta X Z)^3)*hg -
    (2^23*h^6*27*alpha X Z*beta X Z*gamma X Z)*hr +
    (2^25*54*h^6*alpha X Z*beta X Z*gamma X Z)*hf

end ZInQBlueprint.IntegralSextic
#print axioms ZInQBlueprint.IntegralSextic.parameter_identities
#print axioms ZInQBlueprint.IntegralSextic.reciprocal
#print axioms ZInQBlueprint.IntegralSextic.expansion
#print axioms ZInQBlueprint.IntegralSextic.cleared
