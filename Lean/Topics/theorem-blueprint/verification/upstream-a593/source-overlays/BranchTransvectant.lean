import BranchWeights

/-! A coefficient form of the integral quartic invariant. -/
namespace ZInQBlueprint.BranchI4
open Polynomial SexticInvariants
noncomputable section

/-- The integer coefficient form of the fourth Igusa–Clebsch invariant,
in ascending order of the sextic coefficients. -/
def quartic (a b c d e g h : ℂ) : ℂ :=
  1620*a^2*h^2 - 540*a*b*g*h - 504*a*c*e*h + 300*a*c*g^2 +
  324*a*d^2*h - 180*a*d*e*g + 48*a*e^3 + 300*b^2*e*h - 80*b^2*g^2 -
  180*b*c*d*h + 4*b*c*e*g + 36*b*d^2*g - 12*b*d*e^2 + 48*c^3*h -
  12*c^2*d*g + 4*c^2*e^2

theorem quartic_eq (f : ℚ[X]) :
    (igusaI4 f : ℂ) = quartic (f.coeff 0) (f.coeff 1) (f.coeff 2)
      (f.coeff 3) (f.coeff 4) (f.coeff 5) (f.coeff 6) := by
  unfold quartic igusaI4 sexticA sexticB quarticB
  push_cast
  ring

theorem scale_quartic (s a b c d e g h : ℂ) :
    quartic (s*a) (s*b) (s*c) (s*d) (s*e) (s*g) (s*h) = s^4*quartic a b c d e g h := by
  unfold quartic
  ring

/-- Translation in the independent variable leaves the invariant unchanged. -/
theorem translate_quartic (a b c d e g h z : ℂ) :
    quartic (a+z*(b+z*(c+z*(d+z*(e+z*(g+z*h))))))
      (b+z*(2*c+z*(3*d+z*(4*e+z*(5*g+z*6*h)))))
      (c+z*(3*d+z*(6*e+z*(10*g+z*15*h))))
      (d+z*(4*e+z*(10*g+z*20*h))) (e+z*(5*g+z*15*h)) (g+z*6*h) h =
      quartic a b c d e g h := by
  unfold quartic
  grind only [ring] 

end
end ZInQBlueprint.BranchI4
#print axioms ZInQBlueprint.BranchI4.quartic_eq
#print axioms ZInQBlueprint.BranchI4.scale_quartic
#print axioms ZInQBlueprint.BranchI4.translate_quartic
