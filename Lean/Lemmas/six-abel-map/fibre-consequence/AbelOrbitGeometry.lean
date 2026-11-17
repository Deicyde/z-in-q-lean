import GeometricFibreDivisor

/-! The geometric divisor comparison of the original signed sextic. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
open GeometricMarking MarkedForm
noncomputable section
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- The original sextic has a genuine Abel map on its geometric points.
It generates the rational Jacobian after base change, and all degree-two
fibre divisors give the same class, including the ramified fibres. -/
def divisorData : DivisorData hu :=
  divisorData_of_principal hu (FibreDivisors.paper_fibre_principal hu)

/-- Equality holds for every pair of weighted geometric points. -/
theorem weighted_fibre_sums (p q : FibrePoints u) :
    weightedAbel hu p + weightedAbel hu (negY (paperForm u (δ u)) p) =
    weightedAbel hu q + weightedAbel hu (negY (paperForm u (δ u)) q) :=
  (divisorData hu).fibres p q

/-- Divisor classes on the actual rational Jacobian supply the geometric-point comparison
appearing in the six-contact automorphism argument. -/
def picardComparison : PicardComparison hu (JacobianPoints hu) :=
  (divisorData hu).comparison

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.divisorData
#print axioms ZInQBlueprint.SixAbelMap.weighted_fibre_sums
#print axioms ZInQBlueprint.SixAbelMap.picardComparison
