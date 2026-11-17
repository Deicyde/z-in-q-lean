import AbelOrbitEndpoint
import ChartGenericField
import QuadraticDeckTransfer

/-! All scheme places on the signed sextic satisfy the exact principal-fibre statement
needed by its Abel–Jacobi map. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
namespace ZInQBlueprint.FibreDivisors
open BinaryCover GeometricMarking NormalDescent WeightedCurvePoints SixAbelMap
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

private abbrev chart {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    SpecOver (R := Qbar) (Cover (paper Qbar u false)) ⟶ paperCurve u :=
  chartInclusion Qbar _ _ (paper_overlap Qbar u) false ≫ (baseChangeIso hu).hom

private instance chartOpen {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    IsOpenImmersion (chart hu).left := by
  let j := chartInclusion Qbar _ _ (paper_overlap Qbar u) false
  let h : IsOpenImmersion j.left := chartInclusion_open ..
  let e := (Over.forget _).mapIso (baseChangeIso hu)
  exact @IsOpenImmersion.comp _ _ _ j.left e.hom h (IsOpenImmersion.of_isIso _)

theorem actual_chart_deck {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (chart hu).left ≫ ((Over.forget _).mapIso (geometricDeck hu)).inv =
      starSpec (Cover (paper Qbar u false)) ≫ (chart hu).left := by
  let j := (chartInclusion Qbar _ _ (paper_overlap Qbar u) false).left
  let t := (Over.forget _).mapIso (baseChangeIso hu)
  let g := WeightedCurvePoints.deck (paper Qbar u false) (paper Qbar u true) (paper_overlap Qbar u)
  change (j ≫ t.hom) ≫ t.inv ≫ g ≫ t.hom = _ ≫ j ≫ t.hom
  rw [Category.assoc,t.hom_inv_id_assoc,←Category.assoc]
  exact congrArg (fun z => z ≫ t.hom) (deck_chart _ _ (paper_overlap Qbar u) false)

/-- Principal difference of two scheme fibres, including ramification and infinity, for the
literal geometric sextic. The automorphism is the weighted sign change on its sections. -/
theorem paper_fibre_principal {u : ℚ} (hu : u ∉ ZInQ.contactSet) : PrincipalFibres hu := by
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let f := paper Qbar u false
  letI : IsDomain (Cover f) := field_chart_domain Qbar hu false
  letI : Fact (¬ IsSquare (rmap f)) := ⟨paper_nonsquare hu⟩
  let j := chart hu
  let e : (paperCurve u).left.functionField ≃ₐ[Qbar] Cover (rmap f) :=
    { chartFieldIso f j with
      commutes' := fun c => by
        change chartFieldIso f j (baseToFunctionField (paperCurve u).hom c) = _
        rw [chartFieldIso_constants]
        rw [IsScalarTower.algebraMap_apply Qbar (Polynomial Qbar) (Cover f),
          IsScalarTower.algebraMap_apply Qbar (RatFunc Qbar) (Cover (rmap f)), chartEmbedding_polynomial]
        congr 1 }
  intro P Q
  apply principal_of_coordinate_equiv (rmap f) e (functionAction (geometricDeck hu)) _ P Q
  intro x
  exact chartFieldIso_action f j ((Over.forget _).mapIso (geometricDeck hu)) (actual_chart_deck hu) x

end
end ZInQBlueprint.FibreDivisors
#print axioms ZInQBlueprint.FibreDivisors.actual_chart_deck
#print axioms ZInQBlueprint.FibreDivisors.paper_fibre_principal

