import DeterminantPointTranslation
import DeterminantPicardClass
import SignedCanonicalTheta

/-! Poincaré evaluation on the geometric group scheme of the signed sextic. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve NeronModelInfra GoodReductionJacobian JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantAutoduality
open SixAbelMap CanonicalTheta AbelianModel GeometricMarking QuaternionMarking NormalDescent SixThetaRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
variable {F : Type} [Field F] [Algebra Qbar F] [IsCurveOver Qbar F]
variable {C : Over (Spec (.of Qbar))} [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIntegral C.hom] {b : base Qbar ⟶ C} {V : GroupScheme Qbar}
  {e : V ≅ groupScheme Qbar C.hom} {m : C ⟶ V.X}
variable (P : Pointed b e m)

set_option linter.unusedSectionVars false in
theorem transported_point_formula (M : CurveModel Qbar F) (i : M.C ≅ C.left)
    (hi : i.hom ≫ C.hom = M.toBase) (hg : genusFF Qbar F = 2) (p : base Qbar ⟶ C) :
    Nonempty (translated P.determinantLine (Additive.ofMul (p ≫ m)) ⊗ evaluationLine P p ≅ P.determinantLine) := by
  let := PGroup C (schemePoint b) P.represents
  let X := (Over.mk P.J.toBase)
  let E := P.toRepresenting
  let t : sections V := Additive.ofMul (p ≫ m)
  let q : base Qbar ⟶ X := p ≫ Over.homMk P.aj.1 P.aj.2
  let tr : X ⟶ X := 𝟙 X * (CartesianMonoidalCategory.toUnit X ≫ q)
  have tq : t.toMul ≫ E.hom = q := (Category.assoc p m E.hom).trans ((congrArg (p ≫ ·) P.abel_comparison))
  have m1 : E.hom ≫ CartesianMonoidalCategory.toUnit X = SixThetaRestriction.toBase V.X := by
    apply Over.OverMorphism.ext
    change E.hom.left ≫ (CartesianMonoidalCategory.toUnit X).left = V.X.hom
    rw [Over.toUnit_left,E.hom.w]
  have commute : (translation t).hom ≫ E.hom = E.hom ≫ tr := by
    change (𝟙 V.X * (SixThetaRestriction.toBase V.X ≫ t.toMul)) ≫ E.hom = E.hom ≫ (𝟙 X * (CartesianMonoidalCategory.toUnit X ≫ q))
    rw [representing_mul,MonObj.comp_mul,Category.id_comp,Category.comp_id]
    apply congrArg (E.hom * ·)
    exact (Category.assoc _ _ _).trans ((congrArg (SixThetaRestriction.toBase V.X ≫ ·) tq).trans
      ((congrArg (· ≫ q) m1.symm).trans (Category.assoc _ _ _)))
  let L := thetaBundle C.hom (schemePoint b) P.J.toBase P.represents.poincare 4 3
  let U := (Scheme.Modules.pullback (rigSection C.hom P.J.toBase (schemePoint p))).obj P.represents.poincare.L
  let z := (Scheme.Modules.pullbackComp (translation t).hom.left E.hom.left).app L ≪≫
    (Scheme.Modules.pullbackCongr (congrArg (fun f : V.X ⟶ X => f.left) commute)).app L ≪≫
    ((Scheme.Modules.pullbackComp E.hom.left tr.left).app L).symm
  obtain ⟨qE⟩ := representing_point_formula P M i hi hg p
  exact ⟨(z ⊗ᵢ Iso.refl _) ≪≫ (Scheme.Modules.pullbackTensorObjIso E.hom.left _ U).symm ≪≫
    (Scheme.Modules.pullback E.hom.left).mapIso qE⟩

open BinaryCover
theorem paperProper (u : ℚ) : IsProper (paperCurve u).hom := by
  let := paper_proper ℚ u
  exact inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
theorem paperIntegral {u : ℚ} (hu : u ∉ ZInQ.contactSet) : GeometricallyIntegral (paperCurve u).hom := by
  let := geometricallyIntegral_paperModel hu
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
theorem paperSmooth {u : ℚ} (hu : u ∉ ZInQ.contactSet) : SmoothOfRelativeDimension 1 (paperCurve u).hom := by
  let c := (paperModel ℚ u).hom
  let : Smooth c := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral (paperModel ℚ u).left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 c := SixJacobian.relative_dimension_one c (paper_dimension ℚ u)
  exact inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd c (scalarMap ℚ Qbar)))

variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)
local notation "J" => geometricJacobian hu

/-- At the actual weighted point p use the fibre of the fixed rigidified Poincaré family. -/
def signedEvaluation (p : FibrePoints u) : (geometricJacobian hu).X.left.Modules := by
  letI := paperProper u
  letI := paperIntegral hu
  letI := paperSmooth hu
  exact evaluationLine (signedPointed hu) (WeightedCurvePoints.weightedEquiv_pullback hu p)

theorem signedEvaluation_invertible (p : FibrePoints u) : (signedEvaluation hu p).IsInvertible := by
  let := paperProper u
  let := paperIntegral hu
  let := paperSmooth hu
  exact evaluationLine_invertible _ _

theorem signed_evaluation_formula (p : FibrePoints u) :
    Nonempty (translated (signedThetaLine hu) ((rigidDivisors hu).abel p) ⊗ signedEvaluation hu p ≅ signedThetaLine hu) := by
  let := paperProper u
  let := paperIntegral hu
  let := paperSmooth hu
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  let := N.curve
  exact transported_point_formula (signedPointed hu) N.model N.iso N.hbase (paper_functionField_genus hu)
    (WeightedCurvePoints.weightedEquiv_pullback hu p)

end
end ZInQBlueprint.DeterminantAutoduality
#print axioms ZInQBlueprint.DeterminantAutoduality.transported_point_formula
#print axioms ZInQBlueprint.DeterminantAutoduality.signedEvaluation_invertible
#print axioms ZInQBlueprint.DeterminantAutoduality.signed_evaluation_formula
