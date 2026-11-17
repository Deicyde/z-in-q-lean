import RigidifiedAbel
import AbelOrbitGeometry

/-! The Abel curve of the signed model, with its pointed Picard normalization retained. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open JacobianVarieties.Picard.Unpointed GoodReductionJacobian
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
open BinaryCover GeometricMarking NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

private theorem rigid_curve_proper (u : ℚ) : IsProper (paperCurve u).hom := by
  let := paper_proper ℚ u
  exact inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))

private theorem rigid_curve_integral {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    GeometricallyIntegral (paperCurve u).hom := by
  let := geometricallyIntegral_paperModel hu
  exact inferInstanceAs (GeometricallyIntegral (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))

private theorem rigid_curve_dimension {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    SmoothOfRelativeDimension 1 (paperCurve u).hom := by
  let c := (paperModel ℚ u).hom
  let : Smooth c := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral (paperModel ℚ u).left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 c := SixJacobian.relative_dimension_one c (paper_dimension ℚ u)
  exact inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd c (scalarMap ℚ Qbar)))


variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)
private def pointedPresentation :
    letI := rigid_curve_proper u
    letI := rigid_curve_integral hu
    letI := rigid_curve_dimension hu
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    let N := signedModel hu
    letI := N.curve
    AbelPresentation (paperCurve u) N.model N.iso N.hbase (groupScheme Qbar (paperCurve u).hom) (basepoint hu) := by
  letI := rigid_curve_proper u
  letI := rigid_curve_integral hu
  letI := rigid_curve_dimension hu
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  letI := N.curve
  exact (exists_representing_abel (paperCurve u) N.model N.iso N.hbase (basepoint hu)).choose

private abbrev picardIso :=
  letI := rigid_curve_proper u
  letI := rigid_curve_integral hu
  letI := rigid_curve_dimension hu
  IntegralPicard.paperJacobian_baseChangeIso Qbar hu (paperCurve u) (Iso.refl _)

def rigidPresentation :
    letI := rigid_curve_proper u
    letI := rigid_curve_integral hu
    letI := rigid_curve_dimension hu
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    let N := signedModel hu
    letI := N.curve
    AbelPresentation (paperCurve u) N.model N.iso N.hbase (geometricJacobian hu) (basepoint hu) := by
  letI := rigid_curve_proper u
  letI := rigid_curve_integral hu
  letI := rigid_curve_dimension hu
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  letI := (signedModel hu).curve
  exact (pointedPresentation hu).transport (picardIso hu).symm

def rigidMorphism : paperCurve u ⟶ (geometricJacobian hu).X := by
  letI := rigid_curve_proper u
  letI := rigid_curve_integral hu
  letI := rigid_curve_dimension hu
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  letI := (signedModel hu).curve
  exact (rigidPresentation hu).morphism

/-- Under the canonical comparison to the Picard variety of the scalar-extended
curve, this very morphism represents the relative point divisor. -/
theorem rigid_classifies :
    letI := rigid_curve_proper u
    letI := rigid_curve_integral hu
    letI := rigid_curve_dimension hu
    letI := sourceIntegral hu
    letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
    RepresentsPointDivisors (paperCurve u) (basepoint hu)
      (rigidMorphism hu ≫ (picardIso hu).hom.hom.hom.hom) := by
  let := rigid_curve_proper u
  let := rigid_curve_integral hu
  let := rigid_curve_dimension hu
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  let := N.curve
  have h := (exists_representing_abel (paperCurve u) N.model N.iso N.hbase (basepoint hu)).choose_spec
  have can : (picardIso hu).inv.hom.hom.hom ≫ (picardIso hu).hom.hom.hom.hom = 𝟙 _ :=
    congrArg (fun f => f.hom.hom.hom) (picardIso hu).inv_hom_id
  let f := (pointedPresentation hu).morphism
  let g := (picardIso hu).hom.hom.hom.hom
  let k := (picardIso hu).inv.hom.hom.hom
  have hw : (f ≫ k) ≫ g = f := (Category.assoc f k g).trans
    ((congrArg (fun a => f ≫ a) can).trans (Category.comp_id f))
  exact hw.symm ▸ (show RepresentsPointDivisors (paperCurve u) (basepoint hu) f from h)

/-- Milne's positive-genus closed-immersion input for the pointed Picard functor.
It applies to any representing designation and the morphism classifying P-b. -/
def PointedEmbedding (C : Over (Spec (.of Qbar)))
    [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom] : Prop :=
  ∀ (b : base Qbar ⟶ C) (m : C ⟶ (groupScheme Qbar C.hom).X),
    RepresentsPointDivisors C b m → IsClosedImmersion m.left

/-- The geometric hypotheses are implemented using the signed model. -/
def PaperEmbedding : Prop :=
  letI := rigid_curve_proper u
  letI := rigid_curve_integral hu
  letI := rigid_curve_dimension hu
  PointedEmbedding (paperCurve u)

/-- Closed immersion transfers through the canonical base-change isomorphism. -/
theorem rigid_closed_of_pointed (H : PaperEmbedding hu) : IsClosedImmersion (rigidMorphism hu).left := by
  let := rigid_curve_proper u
  let := rigid_curve_integral hu
  let := rigid_curve_dimension hu
  let e := (CommGrp.forget _ ⋙ Over.forget _).mapIso (picardIso hu)
  let m := (rigidMorphism hu).left
  have h : IsClosedImmersion (m ≫ e.hom) := H (basepoint hu) _ (rigid_classifies hu)
  have pull : IsClosedImmersion ((m ≫ e.hom) ≫ e.inv) := inferInstance
  have eq : (m ≫ e.hom) ≫ e.inv = m := (Category.assoc m e.hom e.inv).trans
    ((congrArg (fun f => m ≫ f) e.hom_inv_id).trans (Category.comp_id m))
  exact Eq.mp (congrArg (fun f => IsClosedImmersion f) eq) pull

/-- All three divisor properties hold for the normalized morphism itself. -/
def rigidDivisors : DivisorData hu := by
  letI := rigid_curve_proper u
  letI := rigid_curve_integral hu
  letI := rigid_curve_dimension hu
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  letI := N.curve
  let A := rigidPresentation hu
  let c := WeightedCurvePoints.weightedEquiv_pullback hu
  refine {abel := fun p => A.abel (c p), generate := ?_, fibres := ?_}
  · apply top_unique
    rw [←A.generate]
    apply AddSubgroup.closure_mono
    rintro _ ⟨⟨p,q⟩,rfl⟩
    obtain ⟨v,rfl⟩ := c.surjective p
    obtain ⟨w,rfl⟩ := c.surjective q
    exact ⟨(v,w),rfl⟩
  · intro p q
    let e := geometricDeck hu
    have hp := FibreDivisors.paper_fibre_principal hu (normalizedPlace N (c p)) (normalizedPlace N (c q))
    rw [←normalizedPlace_action N e (c p), ←normalizedPlace_action N e (c q)] at hp
    change A.abel (c p) + A.abel (WeightedCurvePoints.weightedEquiv_pullback hu _) =
      A.abel (c q) + A.abel (WeightedCurvePoints.weightedEquiv_pullback hu _)
    rw [weighted_deck hu p, weighted_deck hu q]
    exact A.sum_eq_of_principal (c p) (c p ≫ e.hom) (c q) (c q ≫ e.hom) hp

theorem rigid_on_points (p : FibrePoints u) :
    (rigidDivisors hu).abel p =
      Additive.ofMul (WeightedCurvePoints.weightedEquiv_pullback hu p ≫ rigidMorphism hu) := rfl

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.rigid_classifies
#print axioms ZInQBlueprint.SixAbelMap.rigidDivisors
#print axioms ZInQBlueprint.SixAbelMap.rigid_on_points

#print axioms ZInQBlueprint.SixAbelMap.rigid_closed_of_pointed
