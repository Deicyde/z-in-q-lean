import PrintedCurve
import OrdinaryGoodReduction

/-! The geometric Jacobian of the signed rational curve is isomorphic as
a group scheme to the unpointed Jacobian of the printed Baba--Granath model. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.PrintedModel
open BinaryCover
noncomputable section
variable {K : Type} [Field K] [CharZero K] {u : ℚ} {d : K}

/-- Extension of the specified affine change to the literal scalar extension. -/
def curveIso (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) (v : K) (hv : v^2=factor u d) :
    paperPullback K u ≅ model hu hd :=
  (unique_reglued_baseChange K hu).exists.choose.symm ≪≫ (unique_printed_iso hu hd v hv).exists.choose

instance model_proper (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) : IsProper (model hu hd).hom :=
  (sexticCompletion_geometry (printed_degree hu hd) (printed_separable hu hd)).2.1

instance model_smooth_one (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    SmoothOfRelativeDimension 1 (model hu hd).hom := by
  obtain ⟨hI,_,hS,hD,_⟩ := sexticCompletion_geometry (printed_degree hu hd) (printed_separable hu hd)
  let : AlgebraicGeometry.IsIntegral (model hu hd).left := hI
  let : Smooth (model hu hd).hom := hS
  exact SixJacobian.relative_dimension_one _ hD

instance model_geom [IsAlgClosed K] (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :
    GeometricallyIrreducible (model hu hd).hom := by
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (factor u d) (by decide : 0<2)
  let e := curveIso hu hd v hv
  let : IsIso e.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).inv))
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  have h : GeometricallyIrreducible (paperPullback K u).hom :=
    inferInstanceAs (GeometricallyIrreducible (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ K)))
  have sq : IsPullback e.inv.left (model hu hd).hom (paperPullback K u).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact e.inv.w⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) sq h

abbrev jacobian [IsAlgClosed K] (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) :=
  groupScheme K (model hu hd).hom

/-- Transport is along an actual isomorphism of group schemes, so it applies
to the entire endomorphism ring, including specializations with extra endomorphisms. -/
def jacobianIso [IsAlgClosed K] (hu : u ∉ ZInQ.contactSet) (hd : d^2=6) (v : K) (hv : v^2=factor u d) :
    (AbelianModel.baseChange (algebraMap ℚ K)).obj (SixJacobian.jacobian hu) ≅ jacobian hu hd :=
  IntegralPicard.paperJacobian_baseChangeIso K hu _ (curveIso hu hd v hv)

end
end ZInQBlueprint.PrintedModel
#print axioms ZInQBlueprint.PrintedModel.curveIso
#print axioms ZInQBlueprint.PrintedModel.model_geom
#print axioms ZInQBlueprint.PrintedModel.jacobianIso
