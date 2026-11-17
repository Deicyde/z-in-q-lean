import SixAbelField
import Nyll.AlgebraicCurves.Models.Points.AlgEquivPointPlaceCompHomEqAlgAutSmulPointPlace

/-! An isomorphism of the geometric curve acts on its normalized places by the
inverse pullback of rational functions. This also identifies the valuation ring
of every closed point with the actual local ring inside the scheme function field. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve GoodReductionJacobian
open AlgebraicCurves.Models.Proofs.CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace.AlgebraicCurve.CurveModel.ModelIndepSol
open FunctionFieldPull
namespace ZInQBlueprint.SixAbelMap
noncomputable section
variable {K : Type} [Field K] [IsAlgClosed K] {C : Over (Spec (.of K))}
  [AlgebraicGeometry.IsIntegral C.left]
local instance : Algebra K C.left.functionField := (baseToFunctionField C.hom).toAlgebra

def pullIso {X Y : Scheme} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (e : X ≅ Y) : Y.functionField ≃+* X.functionField := equivOfIso e

omit [IsAlgClosed K] in
theorem normalized_ffEquiv (N : PlaceModel C) : N.model.ffEquiv = pullIso N.iso := by
  ext x
  obtain ⟨U,hU,s,hx⟩ := C.left.presheaf.exists_germ_eq x
  let : Nonempty U := ⟨⟨genericPoint C.left,hU⟩⟩
  let : Nonempty (N.iso.hom ⁻¹ᵁ U) :=
    ⟨⟨N.iso.inv (genericPoint C.left),by
      change N.iso.hom (N.iso.inv (genericPoint C.left)) ∈ U
      simpa using hU⟩⟩
  have hx' : C.left.germToFunctionField U s = x := hx
  rw [←hx']
  have h := pull_germ N.iso.hom (specializes_of_iso N.iso) U hU s
  conv_lhs => rw [←N.germs U s, RingEquiv.apply_symm_apply]
  exact h.symm

variable (N : PlaceModel C)
def normalizedPlace : (base K ⟶ C) ≃ Place K C.left.functionField :=
  letI := N.curve
  pointPlace C N.model N.iso N.hbase

theorem normalized_valuationRing (p : base K ⟶ C) :
    ((normalizedPlace N p).toValuationSubring : Set C.left.functionField) =
      (algebraMap (C.left.presheaf.stalk (p.left.base (IsLocalRing.closedPoint K))) C.left.functionField).range := by
  let z : {q : Spec (.of K) ⟶ N.model.C // q ≫ N.model.toBase = 𝟙 _} :=
    ⟨p.left ≫ N.iso.inv, by rw [←N.hbase,Category.assoc,N.iso.inv_hom_id_assoc]; exact p.w⟩
  have h := coe_toValuationSubring_pointEquivPlace N.model z
  rw [normalized_ffEquiv] at h
  have he := image_equivOfIso_symm_range_stalk N.iso (z.1.base (IsLocalRing.closedPoint K))
  have hz : N.iso.hom.base (z.1.base (IsLocalRing.closedPoint K)) =
      p.left.base (IsLocalRing.closedPoint K) := by
    change ((p.left ≫ N.iso.inv) ≫ N.iso.hom).base _ = _
    simp
  rw [hz] at he
  exact h.trans he

/-- Covariant action on places. The inverse in the pullback is essential. -/
def functionAction (e : C ≅ C) : C.left.functionField ≃ₐ[K] C.left.functionField :=
  let d : C.left ≅ C.left := (Over.forget _).mapIso e
  AlgEquiv.ofRingEquiv (f := (pullIso d).symm) (fun a => by
    apply (pullIso d).injective
    rw [RingEquiv.apply_symm_apply]
    exact (equivOfIso_baseToFunctionField d C.hom C.hom e.hom.w a).symm)

theorem normalizedPlace_action (e : C ≅ C) (p : base K ⟶ C) :
    normalizedPlace N (p ≫ e.hom) =
      SemilinearAut.ofAlgAut (functionAction e) • normalizedPlace N p := by
  apply Place.ext
  apply SetLike.coe_injective
  rw [SemilinearAut.smul_toValuationSubring,ValuationSubring.coe_pointwise_smul,←Set.image_smul,
    normalized_valuationRing,normalized_valuationRing]
  exact (image_equivOfIso_symm_range_stalk (show C.left ≅ C.left from (Over.forget _).mapIso e)
    (p.left.base (IsLocalRing.closedPoint K))).symm

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.normalized_ffEquiv
#print axioms ZInQBlueprint.SixAbelMap.normalized_valuationRing
#print axioms ZInQBlueprint.SixAbelMap.normalizedPlace_action
