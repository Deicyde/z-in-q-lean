import SignedTorsionField
import CompletedGoodReduction
import SignedThetaEndpoint

/-! The marked order supplies exactly the geometric multiplication needed by
the potentially-good-reduction theorem; rational real multiplication alone
would not give this conclusion. -/
open CategoryTheory AlgebraicGeometry NumberField
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.TorsionHeight
open NormalDescent QuaternionMarking GeometricMarking AbelianModel
open BinaryCover WeightedCurvePoints
noncomputable section

def QuaternionOrderOn (A : GroupScheme ℚ) : Prop :=
  ∃ e : LevelThree.O →+* End ((baseChange (algebraMap ℚ Qbar)).obj A), Function.Injective e

/-- The labelled order on the geometric printed fibre, transported through
the actual printed-model comparison. Its Galois descent is unnecessary here. -/
theorem geometric_order_of_printed {u : ℚ} {hu : u ∉ ZInQ.contactSet} (field : ThetaClass.PrintedField hu) :
    QuaternionOrderOn (SixJacobian.jacobian hu) := by
  obtain ⟨d,hd,v,hv,z,_,act,faithful,_⟩ := field
  let e := PrintedModel.jacobianIso hu hd v hv
  refine ⟨(endRingEquiv e.symm).toRingHom.comp act,(endRingEquiv e.symm).injective.comp faithful⟩

/-- Specialization of Laga--Schembri--Shnidman--Voight, Lemma 4.1, to
the specified order in the discriminant-six rational quaternion algebra. -/
def QuaternionPotentialReduction : Prop :=
  ∀ A : GroupScheme ℚ, IsAbelianScheme A → SmoothOfRelativeDimension 2 A.X.hom →
    QuaternionOrderOn A → ∀ (K : Type) [Field K] [NumberField K] (v : FinitePlace K), PotentialAt A v

/-- Field hypotheses for the stable height theorem, with honest abelian models
at every finite place, the actual six branch sections, and an explicit monic model. -/
theorem signed_height_field_good {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (field : ThetaClass.PrintedField hu) (pqm : QuaternionPotentialReduction)
    (st : SerreTateCriterion (SixJacobian.jacobian hu)) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      FullLevel (SixJacobian.jacobian hu) 12 K ∧
      (∀ v : FinitePlace K, GoodAt (SixJacobian.jacobian hu) v) ∧
      (paper K u false).Splits ∧ Nat.card (fixedSections K u) = 6 ∧
      Nonempty (fixedSections K u) ∧ OddPointChart (paper ℚ u false) K := by
  obtain ⟨K,kf,kn,level,sp,six,pt,chart⟩ := signed_height_field hu
  let := kf
  let := kn
  have potential := pqm _ (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu)
    (geometric_order_of_printed field) K
  exact ⟨K,kf,kn,level,good_everywhere_of_full_twelve _ st potential level,sp,six,pt,chart⟩

end
end ZInQBlueprint.TorsionHeight
#print axioms ZInQBlueprint.TorsionHeight.geometric_order_of_printed
#print axioms ZInQBlueprint.TorsionHeight.signed_height_field_good
