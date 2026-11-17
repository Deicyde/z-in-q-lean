import RosatiMarkedAction
import DiscriminantSixPair
import SixUnpolarizedQM
import CartierMultiplicity

/-! The original non-CM unpolarized comparison suffices. A primitive
compatible principal line on any full-order abelian surface is carried to
the signed determinant using the one principal polarization class for D=6. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.RosatiSigns
open LevelThree QuaternionMarking ThetaClass QuaternionLift NormalDescent AbelianModel
open GeometricMarking CanonicalTheta JacobianHeight
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Voight, (43.6.13), 43.6.16–23: a principal line on the QM surface
coming from the integral trace form. For this implication its (1,mu)
matrix coefficient on an NS-preserving change of coordinates suffices. -/
def PrimitivePrincipalExists : Prop :=
  ∀ {A : GroupScheme Qbar} (ab : IsAbelianScheme A), SmoothOfRelativeDimension 2 A.X.hom →
    ∀ order : O ≃+* End A, ∃ L : A.X.left.Modules, EffectivePrincipal ab L ∧
      ∀ a : A ≅ A, Compatible a L L →
        let q := embed (order.symm (End.of a.hom))
        tracePair q (q*mu) = tracePair 1 mu

theorem rosati_of_primitive_pair {A : GroupScheme Qbar} (L : A.X.left.Modules)
    (order : O ≃+* End A)
    (pair : ∀ a : A ≅ A, Compatible a L L →
      let q := embed (order.symm (End.of a.hom))
      tracePair q (q*mu) = tracePair 1 mu) :
    IsRosatiPresentation L order := by
  intro a polar
  exact (polarized_order_iff _).mpr ((normalized_pair_iff _).mp (pair a polar))

theorem signed_of_full_order {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (order : O ≃+* End (geometricJacobian hu)) :
    ∀ a : geometricJacobian hu ≅ geometricJacobian hu,
      Compatible a (signedThetaLine hu) (signedThetaLine hu) →
        End.of a.hom = 1 ∨ End.of a.hom = -1 := by
  let ab := isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu)
  let : SmoothOfRelativeDimension 2 (SixJacobian.jacobian hu).X.hom := SixJacobian.jacobian_dimension_two hu
  have dim : SmoothOfRelativeDimension 2 (geometricJacobian hu).X.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 2 (Limits.pullback.snd
      (SixJacobian.jacobian hu).X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))))
  obtain ⟨L,principal,pair⟩ := primitive ab dim order
  obtain ⟨f,hf⟩ := uniquePol ab ab L (signedThetaLine hu) dim ⟨order⟩
    principal (signed_effective_principal hu) ⟨Iso.refl _⟩
  exact signed_of_comparison (rosati_of_primitive_pair L order pair) f hf

/-- Uses the canonical polarization already included on the Shimura representative. -/
theorem marked_of_shimura (U : ShimuraClassMap) (models : RosatiPrintedComparison U)
    (factor : CartierPrimeFactorization) {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    Nonempty (MarkedAction u (SixJacobian.jacobian hu)) :=
  marked_of_shimura_rational U models hu (rational_of_prime_factorization hu factor (signed_deck_abel_support hu))

/-- An ordinary unpolarized Shimura comparison supplies the full geometric
endomorphism ring of the signed Jacobian, independently of choice of theta. -/
theorem full_order_of_unpolarized (U : ShimuraClassMap) (models : UnpolarizedPrintedComparison U)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) : Nonempty (O ≃+* End (geometricJacobian hu)) := by
  obtain ⟨_,_,w,d,hd,⟨f⟩⟩ := models u hu (fun _ ha => avoids_cm_table hu ha)
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (PrintedModel.factor u d) (by decide : 0 < 2)
  exact ⟨w.order.trans (endRingEquiv (f ≪≫ (PrintedModel.jacobianIso hu hd v hv).symm))⟩

/-- The earlier printed-model hypothesis is unchanged. No Torelli, Abel
immersion, or coordinate-lift premise is needed for the rational marking. -/
theorem marked_of_unpolarized (U : ShimuraClassMap) (models : UnpolarizedPrintedComparison U)
    (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (factor : CartierPrimeFactorization) {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    Nonempty (MarkedAction u (SixJacobian.jacobian hu)) := by
  obtain ⟨order⟩ := full_order_of_unpolarized U models hu
  have aut := signed_of_full_order hu uniquePol primitive order
  obtain ⟨d,hd,v,hv,z,hz,field⟩ := printedField_of_unpolarized U uniquePol models hu
  let e := PrintedModel.jacobianIso hu hd v hv
  let L := signedThetaLine hu
  have rational := rational_of_prime_factorization hu factor (signed_deck_abel_support hu)
  exact marked_of_class_signs hu e L (classMarking_of_labelled_field e L rational z hz field) aut

end
end ZInQBlueprint.RosatiSigns
#print axioms ZInQBlueprint.RosatiSigns.rosati_of_primitive_pair
#print axioms ZInQBlueprint.RosatiSigns.signed_of_full_order
#print axioms ZInQBlueprint.RosatiSigns.marked_of_shimura
#print axioms ZInQBlueprint.RosatiSigns.full_order_of_unpolarized
#print axioms ZInQBlueprint.RosatiSigns.marked_of_unpolarized
