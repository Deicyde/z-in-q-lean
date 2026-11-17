import SixShimuraEndpoint
import SignedAutodualityInjective

/-! Rotger's principal-polarization count permits a comparison that initially
forgets the polarizations. The general theorem is isolated from the
geometric realization of the maximal order. -/
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.QuaternionLift
open ThetaClass QuaternionMarking NormalDescent AbelianModel GeometricMarking CanonicalTheta
open DeterminantAutoduality
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- In characteristic zero a nonzero section and a trivial translation
kernel characterize an effective line inducing a principal polarization. -/
def EffectivePrincipal {A : GroupScheme Qbar} (ab : IsAbelianScheme A)
    (L : A.X.left.Modules) : Prop :=
  ∃ hL : L.IsInvertible, (∃ s : 𝟙_ A.X.left.Modules ⟶ L, s ≠ 0) ∧
    Function.Injective (polarization ab L hL)

/-- The isomorphism-class count for the maximal discriminant-six order,
with Milne's criterion to recognize the principal lines on the two objects. -/
def UniqueD6Polarization : Prop :=
  ∀ {A B : GroupScheme Qbar} (ab : IsAbelianScheme A) (bb : IsAbelianScheme B)
    (L : A.X.left.Modules) (M : B.X.left.Modules),
    SmoothOfRelativeDimension 2 B.X.hom → Nonempty (LevelThree.O ≃+* End A) → EffectivePrincipal ab L → EffectivePrincipal bb M →
    Nonempty (A ≅ B) → ∃ e : A ≅ B, SameClass A.X.hom L (pullModule (underlying e).hom M)

theorem signed_effective_principal {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    EffectivePrincipal (isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu))
      (signedThetaLine hu) :=
  ⟨signedThetaLine_invertible hu,⟨_,signedThetaSection_ne_zero hu⟩,signedPolarization_injective hu⟩

/-- At a non-CM point the specified Shimura order is the full geometric
endomorphism ring. An isomorphism to the curve's Jacobian
may now forget the line, the order action, and all Galois choices. -/
structure OrdinaryRepresentative (U : ShimuraClassMap) (p : ConicPoint) where
  surface : GroupScheme Qbar
  abelian : IsAbelianScheme surface
  theta : surface.X.left.Modules
  principal : EffectivePrincipal abelian theta
  order : LevelThree.O ≃+* End surface
  represents : U.value p = moduliClass (markedObject surface theta order.toRingHom)

def UnpolarizedPrintedComparison (U : ShimuraClassMap) : Prop :=
  ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet), OutsideCM (SixContact.J u) →
    ∃ (p : ConicPoint), FibrePoint u p ∧
    ∃ (w : OrdinaryRepresentative U p) (d : Qbar) (hd : d^2 = 6),
      Nonempty (w.surface ≅ PrintedModel.jacobian hu hd)

theorem models_of_unpolarized (U : ShimuraClassMap) (uniquePol : UniqueD6Polarization)
    (models : UnpolarizedPrintedComparison U) : PrintedComparison U := by
  intro u hu off
  obtain ⟨p,hp,w,d,hd,⟨f⟩⟩ := models u hu off
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (PrintedModel.factor u d) (by decide : 0 < 2)
  let g := PrintedModel.jacobianIso hu hd v hv
  let : SmoothOfRelativeDimension 2 (SixJacobian.jacobian hu).X.hom := SixJacobian.jacobian_dimension_two hu
  have dim : SmoothOfRelativeDimension 2 (geometricJacobian hu).X.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 2 (Limits.pullback.snd
      (SixJacobian.jacobian hu).X.hom (Spec.map (CommRingCat.ofHom (algebraMap ℚ Qbar)))))
  obtain ⟨e,polar⟩ := uniquePol w.abelian
    (isAbelianScheme_baseChange (algebraMap ℚ Qbar) (SixJacobian.isAbelian hu))
    w.theta (signedThetaLine hu) dim ⟨w.order⟩ w.principal (signed_effective_principal hu)
    ⟨f ≪≫ g.symm⟩
  have trans := (sameClass_transport (underlying g) (signedThetaLine hu)).pull
    (underlying e).hom.left (underlying e).hom.w
  let assoc := (Scheme.Modules.pullbackComp (underlying e).hom.left (underlying g).hom.left).app
    (printedBundle g (signedThetaLine hu))
  refine ⟨p,hp,d,hd,v,hv,⟨?_⟩⟩
  exact ⟨w.surface,w.theta,w.order.toRingHom,w.order.injective,w.represents,e ≪≫ g,
    polar.trans (trans.congr (Iso.refl _) assoc)⟩

theorem printedField_of_unpolarized (U : ShimuraClassMap) (uniquePol : UniqueD6Polarization)
    (models : UnpolarizedPrintedComparison U) {u : ℚ} (hu : u ∉ ZInQ.contactSet) : PrintedField hu :=
  printedField_of_shimura U (models_of_unpolarized U uniquePol models) hu

end
end ZInQBlueprint.QuaternionLift
#print axioms ZInQBlueprint.QuaternionLift.signed_effective_principal
#print axioms ZInQBlueprint.QuaternionLift.models_of_unpolarized
#print axioms ZInQBlueprint.QuaternionLift.printedField_of_unpolarized
