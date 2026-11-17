import IgusaPolynomial

/-! A marked field of moduli on the realized part of the discriminant-six
Igusa locus suffices for both actions on the signed Jacobian. -/
open CategoryTheory AlgebraicGeometry Polynomial NumberField
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ShimuraAtlas
open BinaryCover AbelianModel NormalDescent QuaternionLift GeometricMarking CoarseConic
open ThetaClass QuaternionMarking CanonicalTheta RosatiSigns JacobianHeight
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Some rational smooth sextic represents the specified weighted Igusa point. -/
def RealizedD6Point (j : ℚ) : Prop :=
  ∃ (f : ℚ[X]) (b : ℚ), f.natDegree = 6 ∧ f.Separable ∧ b ≠ 0 ∧
    IgusaCoordinates.ofSextic f = (bgCoordinates j).scale b

theorem signed_realizes {u : ℚ} (hu : u ∉ ZInQ.contactSet) : RealizedD6Point (SixContact.J u) := by
  obtain ⟨b,hb,eq⟩ := signed_coordinates hu
  exact ⟨paper ℚ u false,b,OddModel.paper_degree hu,(paper_chart_regular ℚ hu false).2,hb,eq⟩

/-- The polarized QM representative in the image of the discriminant-six
Shimura curve, with field of moduli of its distinguished R₃ action.
Baba–Granath, §§2.1 and 3.1, Proposition 3.6 and Theorem 3.17. -/
def BGMarkedFields (read : IgusaCoordinates → ModuliClass) : Prop :=
  ∀ j : ℚ, RealizedD6Point j → j*(64*j-81)*(27*j+16) ≠ 0 →
  ∃ (A : GroupScheme Qbar) (L : A.X.left.Modules) (z : Qbar),
    moduliClass (polarizedLabel A L) = read (bgCoordinates j) ∧
    z^2 = ((-(27*j+16)/j : ℚ) : Qbar) ∧ LabelledModuli A L z

/-- Only the scalarity of automorphisms of the given canonical polarization
is used to descend the R₃ generator. -/
def SignedPolarizedSigns : Prop :=
  ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet), ∀ a : geometricJacobian hu ≅ geometricJacobian hu,
    Compatible a (signedThetaLine hu) (signedThetaLine hu) → End.of a.hom = 1 ∨ End.of a.hom = -1

/-- Transfer the published marked field from a representative of the
Igusa class to the signed geometric Jacobian and its chosen printed model. -/
theorem printedField_of_marked_igusa {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) (fields : BGMarkedFields read)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) : PrintedField hu := by
  obtain ⟨A,L,z,hA,hz,marked⟩ := fields _ (signed_realizes hu) (mestre_factors hu)
  obtain ⟨e,polar⟩ := polarizedClass_eq.mp (hA.trans (signed_class_of_igusa classification hu).symm)
  have signed := labelled_transport e polar z marked
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq (6 : Qbar) (by decide : 0 < 2)
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (PrintedModel.factor u d) (by decide : 0 < 2)
  let g := PrintedModel.jacobianIso hu hd v hv
  exact ⟨d,hd,v,hv,z,hz,labelled_transport g (sameClass_transport (underlying g) (signedThetaLine hu)) z signed⟩

/-- A faithful marked quaternion action and the rational R₃ endomorphism on
the same signed Jacobian. No maximality assertion on its endomorphism ring
is used by the Galois descent. -/
theorem actions_of_marked_igusa {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) (fields : BGMarkedFields read)
    (signs : SignedPolarizedSigns) (factor : CartierPrimeFactorization)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    PrintedField hu ∧ RationalRM (SixJacobian.jacobian hu) := by
  have field := printedField_of_marked_igusa classification fields hu
  obtain ⟨d,hd,v,hv,z,hz,moduli⟩ := field
  let g := PrintedModel.jacobianIso hu hd v hv
  have rational := rational_of_prime_factorization hu factor (signed_deck_abel_support hu)
  have marked := classMarking_of_labelled_field g (signedThetaLine hu) rational z hz moduli
  exact ⟨⟨d,hd,v,hv,z,hz,moduli⟩,(marked_of_class_signs hu g _ marked (signs u hu)).elim rationalRM_of_marked⟩

end
end ZInQBlueprint.ShimuraAtlas

namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section

theorem original_of_marked_igusa (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) (read : IgusaCoordinates → ModuliClass)
    (classification : PolarizedIgusaClassification read) (fields : BGMarkedFields read)
    (signs : SignedPolarizedSigns)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) : FrozenTarget :=
  original_of_signed_actions hF hp effective pqm st ddmm
    (fun _ hu => actions_of_marked_igusa classification fields signs factor hu) genus rank

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.ShimuraAtlas.signed_realizes
#print axioms ZInQBlueprint.ShimuraAtlas.printedField_of_marked_igusa
#print axioms ZInQBlueprint.ShimuraAtlas.actions_of_marked_igusa
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_marked_igusa
