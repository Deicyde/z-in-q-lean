import PolarizedAbelAction

/-! The marked representative is needed only on the ordinary part of the
realized rational discriminant-six locus. Its polarization is transported
to the signed Jacobian before taking a Galois correction. -/

open CategoryTheory AlgebraicGeometry
open scoped ZInQBlueprint.NormalDescent

namespace ZInQBlueprint.AbelComparison
open BinaryCover AbelianModel NormalDescent QuaternionMarking CMRepair GeometricMarking
open QuaternionLift ShimuraAtlas CoarseConic CanonicalTheta ThetaClass RosatiSigns
open LocalJacobians JacobianHeight JacobianConductor TorsionHeight MinimalDiscriminant
open WeierstrassCoordinates SixAbelMap ZInQ

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The weighted Igusa point has a polarized marked representative with the
indicated field of moduli. Only represented rational parameters outside the
CM table are required. -/
def OrdinaryMarkedFields (read : IgusaCoordinates → ModuliClass) : Prop :=
  ∀ j : ℚ, RealizedD6Point j → j*(64*j-81)*(27*j+16) ≠ 0 → OutsideCM j →
    ∃ (A : GroupScheme Qbar) (L : A.X.left.Modules) (z : Qbar),
      moduliClass (polarizedLabel A L) = read (bgCoordinates j) ∧
      z^2 = ((-(27*j+16)/j : ℚ) : Qbar) ∧ LabelledModuli A L z

theorem signed_labelled_from_ordinary {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) (fields : OrdinaryMarkedFields read)
    {u : ℚ} (hu : u ∉ contactSet) :
    ∃ z : Qbar, z^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar) ∧
      LabelledModuli (geometricJacobian hu) (signedThetaLine hu) z := by
  obtain ⟨A,L,z,hA,hz,marked⟩ := fields _ (signed_realizes hu) (mestre_factors hu)
    (fun _ ha => avoids_cm_table hu ha)
  obtain ⟨e,polar⟩ := polarizedClass_eq.mp (hA.trans (signed_class_of_igusa classification hu).symm)
  exact ⟨z,hz,labelled_transport e polar z marked⟩

private theorem marked_radicand_square {u : ℚ} (hu : u ∉ contactSet) :
    IsSquare (-(27*SixContact.J u+16)/SixContact.J u) := by
  refine ⟨4*h u/r u, ?_⟩
  rw [show -(27*SixContact.J u+16) = -27*SixContact.J u-16 by ring, second_square, first_square]
  field_simp [(radical_units hu).1]

/-- The same labelled quaternion action compares all conjugates of the rational
Jacobian. The action on divisor differences follows from the polarized
comparison even though the Abel base point can move. -/
theorem signed_abel_of_labelled (torelli : PointedDeterminantTorelli)
    (factor : CartierPrimeFactorization) {u : ℚ} (hu : u ∉ contactSet)
    {z : Qbar} (hz : z^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar))
    (marked : LabelledModuli (geometricJacobian hu) (signedThetaLine hu) z) :
    RationalAbelMarking (SixJacobian.jacobian hu) (rigidMorphism hu) z := by
  let e := Iso.refl (geometricJacobian hu)
  let L := signedThetaLine hu
  have rational := rational_of_prime_factorization hu factor (signed_deck_abel_support hu)
  have transported := labelled_transport e (sameClass_transport (underlying e) L) z marked
  obtain ⟨act, inj, comparisons⟩ := classMarking_of_labelled_field e L rational z hz transported
  refine ⟨act, inj, ?_⟩
  intro σ _
  obtain ⟨φ, gen, pol⟩ := comparisons (marked_radicand_square hu) σ
  refine ⟨φ, gen, ?_⟩
  have h := signed_differences_of_polarized torelli hu (correctionIso e σ φ)
    (correction_sameClass e σ φ L pol)
  simpa [e, correctionIso, rationalOnPrinted] using h

/-- The bounded polynomial using the marked field on the ordinary locus. -/
theorem original_of_ordinary_polarized_comparison (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) (read : IgusaCoordinates → ModuliClass)
    (classification : PolarizedIgusaClassification read) (fields : OrdinaryMarkedFields read)
    (torelli : PointedDeterminantTorelli) (coordinates : VoightCoordinateFormula)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) : FrozenTarget := by
  apply original_of_signed_actions hF hp effective pqm st ddmm _ genus rank
  intro u hu
  obtain ⟨z,hz,marked⟩ := signed_labelled_from_ordinary classification fields hu
  have abel := signed_abel_of_labelled torelli factor hu hz marked
  have rm := (actions_of_rational_abel_marking hu (curveCoordinateLifts_of_voight coordinates hu) hz abel).2
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq (6 : Qbar) (by decide : 0 < 2)
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (PrintedModel.factor u d) (by decide : 0 < 2)
  let g := PrintedModel.jacobianIso hu hd v hv
  exact ⟨⟨d,hd,v,hv,z,hz,labelled_transport g (sameClass_transport (underlying g) (signedThetaLine hu)) z marked⟩,rm⟩

end
end ZInQBlueprint.AbelComparison

#print axioms ZInQBlueprint.AbelComparison.signed_labelled_from_ordinary
#print axioms ZInQBlueprint.AbelComparison.signed_abel_of_labelled
#print axioms ZInQBlueprint.AbelComparison.original_of_ordinary_polarized_comparison
