import SixPolarizedIgusa

/-! The two quotient maps retain the principal polarization. Once the
ordinary surface has its defining Rosati form, one obtains the bounded
polynomial theorem directly from its polarized Igusa class. -/
open CategoryTheory AlgebraicGeometry NumberField
namespace ZInQBlueprint.ShimuraAtlas
open BinaryCover AbelianModel NormalDescent QuaternionLift GeometricMarking CoarseConic
open ThetaClass QuaternionMarking CanonicalTheta RosatiSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- The polarized forgetful map on the rational ordinary locus, in the
five arithmetic Igusa coordinates of Baba--Granath Proposition 3.6. -/
def RationalPolarizedForgetful {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (read : IgusaCoordinates → ModuliClass) : Prop :=
  ∀ (t j : ℚ), OutsideCM j → j*(64*j-81)*(27*j+16) ≠ 0 → j*(t^2+27) = -16 →
    C.read (linePoint (t : Qbar) ≫ chart) ∈ Set.range OrdinarySurface.coarseClass →
    forgetOrder (C.read (linePoint (t : Qbar) ≫ chart)) = read (bgCoordinates j)

/-- The ordinary polarized Shimura moduli problem with its actual order
and Rosati action, on one of the two rational R₃ slopes. -/
def RationalRosatiClasses {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) : Prop :=
  ∀ (t j : ℚ), OutsideCM j → j*(64*j-81)*(27*j+16) ≠ 0 → j*(t^2+27) = -16 →
    ∃ v : ℚ, v^2 = t^2 ∧ ∃ w : OrdinarySurface,
      w.coarseClass = C.read (linePoint (v : Qbar) ≫ chart) ∧ IsRosatiPresentation w.theta w.order

theorem ordinary_of_rosati_classes {M : Over (Spec (.of ℚ))} {C : CoarseInterpretation M}
    {chart : Line ⟶ M} (h : RationalRosatiClasses C chart) : RationalOrdinaryClasses C chart := by
  intro t j o det v
  obtain ⟨s,hs,w,hw,_⟩ := h t j o det v
  exact ⟨s,hs,w,hw⟩

private theorem lift_with_polarization {M : Over (Spec (.of ℚ))} {C : CoarseInterpretation M}
    {chart : Line ⟶ M} {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) (forget : RationalPolarizedForgetful C chart read)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) (ordinary : OutsideCM (SixContact.J u))
    {v : ℚ} (hv : SixContact.J u * (v^2+27) = -16)
    (w : OrdinarySurface) (hw : w.coarseClass = C.read (linePoint (v : Qbar) ≫ chart)) :
    ∃ p : ConicPoint, FibrePoint u p ∧ (shimuraClassMap C chart).value p = w.coarseClass ∧
      ∃ e : w.surface ≅ geometricJacobian hu, Compatible e w.theta (signedThetaLine hu) := by
  obtain ⟨p,hp,hq⟩ := (rational_fibre_iff hu v).mpr hv
  refine ⟨p,hp,?_,polarizedClass_eq.mp ?_⟩
  · change C.read (linePoint p.quotientCoordinate ≫ chart) = w.coarseClass
    rw [hq,hw]
  · change forgetOrder w.coarseClass = _
    rw [hw,forget _ _ ordinary (mestre_factors hu) hv ⟨w,hw⟩]
    exact (signed_class_of_igusa classification hu).symm

private def transportToPrinted {U : ShimuraClassMap} {p : ConicPoint} {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (w : OrdinarySurface) (hw : U.value p = w.coarseClass)
    (e : w.surface ≅ geometricJacobian hu) (he : Compatible e w.theta (signedThetaLine hu))
    {d : Qbar} (hd : d^2=6) (v : Qbar) (hv : v^2=PrintedModel.factor u d) :
    PolarizedRealization U p (PrintedModel.jacobian hu hd)
      (printedBundle (PrintedModel.jacobianIso hu hd v hv) (signedThetaLine hu)) := by
  let g := PrintedModel.jacobianIso hu hd v hv
  exact ⟨w.surface,w.theta,w.order.toRingHom,w.order.injective,hw,e ≪≫ g,
    compatible_comp he (sameClass_transport (underlying g) (signedThetaLine hu))⟩

/-- The ordinary representative and the genuine signed theta determinant
have equal polarized class. Its transport to a printed model uses no
uniqueness theorem for principal polarizations. -/
theorem printed_of_polarized_igusa {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) (ordinary : RationalOrdinaryClasses C chart)
    (forget : RationalPolarizedForgetful C chart read) : PrintedComparison (shimuraClassMap C chart) := by
  intro u hu off
  have eqn := gaussian_rational_equation hu
  obtain ⟨v,hv,w,hw⟩ := ordinary _ _ off (mestre_factors hu) eqn
  obtain ⟨p,hp,rep,e,pol⟩ := lift_with_polarization classification forget hu off (by rw [hv]; exact eqn) w hw
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq (6 : Qbar) (by decide : 0<2)
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (PrintedModel.factor u d) (by decide : 0<2)
  exact ⟨p,hp,d,hd,z,hz,⟨transportToPrinted hu w rep e pol hd z hz⟩⟩

theorem rosati_of_polarized_igusa {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) {read : IgusaCoordinates → ModuliClass}
    (classification : PolarizedIgusaClassification read) (ordinary : RationalRosatiClasses C chart)
    (forget : RationalPolarizedForgetful C chart read) : RosatiPrintedComparison (shimuraClassMap C chart) := by
  intro u hu off
  have eqn := gaussian_rational_equation hu
  obtain ⟨v,hv,w,hw,ros⟩ := ordinary _ _ off (mestre_factors hu) eqn
  obtain ⟨p,hp,rep,e,pol⟩ := lift_with_polarization classification forget hu off (by rw [hv]; exact eqn) w hw
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq (6 : Qbar) (by decide : 0<2)
  obtain ⟨z,hz⟩ := IsAlgClosed.exists_pow_nat_eq (PrintedModel.factor u d) (by decide : 0<2)
  refine ⟨p,hp,d,hd,z,hz,⟨⟨transportToPrinted hu w rep e pol hd z hz,w.order.surjective,?_⟩⟩⟩
  change IsRosatiPresentation w.theta (RingEquiv.ofBijective w.order.toRingHom _)
  have equal : RingEquiv.ofBijective w.order.toRingHom w.order.bijective = w.order :=
    RingEquiv.ext fun _ => rfl
  rw [equal]
  exact ros

end
end ZInQBlueprint.ShimuraAtlas

namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section

theorem original_of_polarized_igusa (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (read : IgusaCoordinates → ModuliClass)
    (classification : PolarizedIgusaClassification read) (ordinary : RationalRosatiClasses C chart)
    (forget : RationalPolarizedForgetful C chart read)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) : FrozenTarget :=
  original_of_rosati_comparison hF hp effective pqm st ddmm factor (shimuraClassMap C chart)
    (rosati_of_polarized_igusa C chart classification ordinary forget) genus rank

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.ShimuraAtlas.ordinary_of_rosati_classes
#print axioms ZInQBlueprint.ShimuraAtlas.printed_of_polarized_igusa
#print axioms ZInQBlueprint.ShimuraAtlas.rosati_of_polarized_igusa
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_polarized_igusa
