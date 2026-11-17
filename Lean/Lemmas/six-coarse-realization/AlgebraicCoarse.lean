import CoarseOrdinary

/-! The two algebraic forgetful maps in Baba--Granath §2.1 and §3.4
and their algebraic genus-two equation (Theorem 3.14). -/
open CategoryTheory AlgebraicGeometry Polynomial
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent AbelianModel BinaryCover CoarseConic
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The unmarked abelian variety underlying a coarse real-labelled class,
over the algebraic closure of the rational field. -/
def forgetLabel : ModuliClass → GroupIsoClass Qbar :=
  Quotient.map RealLabel.surface (by
    intro a b equivalent
    obtain ⟨f, _⟩ := equivalent
    exact ⟨f⟩)

/-- The algebraic forgetful map from the R₃ quotient to the full
Atkin--Lehner quotient on the affine chart (Corollary 3.11). The value E(j)
is the unmarked group of the polarized surface on the latter quotient. -/
def AlgebraicForgetfulMap {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (E : Qbar → GroupIsoClass Qbar) : Prop :=
  ∀ (t j : Qbar), j * (t^2+27) = -16 →
    forgetLabel (C.read (linePoint t ≫ chart)) = E j

/-- The unmarked Jacobian of the literal algebraic equation of Theorem 3.14. -/
def MestreClassAt (E : Qbar → GroupIsoClass Qbar) (j s : Qbar) : Prop :=
  ∀ (hd : (SexticCalibration.sextic s).natDegree = 6),
    let C := sexticCompletion (SexticCalibration.sextic s) hd
    ∀ [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom],
      groupClass (groupScheme Qbar C.hom) = E j

/-- Baba--Granath Theorem 3.14 at rational j with nonzero Mestre
determinant. One choice of the printed square root suffices. -/
def MestreEquation (E : Qbar → GroupIsoClass Qbar) : Prop :=
  ∀ j : ℚ, j*(64*j-81)*(27*j+16) ≠ 0 →
    ∃ s : Qbar, s^2 = -6*(j:Qbar) ∧ MestreClassAt E (j:Qbar) s

/-- Restrict the algebraic forgetful diagram to the six-contact family.
An ordinary representative at t and the Jacobian of the printed sextic at j
have the same unmarked group class. The isomorphism is over Qbar. -/
theorem unpolarized_of_mestre {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) {E : Qbar → GroupIsoClass Qbar}
    (algebraic : AlgebraicOrdinaryClasses C chart) (forget : AlgebraicForgetfulMap C chart E)
    (mestre : MestreEquation E) :
    UnpolarizedPrintedComparison (shimuraClassMap C chart) := by
  intro u hu ordinary
  obtain ⟨p, hp⟩ := fibre_nonempty hu
  have jt := j_quotient p
  rw [hp.y_square] at jt
  have h : (SixContact.J u : Qbar) * (p.quotientCoordinate^2 + 27) = -16 := by
    linear_combination jt/9
  obtain ⟨w, hw⟩ := algebraic p.quotientCoordinate (SixContact.J u) ordinary h
  let W : OrdinaryRepresentative (shimuraClassMap C chart) p :=
    ⟨w.surface, w.abelian, w.theta, w.principal, w.order, hw.symm⟩
  obtain ⟨s, hs, printed⟩ := mestre (SixContact.J u) (mestre_factors hu)
  let d := s / (r u : Qbar)
  have hr : (r u : Qbar) ≠ 0 := by exact_mod_cast (radical_units hu).1
  have hj : (SixContact.J u : Qbar) = -(r u : Qbar)^2 := by exact_mod_cast first_square u
  have hd : d^2 = 6 := by
    dsimp [d]
    rw [div_pow,hs,hj]
    field_simp [hr]
  have harg : PrintedModel.argument u d = s := by
    change s / (r u : Qbar) * (r u : Qbar) = s
    exact div_mul_cancel₀ s hr
  have literal : MestreClassAt E (SixContact.J u : Qbar) (PrintedModel.argument u d) :=
    harg.symm ▸ printed
  have curve := @literal (PrintedModel.printed_degree hu hd)
    (PrintedModel.model_proper hu hd) (PrintedModel.model_smooth_one hu hd)
    (PrintedModel.model_geom hu hd)
  have hW : groupClass w.surface = E (SixContact.J u : Qbar) := by
    change forgetLabel w.coarseClass = _
    rw [hw]
    exact forget _ _ h
  refine ⟨p,hp,W,d,hd,groupClass_eq.mp ?_⟩
  exact hW.trans (show groupClass (PrintedModel.jacobian hu hd) = _ from curve).symm

end
end ZInQBlueprint.ShimuraAtlas

#print axioms ZInQBlueprint.ShimuraAtlas.unpolarized_of_mestre
