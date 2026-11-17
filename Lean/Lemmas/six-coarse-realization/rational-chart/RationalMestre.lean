import MestrePolynomial
import SixGaussianSection

/-! The rational points on both sheets of the real-labelled quotient and
the algebraic Mestre comparison on its rational ordinary open locus. -/
open CategoryTheory AlgebraicGeometry Polynomial NumberField
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent AbelianModel BinaryCover CoarseConic
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem rational_equation_of_fibre {u t : ℚ} {p : ConicPoint} (hp : FibrePoint u p)
    (slope : p.quotientCoordinate = (t : Qbar)) : SixContact.J u * (t^2 + 27) = -16 := by
  have e := j_quotient p
  rw [hp.y_square, slope] at e
  have h : (SixContact.J u : Qbar) * ((t : Qbar)^2 + 27) = -16 := by
    linear_combination e / 9
  exact_mod_cast h

theorem gaussian_rational_equation {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    SixContact.J u * ((4 * h u / r u)^2 + 27) = -16 := by
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) (by decide : 0 < 2)
  exact rational_equation_of_fibre (gaussianPoint_fibre i hi hu) (gaussianPoint_quotient i hi hu)

/-- Both rational signs lift. The single rational equation characterizes
exactly which slopes have a geometric lift in the specified fibre. -/
theorem rational_fibre_iff {u : ℚ} (hu : u ∉ ZInQ.contactSet) (t : ℚ) :
    (∃ p : ConicPoint, FibrePoint u p ∧ p.quotientCoordinate = (t : Qbar)) ↔
      SixContact.J u * (t^2 + 27) = -16 := by
  constructor
  · rintro ⟨p, hp, ht⟩
    exact rational_equation_of_fibre hp ht
  · intro given
    obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : Qbar) (by decide : 0 < 2)
    let a := gaussianPoint i hi hu
    have ha : FibrePoint u a := gaussianPoint_fibre i hi hu
    have hq : a.quotientCoordinate = ((4 * h u / r u : ℚ) : Qbar) := gaussianPoint_quotient i hi hu
    have hprod : SixContact.J u * t^2 = SixContact.J u * (4 * h u / r u)^2 := by
      linear_combination given - gaussian_rational_equation hu
    have heq := mul_left_cancel₀ (unmarked_range hu).2.ne hprod
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp heq with ht | ht
    · exact ⟨a, ha, by simpa only [ht] using hq⟩
    · refine ⟨otherGaussianSheet a, ⟨ha.y_square, ?_⟩, ?_⟩
      · change (-a.z)^2 = _
        rw [neg_sq]
        exact ha.z_square
      · rw [otherGaussianSheet_quotient, hq, ht, Rat.cast_neg]

/-- At least one of the two rational slopes admits a full-order ordinary
representative. The sheet can be chosen separately at every j. -/
def RationalOrdinaryClasses {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) : Prop :=
  ∀ (t j : ℚ), OutsideCM j → j*(64*j-81)*(27*j+16) ≠ 0 → j*(t^2+27) = -16 →
    ∃ v : ℚ, v^2 = t^2 ∧
      C.read (linePoint (v : Qbar) ≫ chart) ∈ Set.range OrdinarySurface.coarseClass

/-- Forgetting the mark on any represented rational ordinary slope gives
the unmarked algebraic group class at its full-quotient coordinate. -/
def RationalForgetfulMap {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (E : Qbar → GroupIsoClass Qbar) : Prop :=
  ∀ (t j : ℚ), OutsideCM j → j*(64*j-81)*(27*j+16) ≠ 0 → j*(t^2+27) = -16 →
    C.read (linePoint (t : Qbar) ≫ chart) ∈ Set.range OrdinarySurface.coarseClass →
    forgetLabel (C.read (linePoint (t : Qbar) ≫ chart)) = E (j : Qbar)

/-- The equation of Baba--Granath at ordinary rational j in the rational
image of the open R₃ chart. One choice of the square root suffices. -/
def RationalMestreEquation (E : Qbar → GroupIsoClass Qbar) : Prop :=
  ∀ j : ℚ, OutsideCM j → j*(64*j-81)*(27*j+16) ≠ 0 → (∃ t : ℚ, j*(t^2+27) = -16) →
    ∃ s : Qbar, s^2 = -6*(j : Qbar) ∧ MestreClassAt E (j : Qbar) s

theorem rationalMestre_of_mestre {E : Qbar → GroupIsoClass Qbar} (mestre : MestreEquation E) :
    RationalMestreEquation E := fun j _ admissible _ => mestre j admissible

private theorem printed_class_of_root {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    {E : Qbar → GroupIsoClass Qbar} {s : Qbar} (hs : s^2 = -6*(SixContact.J u : Qbar))
    (printed : MestreClassAt E (SixContact.J u : Qbar) s) :
    ∃ (d : Qbar) (hd : d^2 = 6), groupClass (PrintedModel.jacobian hu hd) = E (SixContact.J u : Qbar) := by
  let d := s / (r u : Qbar)
  have hr : (r u : Qbar) ≠ 0 := by exact_mod_cast (radical_units hu).1
  have hj : (SixContact.J u : Qbar) = -(r u : Qbar)^2 := by exact_mod_cast first_square u
  have hd : d^2 = 6 := by
    dsimp [d]
    rw [div_pow, hs, hj]
    field_simp [hr]
  have harg : PrintedModel.argument u d = s := div_mul_cancel₀ s hr
  have literal : MestreClassAt E (SixContact.J u : Qbar) (PrintedModel.argument u d) := harg.symm ▸ printed
  exact ⟨d, hd, @literal (PrintedModel.printed_degree hu hd) (PrintedModel.model_proper hu hd)
    (PrintedModel.model_smooth_one hu hd) (PrintedModel.model_geom hu hd)⟩

theorem unpolarized_of_rational_mestre {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) {E : Qbar → GroupIsoClass Qbar}
    (algebraic : RationalOrdinaryClasses C chart) (forget : RationalForgetfulMap C chart E)
    (mestre : RationalMestreEquation E) : UnpolarizedPrintedComparison (shimuraClassMap C chart) := by
  intro u hu ordinary
  have det := mestre_factors hu
  have ht := gaussian_rational_equation hu
  obtain ⟨v, hv, member⟩ := algebraic _ _ ordinary det ht
  have eqv : SixContact.J u * (v^2+27) = -16 := by rw [hv]; exact ht
  obtain ⟨p, hp, hq⟩ := (rational_fibre_iff hu v).mpr eqv
  obtain ⟨w, hw⟩ := member
  let W : OrdinaryRepresentative (shimuraClassMap C chart) p :=
    ⟨w.surface, w.abelian, w.theta, w.principal, w.order, by
      change C.read (linePoint p.quotientCoordinate ≫ chart) = w.coarseClass
      rw [hq, hw]⟩
  have hc : groupClass w.surface = E (SixContact.J u : Qbar) := by
    change forgetLabel w.coarseClass = _
    rw [hw]
    exact forget v _ ordinary det eqv ⟨w, hw⟩
  obtain ⟨s, hs, printed⟩ := mestre _ ordinary det ⟨v, eqv⟩
  obtain ⟨d, hd, hJ⟩ := printed_class_of_root hu hs printed
  exact ⟨p, hp, W, d, hd, groupClass_eq.mp (hc.trans hJ.symm)⟩

end
end ZInQBlueprint.ShimuraAtlas

namespace ZInQBlueprint.MinimalDiscriminant
open BinaryCover AbelianModel LocalJacobians QuaternionMarking GeometricMarking NormalDescent
open JacobianHeight JacobianConductor ThetaClass QuaternionLift TorsionHeight RosatiSigns ShimuraAtlas ZInQ
noncomputable section

theorem original_of_rational_mestre (hF : GroupScheme ℚ → ℝ) (hp : GlobalHeightFormula hF)
    (effective : EffectiveSurfaceHeight hF) (pqm : QuaternionPotentialReduction)
    (st : ∀ A : GroupScheme ℚ, IsAbelianScheme A → SerreTateCriterion A)
    (ddmm : ∀ (p : ℕ) [Fact p.Prime], TwoTripleGoodReduction p)
    (factor : CartierPrimeFactorization) {M : Over (Spec (.of ℚ))} (C : CoarseInterpretation M)
    (chart : Line ⟶ M) (E : Qbar → GroupIsoClass Qbar)
    (algebraic : RationalOrdinaryClasses C chart) (forget : RationalForgetfulMap C chart E)
    (mestre : RationalMestreEquation E) (uniquePol : UniqueD6Polarization) (primitive : PrimitivePrincipalExists)
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) :
    FrozenTarget :=
  original_of_ordinary_comparison hF hp effective pqm st ddmm factor (shimuraClassMap C chart)
    (unpolarized_of_rational_mestre C chart algebraic forget mestre) uniquePol primitive genus rank

end
end ZInQBlueprint.MinimalDiscriminant

#print axioms ZInQBlueprint.ShimuraAtlas.gaussian_rational_equation
#print axioms ZInQBlueprint.ShimuraAtlas.rational_fibre_iff
#print axioms ZInQBlueprint.ShimuraAtlas.unpolarized_of_rational_mestre
#print axioms ZInQBlueprint.MinimalDiscriminant.original_of_rational_mestre
