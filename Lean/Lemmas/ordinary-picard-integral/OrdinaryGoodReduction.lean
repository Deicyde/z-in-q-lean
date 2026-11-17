import IntegralSheaf
import UnpointedBaseChange

/-! Good reduction of the actual rational Jacobian at ordinary primes of the signed sextic. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve AlgebraicGeometry.GeneralizedJacobian GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed IsDiscreteValuationRing
open ZInQBlueprint.BinaryCover ZInQBlueprint.PrimitiveParameters ZInQBlueprint.IntegralSextic
open ZInQBlueprint.RationalClusters ZInQBlueprint.GlobalTwist
namespace ZInQBlueprint.IntegralPicard
noncomputable section

/-- A curve over a field identified with the scalar extension of the paper curve has the
correct unpointed Jacobian over that field, as a commutative group scheme. -/
def paperJacobian_baseChangeIso (L : Type) [Field L] [CharZero L] {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (D : Over (Spec (.of L))) [IsProper D.hom]
    [SmoothOfRelativeDimension 1 D.hom] [GeometricallyIrreducible D.hom]
    (e : paperPullback L u ≅ D) :
    (AbelianModel.baseChange (algebraMap ℚ L)).obj (SixJacobian.jacobian hu) ≅ groupScheme L D.hom := by
  let C := paperModel ℚ u
  let : IsProper C.hom := paper_proper ℚ u
  let : GeometricallyIntegral C.hom := geometricallyIntegral_paperModel hu
  let : Smooth C.hom := smooth_paperModel hu
  let : AlgebraicGeometry.IsIntegral C.left := paper_reglued_integral ℚ hu
  let : SmoothOfRelativeDimension 1 C.hom := SixJacobian.relative_dimension_one C.hom (paper_dimension ℚ u)
  exact unpointed_baseChangeIso C D e

variable (p : ℕ) [Fact p.Prime]
local notation "Zp" => ℤ_[p]
local notation "Qp" => ℚ_[p]

private theorem units_of_coordinates {u : ℚ} (hp : 7≤p)
    (hF : IsUnit (F p u)) (hG : IsUnit (G p u)) {t a : Zpˣ}
    (H : Coordinates p u (t:Zp) 1 (a:Zp)) :
    IsUnit (OrdinaryModel.scale p u a) ∧ IsUnit ((t:Zp)^2+27) := by
  have ds : IsUnit (delta u:Zp) := addVal_eq_zero_iff.mp ((ordinary p u (addVal_eq_zero_iff.mpr hF)).padic_val)
  have six : IsUnit (6:Zp) := unit_nat p 6 (by decide) (by omega)
  refine ⟨(((six.neg.mul ds).mul hG).mul isUnit_one).mul (a.isUnit.pow 2),?_⟩
  cases H with
  | second hv => norm_num at hv
  | first hv ha ht =>
    have hg : (G p u)^3=27*(left p u)^2+(right p u)^2 := (parameter_identities _ _).2.1
    rw [←ht,←ha] at hg
    have e : (a:Zp)^2*((t:Zp)^2+27)=(G p u)^3 := by linear_combination -hg
    exact isUnit_of_mul_isUnit_right (e ▸ hG.pow 3)

/-- The ordinary model supplies an integral Picard-zero abelian scheme whose generic
fibre is the base change of the already constructed rational Jacobian. -/
theorem ordinary_goodReduction {u : ℚ} (hu : u ∉ ZInQ.contactSet) (hp : 7≤p)
    (hF : IsUnit (F p u)) (hG : IsUnit (G p u)) :
    AbelianModel.GoodReductionAt p (SixJacobian.jacobian hu) := by
  obtain ⟨t,a,hc,_,hpr,hgi,⟨e⟩⟩ := OrdinaryModel.ordinary_curve_model p hu hp hF hG
  obtain ⟨hs,hD⟩ := units_of_coordinates p hp hF hG hc
  let s := OrdinaryModel.scale p u a
  let M := OrdinaryModel.model s (t:Zp)
  have h2 : IsUnit (2:Zp) := unit_nat p 2 (by decide) (by omega)
  let : IsProper M.hom := hpr
  let : GeometricallyIntegral M.hom := hgi
  let : SmoothOfRelativeDimension 1 M.hom :=
    OrdinaryModel.relative_dimension Zp hs h2 t.isUnit hD
  obtain ⟨A,iC,iA,iL,iN,iR,iF,iP,iFF,iE,_,⟨ε⟩⟩ :=
    local_section_cover (R:=Zp) hs.unit (t:Zp) h2
  rw [IsUnit.unit_spec] at ε
  obtain ⟨P⟩ := exists_presentation Zp M.hom A ε
  let D := (Over.pullback (specMap Zp Qp)).obj M
  let : IsProper D.hom := inferInstanceAs (IsProper (pullback.snd M.hom (specMap Zp Qp)))
  let : SmoothOfRelativeDimension 1 D.hom :=
    inferInstanceAs (SmoothOfRelativeDimension 1 (pullback.snd M.hom (specMap Zp Qp)))
  let : GeometricallyIntegral D.hom := inferInstanceAs (GeometricallyIntegral (pullback.snd M.hom (specMap Zp Qp)))
  refine ⟨P.group,P.isAbelian,⟨?_⟩⟩
  exact baseChangeToRepresentative (C:=M) (D:=D) P.groupRepresentation
    (groupSheafRepresentation Qp D.hom) (Iso.refl D) ≪≫ sheafGroupSchemeIso Qp D.hom ≪≫
    (paperJacobian_baseChangeIso Qp hu D e).symm

end
end ZInQBlueprint.IntegralPicard
#print axioms ZInQBlueprint.IntegralPicard.paperJacobian_baseChangeIso
#print axioms ZInQBlueprint.IntegralPicard.ordinary_goodReduction
