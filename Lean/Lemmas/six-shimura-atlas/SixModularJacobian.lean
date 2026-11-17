import SixBGCompletion

/-! The actual Jacobian of the normalized modular-form equation, with its
proper curve and a comparison to the printed Jacobian. -/
open CategoryTheory AlgebraicGeometry Polynomial
open JacobianVarieties.Picard.Unpointed
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent CoarseConic PrintedModel BinaryCover
open AbelianModel
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

variable {u : ℚ} (hu : u ∉ ZInQ.contactSet) {p : ConicPoint} (hp : FibrePoint u p)
  {e l : Qbar} (he : e^2 = -6) (hl : l^2=2)
def rad {u : ℚ} {p : ConicPoint} {e : Qbar} := -(e*p.y/3)/(r u : Qbar)

include hu hp he hl

theorem rad_spec :
    (rad (u:=u) (p:=p) (e:=e))^2=6 ∧ argument u (rad (u:=u) (p:=p) (e:=e)) = -(e*p.y/3) ∧
    (l*p.z)^2=9*(e*p.y/3)^2-32 ∧ l*p.z≠0 := by
  obtain ⟨d,h1,h2,h3,h4⟩ := compatible_radicals hu hp e l he hl
  have hr : (r u : Qbar) ≠ 0 := by exact_mod_cast (radical_units hu).1
  have eq : d = rad (u:=u) (p:=p) (e:=e) := (eq_div_iff hr).mpr h2
  exact eq ▸ ⟨h1,h2,h3,h4⟩

abbrev modularCurve := sexticCompletion (modularPolynomial (e*p.y/3) (l*p.z))
  (modular_regular hu (rad_spec hu hp he hl).1 (rad_spec hu hp he hl).2.1
    (rad_spec hu hp he hl).2.2.1 (rad_spec hu hp he hl).2.2.2).1

def modularCurveIso :
    modularCurve hu hp he hl ≅ PrintedModel.model hu (rad_spec hu hp he hl).1 := by
  let chooseRoot := IsAlgClosed.exists_pow_nat_eq (-4*(l*p.z)^6) (by decide : 0<2)
  let v := chooseRoot.choose
  have hv := chooseRoot.choose_spec
  exact (modular_completion hu (rad_spec hu hp he hl).1 (rad_spec hu hp he hl).2.1
    (rad_spec hu hp he hl).2.2.1 (rad_spec hu hp he hl).2.2.2 hv).exists.choose

def signedToModular : paperPullback Qbar u ≅ modularCurve hu hp he hl := by
  let chooseRoot := IsAlgClosed.exists_pow_nat_eq (factor u (rad (u:=u) (p:=p) (e:=e))) (by decide : 0<2)
  let v := chooseRoot.choose
  have hv := chooseRoot.choose_spec
  exact PrintedModel.curveIso hu (rad_spec hu hp he hl).1 v hv ≪≫ (modularCurveIso hu hp he hl).symm

instance modular_proper : IsProper (modularCurve hu hp he hl).hom :=
  (sexticCompletion_geometry _ (modular_regular hu (rad_spec hu hp he hl).1
    (rad_spec hu hp he hl).2.1 (rad_spec hu hp he hl).2.2.1 (rad_spec hu hp he hl).2.2.2).2).2.1

instance modular_smooth : SmoothOfRelativeDimension 1 (modularCurve hu hp he hl).hom := by
  obtain ⟨hI,_,hS,hD,_⟩ := sexticCompletion_geometry _ (modular_regular hu (rad_spec hu hp he hl).1
    (rad_spec hu hp he hl).2.1 (rad_spec hu hp he hl).2.2.1 (rad_spec hu hp he hl).2.2.2).2
  let : AlgebraicGeometry.IsIntegral (modularCurve hu hp he hl).left := hI
  let : Smooth (modularCurve hu hp he hl).hom := hS
  exact SixJacobian.relative_dimension_one _ hD

instance modular_geom : GeometricallyIrreducible (modularCurve hu hp he hl).hom := by
  let a := signedToModular hu hp he hl
  let : IsIso a.inv.left := inferInstanceAs (IsIso (((Over.forget _).mapIso a).inv))
  let : GeometricallyIntegral (paperModel ℚ u).hom := geometricallyIntegral_paperModel hu
  have h : GeometricallyIrreducible (paperPullback Qbar u).hom := inferInstanceAs (GeometricallyIrreducible (Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  have sq : IsPullback a.inv.left (modularCurve hu hp he hl).hom (paperPullback Qbar u).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact a.inv.w⟩
  exact MorphismProperty.of_isPullback (P := @GeometricallyIrreducible) sq h

abbrev modularJacobian := groupScheme Qbar (modularCurve hu hp he hl).hom

def signedModularJacobian :
    (baseChange (algebraMap ℚ Qbar)).obj (SixJacobian.jacobian hu) ≅ modularJacobian hu hp he hl :=
  IntegralPicard.paperJacobian_baseChangeIso Qbar hu _ (signedToModular hu hp he hl)

def modularPrintedJacobian :
    modularJacobian hu hp he hl ≅ PrintedModel.jacobian hu (rad_spec hu hp he hl).1 := by
  let chooseRoot := IsAlgClosed.exists_pow_nat_eq (factor u (rad (u:=u) (p:=p) (e:=e))) (by decide : 0<2)
  let v := chooseRoot.choose
  have hv := chooseRoot.choose_spec
  exact (signedModularJacobian hu hp he hl).symm ≪≫ PrintedModel.jacobianIso hu (rad_spec hu hp he hl).1 v hv

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.rad_spec
#print axioms ZInQBlueprint.ShimuraAtlas.modularCurveIso
#print axioms ZInQBlueprint.ShimuraAtlas.signedToModular
#print axioms ZInQBlueprint.ShimuraAtlas.signedModularJacobian
#print axioms ZInQBlueprint.ShimuraAtlas.modularPrintedJacobian
