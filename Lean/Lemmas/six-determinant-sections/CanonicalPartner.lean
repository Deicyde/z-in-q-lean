import SignedDifferenceMap
import PencilExceptions

/-! The point paired with the chosen marking by the canonical genus-two pencil. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped KaehlerDifferential ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap NormalDescent GeometricMarking
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- O(q) is the Serre-dual line ω_C(−b). -/
def CanonicalPartner (q : CurvePoints u) : Prop :=
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  letI := N.curve
  letI := paper_essentially_finite hu
  let F := (paperCurve u).left.functionField
  letI : HasCanonicalDivisor (K:=Qbar) (F:=F) := hasCanonicalDivisor_of_isCurveOver
  let b := normalizedPlace N (basepoint hu)
  ∃ (ω : Ω[F⁄Qbar]) (hω : ω ≠ 0), Divisor.IsPrincipal
    (Finsupp.single (normalizedPlace N q) 1 - (canonicalDivisorOf hω - Finsupp.single b 1))

theorem canonicalPartner_exists : ∃ q, CanonicalPartner hu q := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let N := signedModel hu
  let := N.curve
  let := paper_essentially_finite hu
  let F := (paperCurve u).left.functionField
  let : HasCanonicalDivisor (K:=Qbar) (F:=F) := hasCanonicalDivisor_of_isCurveOver
  let : ∀ v : Place Qbar F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  let b := normalizedPlace N (basepoint hu)
  let ω := b.dCoord
  have hω : ω ≠ 0 := b.dCoord_ne_zero
  let Kc := canonicalDivisorOf hω
  have g : genusFF Qbar F = 2 := paper_functionField_genus hu
  obtain ⟨t,ht,hfin,-⟩ := IsCurveOver.exists_separating_transcendental (K:=Qbar) (F:=F)
  have RR : FunctionFieldRiemannRoch Qbar F := functionFieldRiemannRoch_of_isAlgClosed_of_transcendental ht hfin
  have con := constantsAreBase_of_isAlgClosed_of_transcendental t ht
  have wa : WeilDualityAdelic Qbar F := weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists RR
    (stichtenothGenusExists_of_isCurveOver con)
  have gg := (genus_eq_genusFF RR wa con).trans g
  have expr := RR hω Kc
  have e0 := ell_zero_eq_one_of_constantsAreBase con
  obtain ⟨ek,eb⟩ := paper_canonical_pencil hu b ω hω
  change (ell Kc : ℤ) - ell (Kc-Kc) = Divisor.degree Kc + 1 - _ at expr
  change ell Kc = 2 at ek
  rw [sub_self,e0,ek,gg] at expr
  have dk : Divisor.degree (Kc - Finsupp.single b 1) = 1 := by
    rw [map_sub,Divisor.degree_single,IsCurveOver.deg_eq_one_of_isAlgClosed]
    norm_num at expr ⊢
    omega
  have e1 : 0 < ell (Kc - Finsupp.single b 1) := by rw [show ell (Kc - Finsupp.single b 1) = 1 from eb]; decide
  obtain ⟨P,hP⟩ := (CanonicalTheta.degree_one_ell _ dk).mp e1
  obtain ⟨q,rfl⟩ := (normalizedPlace N).surjective P
  exact ⟨q,ω,hω,hP⟩

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.canonicalPartner_exists
