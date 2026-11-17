import CanonicalPartner
import PrimeFormMaps
import SignedSquareSections

/-! A geometric comparison on the original curve square. Each map on sections is
specified before taking its dimension. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap NormalDescent GeometricMarking CanonicalTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

abbrev outerPointLine (q : CurvePoints u) :=
  external u (pointLine (basepoint hu)) (pointLine q)

abbrev primeFormLine (q : CurvePoints u) :=
  outerPointLine hu q ⊗ (diagonalIdeal u).invModule

/-- The prime-form isomorphism (up to a scalar), the degree-zero Künneth
map, and the *canonical* inclusion of sections allowing poles on the diagonal. -/
structure PrimeFormGeometry : Prop where
  primeForm (q : CurvePoints u) : CanonicalPartner hu q →
    Nonempty (squareTheta hu ≅ primeFormLine hu q)
  externalProduct (q : CurvePoints u) : CanonicalPartner hu q →
    Function.Bijective (externalSections (pointLine (basepoint hu)) (pointLine q))
  diagonal (q : CurvePoints u) : CanonicalPartner hu q →
    Function.Bijective (sectionsMap (curveSquare u) (diagonalInclusion u (outerPointLine hu q)))

private theorem sectionsMap_bijective {X : Over (Spec (.of Qbar))} {L M : X.left.Modules}
    (e : L ≅ M) : Function.Bijective (sectionsMap X e.hom) := by
  refine ⟨Function.LeftInverse.injective (g:=sectionsMap X e.inv) ?_,
    Function.RightInverse.surjective (g:=sectionsMap X e.inv) ?_⟩
  · intro x
    change (e.hom.app ⊤ ≫ e.inv.app ⊤) x = x
    rw [←Scheme.Modules.Hom.comp_app,e.hom_inv_id,Scheme.Modules.Hom.id_app]
    rfl
  · intro x
    change (e.inv.app ⊤ ≫ e.hom.app ⊤) x = x
    rw [←Scheme.Modules.Hom.comp_app,e.inv_hom_id,Scheme.Modules.Hom.id_app]
    rfl

/-- The section dimension of the actual signed Jacobian follows from the
geometric prime form, degree-zero Künneth, and the diagonal inclusion. -/
theorem signed_rank_of_prime_form (geom : PrimeFormGeometry hu) :
    ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom (signedThetaLine hu) = 1 := by
  obtain ⟨q,hq⟩ := canonicalPartner_exists hu
  obtain ⟨e⟩ := geom.primeForm q hq
  let L := pointLine (basepoint hu)
  let M := pointLine q
  let Y := curveSquare u
  let k := LinearEquiv.ofBijective (externalSections L M) (geom.externalProduct q hq)
  let d := LinearEquiv.ofBijective (sectionsMap Y (diagonalInclusion u (outerPointLine hu q)))
    (geom.diagonal q hq)
  let t := LinearEquiv.ofBijective (sectionsMap Y e.hom) (sectionsMap_bijective e)
  have c := (t.trans (d.symm.trans k.symm)).finrank_eq
  have l : Module.finrank Qbar (overSections (paperCurve u) L) = 1 := pointLine_rank hu _
  have m : Module.finrank Qbar (overSections (paperCurve u) M) = 1 := pointLine_rank hu _
  apply signed_rank_one hu
  exact c.trans (by rw [Module.finrank_tensorProduct,l,m])

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.signed_rank_of_prime_form
