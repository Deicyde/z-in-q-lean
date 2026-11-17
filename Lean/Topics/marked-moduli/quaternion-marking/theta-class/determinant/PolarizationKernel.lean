import AbelStabilizer
import SignedAutoduality

/-! The stabilizer of the line embeds into the stabilizer of its unique
effective divisor. The latter was computed on the literal signed curve. -/
open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking DeterminantAutoduality CanonicalTheta SixAbelMap SixThetaRestriction
noncomputable section
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

/-- Dimension one makes the signed determinant homomorphism injective on
geometric points. This step works with the support of the Abel divisor. -/
theorem signed_polarization_injective
    (one : ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom (signedThetaLine hu) = 1) :
    Function.Injective (signedPolarization hu) := by
  let A := geometricJacobian hu
  let L := signedThetaLine hu
  let s := signedThetaSection hu
  have hL := signedThetaLine_invertible hu
  apply (injective_iff_map_eq_zero _).mpr
  intro t ht
  change translatedClass L hL t / lineClass L hL = 1 at ht
  obtain ⟨e⟩ := (lineClass_eq _ _).mp (div_eq_one.mp ht)
  let id : A ≅ A := Iso.refl _
  let idPull : (Scheme.Modules.pullback id.hom.hom.hom.hom.left).obj L ≅ L :=
    (Scheme.Modules.pullbackId A.X.left).app L
  apply signed_abel_stabilizer_zero hu
  intro p hp
  have hz := Set.ext_iff.mp (signedThetaSection_zeros hu) p
  have moved := ThetaLinearSystem.group_vanishes_iff L hL s (signedThetaSection_ne_zero hu)
    one id t (idPull ≪≫ e.symm) p
  exact (Set.ext_iff.mp (signedThetaSection_zeros hu) (p+t)).mp (moved.mp (hz.mpr hp))

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.signed_polarization_injective
