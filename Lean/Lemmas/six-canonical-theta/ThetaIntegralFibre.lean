import ThetaReducedImage
import ThetaMultiplicity

/-! The remaining scheme-theoretic comparison is precisely reducedness of the
determinant divisor. Moret-Bailly, Métriques permises, 2.7.10(ii) supplies this
for the canonical Cartier divisor in every geometric fibre. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.CanonicalTheta
open SixAbelMap
noncomputable section

theorem ideal_eq_of_reduced_zero_scheme {X : Scheme} (I : X.IdealSheafData) [IsReduced I.subscheme] :
    I.radical = I := by
  simpa only [Scheme.IdealSheafData.ker_subschemeι] using radical_image_ideal I.subschemeι

theorem signedThetaSection_ideal_of_reduced {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    [IsReduced (Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu)).subscheme] :
    Scheme.Modules.zeroSchemeIdeal (signedThetaSection hu) = (rigidMorphism hu).left.ker :=
  (ideal_eq_of_reduced_zero_scheme _).symm.trans (signedThetaSection_reduced_ideal hu)

end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.ideal_eq_of_reduced_zero_scheme
#print axioms ZInQBlueprint.CanonicalTheta.signedThetaSection_ideal_of_reduced
