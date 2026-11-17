import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertiblePullbackSectionEqZeroIffMemSupport
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgebraicEquivalenceIsoTensorUnit

/-! Base change of the geometric zero set of a section of an invertible sheaf. -/
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace ZInQBlueprint.CanonicalTheta
noncomputable section
/-- Vanishing can be tested after composing the point with the comparison morphism. -/
theorem fibrewise_pullback {k : Type} [Field k] {X Y : Scheme} (f : X ⟶ Y) {L : Y.Modules}
    (invL : L.IsInvertible) (s : 𝟙_ _ ⟶ L) (x : Spec (.of k) ⟶ X) :
    Scheme.Modules.pullbackSection x (Scheme.Modules.pullbackSection f s) = 0 ↔
      Scheme.Modules.pullbackSection (x ≫ f) s = 0 := by
  rw [(invL.pullback f).pullbackSection_eq_zero_iff_mem_support,invL.pullbackSection_eq_zero_iff_mem_support,
    ←invL.comap_zeroSchemeIdeal f s,Scheme.IdealSheafData.support_comap]
  rfl
/-- Isomorphisms preserve a nonzero section of a module. -/
theorem iso_pullback_nonzero {X Y : Scheme} (f : X ≅ Y) {L : Y.Modules} (s : 𝟙_ _ ⟶ L) (hs : s ≠ 0) :
    Scheme.Modules.pullbackSection f.hom s ≠ 0 :=
  JacobianVarieties.Picard.Proofs.IsAlgEquivZero_nonempty_iso_tensorUnit_of_ne_zero.AlgZeroTrivGlue.pullbackSection_ne_zero f.hom s hs
end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.fibrewise_pullback
#print axioms ZInQBlueprint.CanonicalTheta.iso_pullback_nonzero
