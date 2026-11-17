import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-! A map into a separated scheme is determined on a nonempty open of an integral
source by its action on field-valued points there. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.AffinePointAction
universe u
noncomputable section
variable {K : Type u} [Field K] [IsAlgClosed K]
abbrev base (K : Type u) [Field K] := Spec (CommRingCat.of K)
abbrev origin (K : Type u) [Field K] : Over (base K) := Over.mk (𝟙 _)
def support {C : Over (base K)} (p : origin K ⟶ C) : C.left :=
  p.left (IsLocalRing.closedPoint K)

set_option backward.isDefEq.respectTransparency false in
theorem ext_of_open_points {C D : Over (base K)} [AlgebraicGeometry.IsIntegral C.left]
    [LocallyOfFiniteType C.hom] [LocallyOfFiniteType D.hom] [IsSeparated D.hom]
    (f g : C ⟶ D) (U : C.left.Opens) (hU : (U : Set C.left).Nonempty)
    (h : ∀ p : origin K ⟶ C, support p ∈ U → p ≫ f = p ≫ g) : f = g := by
  let : LocallyOfFiniteType (f.left ≫ D.hom) := f.w.symm ▸ inferInstanceAs (LocallyOfFiniteType C.hom)
  apply Over.OverMorphism.ext
  apply AlgebraicGeometry.ext_of_apply_eq D.hom U U.isOpen.isLocallyClosed (U.isOpen.dense hU)
  · intro x hx hclosed
    let p : origin K ⟶ C := Over.homMk (pointOfClosedPoint C.hom x hclosed)
      (pointOfClosedPoint_comp C.hom x hclosed)
    have hp : support p = x := pointOfClosedPoint_apply _ _ _ _
    have he := congrArg (fun q : origin K ⟶ D => support q) (h p (hp.symm ▸ hx))
    change f.left (support p) = g.left (support p) at he
    rwa [hp] at he
  · exact f.w.trans g.w.symm

end
end ZInQBlueprint.AffinePointAction
#print axioms ZInQBlueprint.AffinePointAction.ext_of_open_points
