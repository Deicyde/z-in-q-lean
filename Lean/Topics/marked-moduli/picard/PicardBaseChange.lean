import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! Group-valued Yoneda and base change of a represented Picard functor.
Test schemes need no rational point on the curve. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace ZInQBlueprint.PicardBaseChange
universe u
noncomputable section

/-- The group of points is evaluated on every test scheme over the base. -/
abbrev points {S : Scheme.{u}} (A : CommGrp (Over S)) : (Over S)ᵒᵖ ⥤ GrpCat.{u} :=
  yonedaGrp.obj A.toGrp

/-- A natural isomorphism of group-valued point functors induces a group-scheme isomorphism. -/
def groupIso {S : Scheme.{u}} {A B : CommGrp (Over S)} (e : points A ≅ points B) : A ≅ B :=
  (CommGrp.fullyFaithfulForget₂Grp (Over S)).preimageIso (yonedaGrpFullyFaithful.preimageIso e)

theorem points_map_groupIso {S : Scheme.{u}} {A B : CommGrp (Over S)} (e : points A ≅ points B) :
    yonedaGrp.mapIso ((CommGrp.forget₂Grp (Over S)).mapIso (groupIso e)) = e := by
  apply Iso.ext
  change yonedaGrp.map ((CommGrp.forget₂Grp (Over S)).map
    ((CommGrp.fullyFaithfulForget₂Grp (Over S)).preimage
      (yonedaGrpFullyFaithful.preimage e.hom))) = e.hom
  rw [(CommGrp.fullyFaithfulForget₂Grp (Over S)).map_preimage]
  exact yonedaGrpFullyFaithful.map_preimage e.hom

/-- Evaluate a representing group scheme after extending the base. -/
def restrictPoints {S T : Scheme.{u}} (f : T ⟶ S) (A : CommGrp (Over S)) :
    (Over.map f).op ⋙ points A ≅ points ((Over.pullback f).mapCommGrp.obj A) := by
  let adj := Over.mapPullbackAdj f
  refine NatIso.ofComponents (fun U => (MulEquiv.toGrpIso
    (show ((Over.map f).obj U.unop ⟶ A.X) ≃* (U.unop ⟶ (Over.pullback f).obj A.X) from
      { __ := adj.homEquiv U.unop A.X
        map_mul' := fun a b => by
          change adj.homEquiv U.unop A.X (a*b) =
            adj.homEquiv U.unop A.X a * adj.homEquiv U.unop A.X b
          simp only [Adjunction.homEquiv_apply, Functor.map_mul]
          exact MonObj.comp_mul _ _ _ }))) ?_
  intro U V h
  ext a
  exact adj.homEquiv_naturality_left h.unop a

/-- A local and a global representative of the same relative Picard functor
give canonically isomorphic group schemes on the local base. -/
def localIso {S T : Scheme.{u}} (f : T ⟶ S) {A : CommGrp (Over S)} {B : CommGrp (Over T)}
    {P : (Over S)ᵒᵖ ⥤ GrpCat.{u}} {Q : (Over T)ᵒᵖ ⥤ GrpCat.{u}}
    (globalRep : P ≅ points A) (localRep : Q ≅ points B)
    (comparison : Q ≅ (Over.map f).op ⋙ P) :
    B ≅ (Over.pullback f).mapCommGrp.obj A :=
  groupIso (localRep.symm ≪≫ comparison ≪≫ Functor.isoWhiskerLeft _ globalRep ≪≫ restrictPoints f A)

end
end ZInQBlueprint.PicardBaseChange

#print axioms ZInQBlueprint.PicardBaseChange.groupIso
#print axioms ZInQBlueprint.PicardBaseChange.points_map_groupIso
#print axioms ZInQBlueprint.PicardBaseChange.restrictPoints
#print axioms ZInQBlueprint.PicardBaseChange.localIso
