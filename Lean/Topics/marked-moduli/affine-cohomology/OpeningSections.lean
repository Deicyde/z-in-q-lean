import TerminalCohomology
import Mathlib.CategoryTheory.Adjunction.Whiskering

/-! Identification, natural in the open, of degree-zero cohomology with ordinary sections. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{0}] [HasExt.{0} (Sheaf J AddCommGrpCat.{0})]

/-- Additive Yoneda for the free abelian presheaf represented by U. -/
def freeEvaluation (P : Cᵒᵖ ⥤ AddCommGrpCat.{0}) (U : C) :
    (yoneda.obj U ⋙ AddCommGrpCat.free ⟶ P) ≃+ P.obj (op U) where
  toEquiv := ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj U) P).trans yonedaEquiv
  map_add' f g := by rfl

/-- Degree-zero cohomology at U agrees with sections over U. -/
def openingSections (F : Sheaf J AddCommGrpCat.{0}) (U : C) :
    F.H' 0 U ≃+ F.obj.obj (op U) :=
  (Ext.addEquiv₀.trans ((sheafificationAdjunction J _).homAddEquiv _ F)).trans
    (freeEvaluation F.obj U)

private theorem openingSections_mk (F : Sheaf J AddCommGrpCat.{0}) (U : C)
    (a : (presheafToSheaf J AddCommGrpCat).obj (yoneda.obj U ⋙ AddCommGrpCat.free) ⟶ F) :
    openingSections F U (Ext.mk₀ a) =
      freeEvaluation F.obj U (((sheafificationAdjunction J _).homEquiv _ F) a) :=
  congrArg (fun b => freeEvaluation F.obj U (((sheafificationAdjunction J _).homEquiv _ F) b))
    (Ext.homEquiv₀.right_inv a)

theorem openingSections_restrict (F : Sheaf J AddCommGrpCat.{0}) {U V : C}
    (i : V ⟶ U) (x : F.H' 0 U) :
    openingSections F V ((F.cohomologyPresheaf 0).map i.op x) =
      F.obj.map i.op (openingSections F U x) := by
  obtain ⟨a, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
  let j := Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free
  change openingSections F V ((Ext.mk₀ ((presheafToSheaf J _).map j)).comp
    (Ext.mk₀ a) (zero_add 0)) = _
  rw [Ext.mk₀_comp_mk₀]
  rw [openingSections_mk, openingSections_mk]
  change yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
      (((sheafificationAdjunction J _).homEquiv _ _) ((presheafToSheaf J _).map j ≫ a))) =
    F.obj.map i.op (yonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
      (((sheafificationAdjunction J _).homEquiv _ _) a)))
  rw [Adjunction.homEquiv_naturality_left]
  let b := ((sheafificationAdjunction J _).homEquiv _ F) a
  exact (congrArg yonedaEquiv ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left
    (yoneda.map i) b)).trans (yonedaEquiv_naturality
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _) b) i).symm

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.openingSections
#print axioms ZInQBlueprint.BinaryCover.Cech.openingSections_restrict
