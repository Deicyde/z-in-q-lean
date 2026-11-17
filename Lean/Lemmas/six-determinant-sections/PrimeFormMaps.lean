import CurvePointSections
import SectionDescent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Nyll.SchemeTheory.Modules.Tensor.TensorSections

/-! The degree-zero external product, the diagonal Cartier section, and
their induced maps on global sections. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped TensorProduct ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap NormalDescent GeometricMarking
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
variable {u : ℚ}

abbrev overSections (X : Over (Spec (.of Qbar))) (L : X.left.Modules) := Γ(L,⊤)

scoped instance sectionsModule (X : Over (Spec (.of Qbar))) (L : X.left.Modules) :
    Module Qbar (overSections X L) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom X.hom L ⊤

def sectionsMap (X : Over (Spec (.of Qbar))) {L M : X.left.Modules} (j : L ⟶ M) :
    overSections X L →ₗ[Qbar] overSections X M where
  toFun := fun x => j.app ⊤ x
  map_add' := fun x y => map_add _ x y
  map_smul' := fun a x => Scheme.Modules.Hom.app_smul j
    ((Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤).algebraMap a) x

def external (u : ℚ) (L M : (paperCurve u).left.Modules) : (curveSquare u).left.Modules :=
  (Scheme.Modules.pullback (first u).left).obj L ⊗ (Scheme.Modules.pullback (second u).left).obj M

/-- Send s⊗t to pr₁*s ⊗ pr₂*t. -/
def externalSections (L M : (paperCurve u).left.Modules) :
    (overSections (paperCurve u) L ⊗[Qbar] overSections (paperCurve u) M) →ₗ[Qbar]
      overSections (curveSquare u) (external u L M) := by
  let a := sectionsPull (first u) L
  let b := sectionsPull (second u) M
  let S := (curveSquare u).left
  let act := (Scheme.TwoAffineOpenCover.algebraOfHom (curveSquare u).hom ⊤).algebraMap
  apply TensorProduct.lift
  refine LinearMap.mk₂ Qbar (fun x y => Scheme.Modules.tensorSections (a x) (b y)) ?_ ?_ ?_ ?_
  · intro x y z; rw [map_add,Scheme.Modules.tensorSections_add_left]
  · intro r x y; rw [map_smul]
    exact Scheme.Modules.tensorSections_smul_left (act r) (a x) (b y)
  · intro x y z; rw [map_add,Scheme.Modules.tensorSections_add_right]
  · intro r x y; rw [map_smul]
    exact Scheme.Modules.tensorSections_smul_right (act r) (a x) (b y)

def diagonalIdeal (u : ℚ) : (curveSquare u).left.IdealSheafData :=
  (pullback.diagonal (paperCurve u).hom).ker

def diagonalInclusion (u : ℚ) (B : (curveSquare u).left.Modules) :
    B ⟶ B ⊗ (diagonalIdeal u).invModule :=
  (ρ_ B).inv ≫ B ◁ (diagonalIdeal u).invModuleSection

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.externalSections
#print axioms ZInQBlueprint.DeterminantSections.diagonalInclusion
