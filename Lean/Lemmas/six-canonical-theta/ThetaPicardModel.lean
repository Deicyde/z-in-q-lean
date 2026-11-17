import ThetaDeterminant
import ThetaSectionTransport

/-! Transport of the determinant bundle, including its actual pointed Picard comparison. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicCurve GoodReductionJacobian NeronModelInfra MonoidalCategory
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.CanonicalTheta
open SixAbelMap AbelianModel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
  [Algebra.EssFiniteType K F]
variable {C : Over (Spec (.of K))} [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
  [GeometricallyIntegral C.hom] {b : base K ⟶ C} {V : GroupScheme K}
  {e : V ≅ groupScheme K C.hom} {m : C ⟶ V.X}

/-- A pointed representation includes the commutative square identifying the given morphism.
Thus all changes of coordinates of the target are accounted for in the determinant. -/
structure Pointed {C : Over (Spec (.of K))} [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom]
    [GeometricallyIntegral C.hom] (b : base K ⟶ C) {V : GroupScheme K}
    (e : V ≅ groupScheme K C.hom) (m : C ⟶ V.X) where
  J : RelativePic0Designation K C.hom
  represents : RepresentsRelSubPic C.hom (schemePoint b) (algEquivZeroCut C.hom (schemePoint b)) J
  aj : SchemeHomOver C.hom J.toBase
  classifies : IsPointedAbel C (schemePoint b) J represents aj
  comparison : (m ≫ e.hom.hom.hom.hom) ≫
    ((presentation K C.hom).pointedComparisonOver (schemePoint b) represents).hom = Over.homMk aj.1 aj.2

namespace Pointed
variable (P : Pointed b e m)
def toRepresenting : V.X ≅ Over.mk P.J.toBase :=
  (CommGrp.forget _).mapIso e ≪≫ (presentation K C.hom).pointedComparisonOver (schemePoint b) P.represents

omit [IsAlgClosed K] in
theorem abel_comparison : m ≫ P.toRepresenting.hom = Over.homMk P.aj.1 P.aj.2 :=
  (Category.assoc _ _ _).symm.trans P.comparison

/-- The dual determinant of the rank-three Picard bundle at 4b, pulled back along
the canonical base-change and representing isomorphisms. -/
def determinantLine : V.X.left.Modules :=
  (Scheme.Modules.pullback P.toRepresenting.hom.left).obj
    (thetaBundle C.hom (schemePoint b) P.J.toBase P.represents.poincare 4 3)

theorem exists_theta (M : CurveModel K F) (i : M.C ≅ C.left) (hi : i.hom ≫ C.hom = M.toBase)
    (g : genusFF K F = 2) :
    P.determinantLine.IsInvertible ∧ ∃ θ : 𝟙_ _ ⟶ P.determinantLine, θ ≠ 0 ∧
      ∀ x : base K ⟶ V.X, Scheme.Modules.pullbackSection x.left θ = 0 ↔
        ∃ p : base K ⟶ C, p ≫ m = x := by
  let z := (presentation K C.hom).pointedComparisonOver (schemePoint b) P.represents
  let zs := (Over.forget _).mapIso z
  let E := P.toRepresenting
  let Es := (Over.forget _).mapIso E
  have heq : z.inv.left ≫ (toBase K C.hom) = P.J.toBase := z.inv.w
  let : Smooth (toBase K C.hom) := smooth K C.hom
  let : IsProper (toBase K C.hom) := proper K C.hom
  let : IsIso z.inv.left := inferInstanceAs (IsIso zs.inv)
  have s : Smooth P.J.toBase := by rw [←heq];infer_instance
  have pr : IsProper P.J.toBase := by rw [←heq];infer_instance
  obtain ⟨hL, θ,ne,eq⟩ := exists_designated_theta C b P.represents P.aj M i hi g s pr P.classifies
  refine ⟨hL.pullback E.hom.left, Scheme.Modules.pullbackSection E.hom.left θ,
    iso_pullback_nonzero Es θ ne,?_⟩
  intro x
  rw [fibrewise_pullback E.hom.left hL θ x.left]
  change Scheme.Modules.pullbackSection (x ≫ E.hom).left θ = 0 ↔ _
  rw [eq]
  constructor
  · rintro ⟨p,hp⟩
    refine ⟨p,(cancel_mono E.hom).mp ?_⟩
    rw [Category.assoc,P.abel_comparison]
    apply Over.OverMorphism.ext
    exact hp
  · rintro ⟨p,rfl⟩
    refine ⟨p,?_⟩
    have hw := congrArg (fun z : base K ⟶ Over.mk P.J.toBase => z.left)
      ((Category.assoc p m E.hom).trans (congrArg (p ≫ ·) P.abel_comparison))
    exact hw.symm

end Pointed
end
end ZInQBlueprint.CanonicalTheta
#print axioms ZInQBlueprint.CanonicalTheta.Pointed.abel_comparison
#print axioms ZInQBlueprint.CanonicalTheta.Pointed.exists_theta
