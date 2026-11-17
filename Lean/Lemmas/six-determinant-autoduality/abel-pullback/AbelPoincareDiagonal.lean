import SignedDeterminantEvaluation
import DiagonalBundleAlgebra
import Nyll.JacobianVarieties.Albanese.AbelJacobiPointClassUnique

/-! The restriction of the fixed Poincaré bundle to the pointed Abel map. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed ZInQBlueprint.AbelDiagonalAlgebra ZInQBlueprint.AbelDiagonalAlgebra.Classical
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.DeterminantAutoduality
open SixAbelMap CanonicalTheta AbelianModel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2100000
variable {K : Type} [Field K] [IsAlgClosed K] {C : Over (Spec (.of K))}
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]
  {b : base K ⟶ C} {V : GroupScheme K} {e : V ≅ groupScheme K C.hom} {m : C ⟶ V.X}
variable (P : Pointed b e m)

/-- Uniqueness from the actual field-valued point classes identifies the fixed
pointed Abel map with the normalized diagonal's classifying morphism. -/
theorem abel_eq_diagonal : P.aj =
    diagonalPicardClassifyingMap C.hom b.left b.w P.J P.represents := by
  let z := (presentation K C.hom).pointedComparisonOver (schemePoint b) P.represents
  let zs := (Over.forget _).mapIso z
  let : IsIso z.inv.left := inferInstanceAs (IsIso zs.inv)
  let : IsProper (toBase K C.hom) := proper K C.hom
  have hz : z.inv.left ≫ (toBase K C.hom) = P.J.toBase := z.inv.w
  let : IsProper P.J.toBase := by rw [← hz]; infer_instance
  apply abelJacobi_eq_of_geometric_point_class K C.hom (schemePoint b) P.J P.represents K
  · exact P.classifies.2 K _
  · exact diagonalPicardClassifyingMap_fieldPointIso C.hom b.left b.w P.J P.represents K _

/-- On the entire product the pullback is O(Δ−{b}×C−C×{b}).
Both horizontal and vertical factors are retained. -/
theorem abel_poincare_diagonal :
    Nonempty ((P.represents.poincare.pullbackAlong P.aj).L ≅
      (graphEffectiveCartierDivisor C.hom C.hom (𝟙 C.left) (Category.id_comp _)).1.invModule ⊗
        (diagonalEdgeEffectiveCartierDivisor C.hom b.left b.w).1.module) := by
  rw [abel_eq_diagonal P]
  exact diagonalPicardClassifyingMap_poincareIso C.hom b.left b.w P.J P.represents

set_option linter.unusedSectionVars false in
omit [IsAlgClosed K] in
/-- Restricting O(Δ−{b}×C) to {p}×C leaves O(p). The constant line
contributed by {b} is trivial on the base field, including at p=b. -/
theorem horizontal_abel_family (p : base K ⟶ C) :
    Nonempty ((Scheme.Modules.pullback (rigSection C.hom C.hom (schemePoint p))).obj
      (ajFamily (a:=C.hom) (schemePoint b)) ≅ p.left.ker.invModule) := by
  let c := C.hom
  let σ := rigSection c c (schemePoint p)
  let D := graphEffectiveCartierDivisor c c (𝟙 C.left) (Category.id_comp c)
  let A := productPointFstEffectiveCartierDivisor c b.left b.w
  have hP : p.left.ker.IsInvertible := (sectionEffectiveCartierDivisor c p.left p.w).2.isInvertible
  have hB : b.left.ker.IsInvertible := (sectionEffectiveCartierDivisor c b.left b.w).2.isInvertible
  have H : D.1.comap σ = p.left.ker := diagonalIdeal_comap_kunnethSectionRight c p.left p.w
  obtain ⟨δ⟩ := D.2.isInvertible.nonempty_pullback_invModule_iso σ (H.symm ▸ hP)
  let d := δ ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule H)
  have hA : IsIso (b.left.ker.pullbackModuleComparison (pullback.fst c c)) :=
    hB.isIso_pullbackModuleComparison (pullback.fst c c) A.2.isInvertible
  let u := @asIso _ _ _ _ (b.left.ker.pullbackModuleComparison (pullback.fst c c)) hA
  obtain ⟨κ⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K _
    (hB.isInvertible_module.pullback p.left)
  have s : σ ≫ pullback.fst c c = c ≫ p.left := kunnethSectionRight_fst c c p.left p.w
  let k := (Scheme.Modules.pullback σ).mapIso u.symm ≪≫
    (Scheme.Modules.pullbackComp σ (pullback.fst c c)).app b.left.ker.module ≪≫
    (Scheme.Modules.pullbackCongr s).app b.left.ker.module ≪≫
    ((Scheme.Modules.pullbackComp c p.left).app b.left.ker.module).symm ≪≫
    (Scheme.Modules.pullback c).mapIso κ ≪≫ Scheme.Modules.pullbackTensorUnitObjIso c
  let a : A.1.module ≅ (constDiv (a:=c) (schemePoint b)).idealModule :=
    eqToIso (congrArg Scheme.IdealSheafData.module (pointKernel_comap_fst c c b.left b.w))
  exact ⟨(Scheme.Modules.pullback σ).mapIso (Iso.refl D.1.invModule ⊗ᵢ a.symm) ≪≫
    Scheme.Modules.pullbackTensorObjIso σ D.1.invModule A.1.module ≪≫ (d ⊗ᵢ k) ≪≫ ρ_ _⟩

/-- The actual Abel pullback of the Poincaré evaluation at p is O(p−b). -/
theorem abel_pullback_evaluation (p : base K ⟶ C) :
    Nonempty ((Scheme.Modules.pullback m.left).obj (evaluationLine P p) ≅
      p.left.ker.invModule ⊗ b.left.ker.module) := by
  let c := C.hom
  let W := P.represents.poincare
  let σ := rigSection c c (schemePoint p)
  let τ := rigSection c P.J.toBase (schemePoint p)
  let ψ := baseChangeSnd c P.aj
  let B := productPointSndEffectiveCartierDivisor c b.left b.w
  have hB := (sectionEffectiveCartierDivisor c b.left b.w).2.isInvertible
  have hB' : IsIso (b.left.ker.pullbackModuleComparison (pullback.snd c c)) :=
    hB.isIso_pullbackModuleComparison (pullback.snd c c) B.2.isInvertible
  let β := @asIso _ _ _ _ (b.left.ker.pullbackModuleComparison (pullback.snd c c)) hB'
  have σ₂ : σ ≫ pullback.snd c c = 𝟙 C.left := kunnethSectionRight_snd c c p.left p.w
  let res : (Scheme.Modules.pullback σ).obj B.1.module ≅ b.left.ker.module :=
    (Scheme.Modules.pullback σ).mapIso β.symm ≪≫
    (Scheme.Modules.pullbackComp σ (pullback.snd c c)).app b.left.ker.module ≪≫
    (Scheme.Modules.pullbackCongr σ₂).app b.left.ker.module ≪≫
    (Scheme.Modules.pullbackId C.left).app b.left.ker.module
  obtain ⟨diag⟩ := abel_poincare_diagonal P
  obtain ⟨edges⟩ := diagonalMiddleDivisorBundle_iso_ajFamily c b.left b.w
  obtain ⟨hor⟩ := horizontal_abel_family (b:=b) p
  have hcomp : m.left ≫ P.toRepresenting.hom.left = P.aj.1 :=
    congrArg (fun k : C ⟶ Over.mk P.J.toBase => k.left) P.abel_comparison
  have hrs : σ ≫ ψ = P.aj.1 ≫ τ := rigSection_baseChangeSnd c (schemePoint p) P.aj
  let t := (Scheme.Modules.pullback τ).obj W.L
  exact ⟨(Scheme.Modules.pullbackComp m.left P.toRepresenting.hom.left).app t ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app t ≪≫
    (Scheme.Modules.pullbackComp P.aj.1 τ).app W.L ≪≫
    (Scheme.Modules.pullbackCongr hrs.symm).app W.L ≪≫
    ((Scheme.Modules.pullbackComp σ ψ).app W.L).symm ≪≫
    (Scheme.Modules.pullback σ).mapIso (diag ≪≫ edges) ≪≫
    Scheme.Modules.pullbackTensorObjIso σ _ _ ≪≫ (hor ⊗ᵢ res)⟩

end
end ZInQBlueprint.DeterminantAutoduality
#print axioms ZInQBlueprint.DeterminantAutoduality.abel_eq_diagonal
#print axioms ZInQBlueprint.DeterminantAutoduality.abel_poincare_diagonal
#print axioms ZInQBlueprint.DeterminantAutoduality.horizontal_abel_family
#print axioms ZInQBlueprint.DeterminantAutoduality.abel_pullback_evaluation
