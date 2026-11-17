import AbelPoincareDiagonal
import SignedAutoduality
import SignedDifferenceMap

/-! The signed determinant polarization is injective on geometric sections. -/
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantAutoduality
open SixAbelMap CanonicalTheta AbelianModel GeometricMarking QuaternionMarking NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
variable {K : Type} [Field K] [IsAlgClosed K] {C : Over (Spec (.of K))}
  [IsProper C.hom] [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIntegral C.hom]
  {b : base K ⟶ C} {V : GroupScheme K} {e : V ≅ groupScheme K C.hom} {m : C ⟶ V.X}
variable (P : Pointed b e m)

omit [IsAlgClosed K] in
/-- Convert the curve's divisor O(p−b) to the actual fibre of the
relative Poincaré family belonging to the Abel class at p. -/
theorem point_difference_fibre (p : base K ⟶ C) :
    let f := pullback.fst C.hom (𝟙 (Spec (.of K)))
    Nonempty ((Scheme.Modules.pullback f).obj (p.left.ker.invModule ⊗ b.left.ker.module) ≅
      (P.represents.poincare.pullbackAlong
        (schemePoint (p ≫ (Over.homMk P.aj.1 P.aj.2 : C ⟶ Over.mk P.J.toBase)))).L) := by
  let c := C.hom
  let t := 𝟙 (Spec (.of K))
  let f := pullback.fst c t
  let v : SchemeHomOver t c := ⟨t ≫ b.left, by rw [Category.assoc,b.w]; exact Category.comp_id t⟩
  let A := RelEffCartierDiv.ofPoint c p.left p.w
  let B := RelEffCartierDiv.ofPoint c v.1 v.2
  have kerP : p.left.ker.comap f = A.I := by
    have h := pointKernel_comap_fst c t p.left p.w
    have X : t ≫ p.left = p.left := Category.id_comp _
    have k := RelEffCartierDiv.ofPoint_congr c X (by rw [Category.assoc,p.w]; exact Category.id_comp _) p.w
    exact h.trans (congrArg RelEffCartierDiv.I k)
  have kerB : b.left.ker.comap f = B.I := pointKernel_comap_fst c t b.left b.w
  have hP := Scheme.Hom.isInvertible_ker_of_comp_eq_id p.left p.w
  have hB := Scheme.Hom.isInvertible_ker_of_comp_eq_id b.left b.w
  obtain ⟨isoP⟩ := hP.nonempty_pullback_invModule_iso f
    (kerP.symm ▸ RelEffCartierDiv.isInvertible_I A)
  have eB : IsIso (b.left.ker.pullbackModuleComparison f) :=
    hB.isIso_pullbackModuleComparison f (kerB.symm ▸ RelEffCartierDiv.isInvertible_I B)
  let u := isoP ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule kerP)
  let v' := @asIso _ _ _ _ (b.left.ker.pullbackModuleComparison f) eB ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.module kerB)
  obtain ⟨w⟩ := P.classifies.2 K t (schemePoint p)
  exact ⟨Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (u ⊗ᵢ v') ≪≫ w.symm⟩

/-- Isomorphic evaluations give equal Abel classes. This compares only
the chosen Picard representation and its own normalized families. -/
theorem equal_abel_of_evaluations {p q : base K ⟶ C}
    (H : Nonempty (evaluationLine P p ≅ evaluationLine P q)) : p ≫ m = q ≫ m := by
  obtain ⟨l⟩ := H
  obtain ⟨hP⟩ := abel_pullback_evaluation P p
  obtain ⟨hQ⟩ := abel_pullback_evaluation P q
  obtain ⟨wP⟩ := point_difference_fibre P p
  obtain ⟨wQ⟩ := point_difference_fibre P q
  let F := Scheme.Modules.pullback (pullback.fst C.hom (𝟙 (Spec (.of K))))
  let j : C ⟶ Over.mk P.J.toBase := Over.homMk P.aj.1 P.aj.2
  have h := P.represents.ext_of_iso (𝟙 _) (schemePoint (p ≫ j)) (schemePoint (q ≫ j))
    ⟨wP.symm ≪≫ F.mapIso (hP.symm ≪≫ (Scheme.Modules.pullback m.left).mapIso l ≪≫ hQ) ≪≫ wQ⟩
  apply (cancel_mono P.toRepresenting.hom).mp
  rw [Category.assoc,Category.assoc,P.abel_comparison]
  exact Over.OverMorphism.ext (congrArg Subtype.val h)

variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)
local notation "J" => geometricJacobian hu

theorem signed_abel_pullback_evaluation (p : FibrePoints u) :
    Nonempty ((Scheme.Modules.pullback (rigidMorphism hu).left).obj (signedEvaluation hu p) ≅
      (WeightedCurvePoints.weightedEquiv_pullback hu p).left.ker.invModule ⊗
        (basepoint hu).left.ker.module) := by
  let := paperProper u
  let := paperIntegral hu
  let := paperSmooth hu
  exact abel_pullback_evaluation (signedPointed hu) (WeightedCurvePoints.weightedEquiv_pullback hu p)

theorem signed_eq_abel_of_evaluations {p q : FibrePoints u}
    (h : evaluationClass hu p = evaluationClass hu q) :
    (rigidDivisors hu).abel p = (rigidDivisors hu).abel q := by
  let := paperProper u
  let := paperIntegral hu
  let := paperSmooth hu
  have z := (lineClass_eq (signedEvaluation_invertible hu p) (signedEvaluation_invertible hu q)).mp
    (congrArg Additive.toMul h)
  rw [rigid_on_points hu p,rigid_on_points hu q]
  exact congrArg Additive.ofMul (equal_abel_of_evaluations (signedPointed hu) z)

/-- No H⁰-dimension or principal-polarization hypothesis is needed.
Every geometric Jacobian class is a single difference on this genus-two curve. -/
theorem signedPolarization_injective : Function.Injective (signedPolarization hu) := by
  intro x y eqn
  obtain ⟨p,q,h⟩ := DeterminantSections.signed_single_difference hu (x-y)
  have zero : signedPolarization hu ((rigidDivisors hu).abel p - (rigidDivisors hu).abel q) = 0 := by
    rw [h,map_sub,eqn,sub_self]
  rw [map_sub,polarization_at_abel,polarization_at_abel,sub_eq_zero,neg_inj] at zero
  exact sub_eq_zero.mp (h.symm.trans (sub_eq_zero.mpr (signed_eq_abel_of_evaluations hu zero)))

end
end ZInQBlueprint.DeterminantAutoduality
#print axioms ZInQBlueprint.DeterminantAutoduality.point_difference_fibre
#print axioms ZInQBlueprint.DeterminantAutoduality.equal_abel_of_evaluations
#print axioms ZInQBlueprint.DeterminantAutoduality.signed_abel_pullback_evaluation
#print axioms ZInQBlueprint.DeterminantAutoduality.signed_eq_abel_of_evaluations
#print axioms ZInQBlueprint.DeterminantAutoduality.signedPolarization_injective
