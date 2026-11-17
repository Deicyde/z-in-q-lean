import SignedAbelSeparation
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! Geometric point separation and the unramified diagonal for the actual proper Abel map. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open JacobianVarieties.Picard.Unpointed GoodReductionJacobian
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.SixAbelMap
noncomputable section
open BinaryCover GeometricMarking NormalDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

/-- The scheme morphism in the signed curve's Abel presentation. -/
def abelMorphism {u : ℚ} (hu : u ∉ ZInQ.contactSet) : paperCurve u ⟶ (geometricJacobian hu).X :=
  letI := sourceIntegral hu
  letI := (baseToFunctionField (paperCurve u).hom).toAlgebra
  letI := (signedModel hu).curve
  (realization hu).morphism

/-- Proper morphisms over an algebraically closed field which separate geometric points
are closed immersions as soon as they are formally unramified. The proof checks the
diagonal on closed points of the full scheme-theoretic fibre product. -/
theorem closed_of_point_separation {K : Type} [Field K] [IsAlgClosed K]
    {X Y : Scheme.{0}} (c : X ⟶ Spec (.of K)) (d : Y ⟶ Spec (.of K)) (f : X ⟶ Y)
    (comm : f ≫ d = c) [IsProper f] [LocallyOfFiniteType c] [FormallyUnramified f]
    (hinj : ∀ (p q : Spec (.of K) ⟶ X), p ≫ c = 𝟙 _ → q ≫ c = 𝟙 _ →
      p ≫ f = q ≫ f → p = q) : IsClosedImmersion f := by
  let k := pullback.fst f f ≫ c
  let : JacobsonSpace (pullback f f : Scheme) := LocallyOfFiniteType.jacobsonSpace k
  let δ := pullback.diagonal f
  have hc : IsClosed (Set.range δ) := δ.isClosedEmbedding.isClosed_range
  have hall : closedPoints (pullback f f : Scheme) ⊆ Set.range δ := by
    intro x hx
    let t := pointOfClosedPoint k x hx
    have tw : t ≫ k = 𝟙 _ := pointOfClosedPoint_comp k x hx
    let p := t ≫ pullback.fst f f
    let q := t ≫ pullback.snd f f
    have hh : p ≫ f = q ≫ f := by simp only [p,q,Category.assoc,pullback.condition]
    have hp : p ≫ c = 𝟙 _ := by simpa only [p,Category.assoc,k] using tw
    have hq : q ≫ c = 𝟙 _ := by rw [←comm,←Category.assoc,←hh,Category.assoc,comm,hp]
    have h := hinj p q hp hq hh
    have hpt : p ≫ δ = t := by
      apply pullback.hom_ext
      · simp only [δ,Category.assoc,pullback.diagonal_fst,Category.comp_id]; rfl
      · simpa only [δ,Category.assoc,pullback.diagonal_snd,Category.comp_id] using h
    let o := IsLocalRing.closedPoint K
    exact ⟨p o, (congrArg (fun m : Spec (.of K) ⟶ _ => m o) hpt).trans (pointOfClosedPoint_apply k x hx o)⟩
  have dense : Dense (closedPoints (pullback f f : Scheme)) := by
    rw [dense_iff_closure_eq]
    simpa using JacobsonSpace.closure_inter_closedPoints_eq_closure
      (X := (pullback f f : Scheme)) isOpen_univ.isLocallyClosed
  have surj : Surjective δ := by
    rw [surjective_iff, ← Set.range_eq_univ, ← hc.closure_eq]
    exact (dense.mono hall).closure_eq
  have : IsIso δ := (isIso_iff_isOpenImmersion_and_surjective δ).mpr ⟨inferInstance,surj⟩
  exact (IsClosedImmersion.iff_isProper_and_mono f).mpr
    ⟨inferInstance,(pullback.isIso_diagonal_iff f).mp this⟩

/-- The precise remaining infinitesimal premise for Milne's proposition on this curve. -/
theorem abel_closed_of_formallyUnramified {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (h : FormallyUnramified (abelMorphism hu).left) : IsClosedImmersion (abelMorphism hu).left := by
  let C := paperCurve u
  let J := (geometricJacobian hu).X
  let a := abelMorphism hu
  have := paper_proper ℚ u
  let : IsProper C.hom := inferInstanceAs
    (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
  let : IsProper (SixJacobian.jacobian hu).X.hom := (SixJacobian.isAbelian hu).proper
  let : IsProper J.hom := inferInstanceAs
    (IsProper (pullback.snd (SixJacobian.jacobian hu).X.hom (specExtension ℚ Qbar)))
  let : IsProper (a.left ≫ J.hom) := by rw [Over.w]; infer_instance
  let : IsProper a.left := IsProper.of_comp a.left J.hom
  apply closed_of_point_separation C.hom J.hom a.left (Over.w a)
  intro p q hp hq hpq
  let P : CurvePoints u := Over.homMk p hp
  let Q : CurvePoints u := Over.homMk q hq
  have h : abel hu P = abel hu Q := by
    change Additive.ofMul (P ≫ a) = Additive.ofMul (Q ≫ a)
    apply congrArg Additive.ofMul
    exact Over.OverMorphism.ext hpq
  exact congrArg (fun t : CurvePoints u => t.left) (abel_injective hu h)

end
end ZInQBlueprint.SixAbelMap
#print axioms ZInQBlueprint.SixAbelMap.closed_of_point_separation
#print axioms ZInQBlueprint.SixAbelMap.abel_closed_of_formallyUnramified
