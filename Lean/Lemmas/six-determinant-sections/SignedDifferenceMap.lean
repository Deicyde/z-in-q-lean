import GenusTwoAbelPairs

/-! The geometric difference morphism on the square of the signed curve. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.DeterminantSections
open SixAbelMap GeometricMarking NormalDescent BinaryCover MarkedForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {u : ℚ} (hu : u ∉ ZInQ.contactSet)

theorem signed_sum (x : JacobianPoints hu) :
    ∃ p q, (rigidDivisors hu).abel p + (rigidDivisors hu).abel q = x := by
  let := sourceIntegral hu
  let := (baseToFunctionField (paperCurve u).hom).toAlgebra
  let := (signedModel hu).curve
  let : Algebra.EssFiniteType Qbar (paperCurve u).left.functionField := by
    have := paper_proper ℚ u
    let : IsProper (paperCurve u).hom :=
      inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ Qbar)))
    exact AlgebraicCurve.essFiniteType_functionField (paperCurve u).hom
  obtain ⟨p,q,h⟩ := abel_sums (rigidPresentation hu) (paper_functionField_genus hu) x
  obtain ⟨p',rfl⟩ := (WeightedCurvePoints.weightedEquiv_pullback hu).surjective p
  obtain ⟨q',rfl⟩ := (WeightedCurvePoints.weightedEquiv_pullback hu).surjective q
  exact ⟨p',q',h⟩

theorem signed_single_difference (x : JacobianPoints hu) :
    ∃ p q, (rigidDivisors hu).abel p - (rigidDivisors hu).abel q = x := by
  let b := (WeightedCurvePoints.weightedEquiv_pullback hu).symm (basepoint hu)
  let A := (rigidDivisors hu).abel
  let n := negY (paperForm u (δ u))
  obtain ⟨p,r,s⟩ := signed_sum hu (x + (A b + A (n b)))
  refine ⟨p,n r,?_⟩
  change A p - A (n r) = x
  calc _ = (A p + A r) - (A r + A (n r)) := by abel
       _ = x := by rw [s,show A r + A (n r) = A b + A (n b) from (rigidDivisors hu).fibres r b]; abel

abbrev curveSquare (u : ℚ) : Over (Spec (.of Qbar)) :=
  Over.mk (pullback.fst (paperCurve u).hom (paperCurve u).hom ≫ (paperCurve u).hom)

def first (u : ℚ) : curveSquare u ⟶ paperCurve u := Over.homMk (pullback.fst _ _) rfl
def second (u : ℚ) : curveSquare u ⟶ paperCurve u :=
  Over.homMk (pullback.snd _ _) pullback.condition.symm

def pairPoint (p q : CurvePoints u) : basePoint ⟶ curveSquare u :=
  Over.homMk (pullback.lift p.left q.left (p.w.trans q.w.symm)) (by
    change pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ _ = _
    rw [pullback.lift_fst_assoc,p.w])

theorem pair_first (p q : CurvePoints u) : pairPoint p q ≫ first u = p :=
  Over.OverMorphism.ext (pullback.lift_fst _ _ _)
theorem pair_second (p q : CurvePoints u) : pairPoint p q ≫ second u = q :=
  Over.OverMorphism.ext (pullback.lift_snd _ _ _)

/-- The order Q−P agrees with the difference convention in Ben-Zvi–Biswas. -/
def differenceMap : curveSquare u ⟶ (geometricJacobian hu).X :=
  (second u ≫ rigidMorphism hu) * (first u ≫ rigidMorphism hu)⁻¹

theorem differenceMap_surjective : Function.Surjective
    (fun x : basePoint ⟶ curveSquare u => x ≫ differenceMap hu) := by
  intro y
  obtain ⟨p,q,h⟩ := signed_single_difference hu (Additive.ofMul y)
  rw [rigid_on_points hu p,rigid_on_points hu q] at h
  refine ⟨pairPoint (WeightedCurvePoints.weightedEquiv_pullback hu q)
      (WeightedCurvePoints.weightedEquiv_pullback hu p),?_⟩
  simp only [differenceMap,MonObj.comp_mul,GrpObj.comp_inv,←Category.assoc,pair_first,pair_second]
  exact congrArg Additive.toMul h

end
end ZInQBlueprint.DeterminantSections
#print axioms ZInQBlueprint.DeterminantSections.signed_sum
#print axioms ZInQBlueprint.DeterminantSections.signed_single_difference
#print axioms ZInQBlueprint.DeterminantSections.differenceMap_surjective
