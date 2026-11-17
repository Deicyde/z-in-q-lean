import MarkedTorelli

/-! The geometric point group is the functor of points of the actual
base-changed Jacobian. Its additive group, point bijection, action of each
group automorphism and sign of the inversion map are canonical. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.GeometricMarking
open MarkedForm MarkedPicard NormalDescent JacobianHeight
noncomputable section
set_option maxHeartbeats 2500000

abbrev basePoint := Over.mk (𝟙 (Spec (.of Qbar)))

abbrev JacobianPoints {u : ℚ} (hu : u∉ZInQ.contactSet) :=
  Additive (basePoint ⟶ (geometricJacobian hu).X)

def geometricPointEquiv {u : ℚ} (hu : u∉ZInQ.contactSet) :
    JacobianPoints hu ≃ Point (geometricJacobian hu).X.hom where
  toFun p := ⟨p.toMul.left, Over.w p.toMul⟩
  invFun p := Additive.ofMul (Over.homMk p.val p.property)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The remaining comparison consists exactly of the Abel--Jacobi map,
generation by differences, and equivalence of the degree-two fibre divisors. -/
structure DivisorData {u : ℚ} (hu : u∉ZInQ.contactSet) where
  abel : FibrePoints u → JacobianPoints hu
  generate : AddSubgroup.closure (Set.range (fun r : FibrePoints u × FibrePoints u =>
    abel r.1-abel r.2))=⊤
  fibres : ∀ p q, abel p+abel (negY (paperForm u (δ u)) p)=
    abel q+abel (negY (paperForm u (δ u)) q)

def DivisorData.comparison {u : ℚ} {hu : u∉ZInQ.contactSet} (D : DivisorData hu) :
    PicardComparison hu (JacobianPoints hu) where
  abel := D.abel
  generate := D.generate
  fibres := D.fibres
  point := geometricPointEquiv hu
  inversion _ := rfl

/-- Actual action of each geometric group automorphism on points, in additive notation. -/
def groupAction {u : ℚ} {hu : u∉ZInQ.contactSet} (a : geometricJacobian hu ≅ geometricJacobian hu) :
    JacobianPoints hu →+ JacobianPoints hu where
  toFun p := Additive.ofMul (p.toMul ≫ a.hom.hom.hom.hom)
  map_zero' := by
    change (1 : basePoint ⟶ (geometricJacobian hu).X) ≫ a.hom.hom.hom.hom=1
    exact MonObj.one_comp _
  map_add' p q := by
    change (p.toMul*q.toMul) ≫ a.hom.hom.hom.hom=_
    exact MonObj.mul_comp p.toMul q.toMul _

abbrev groupMap {u : ℚ} {hu : u∉ZInQ.contactSet} (a : geometricJacobian hu ≅ geometricJacobian hu) :
    SchemeEnd hu := a.hom.hom.hom.hom.left

/-- Strong Torelli in difference form for a specified class of geometric
group automorphisms. Canonical principal polarization is the intended predicate. -/
def PolarizedTorelli {u : ℚ} {hu : u∉ZInQ.contactSet} (D : DivisorData hu)
    (preserves : (geometricJacobian hu ≅ geometricJacobian hu) → Prop) : Prop :=
  ∀ a, preserves a → ∃ t : Lift u (δ u), ∀ p q,
    groupAction a (D.abel p-D.abel q)=D.abel (t.action p)-D.abel (t.action q)

def correction {u : ℚ} {hu : u∉ZInQ.contactSet}
    (preserves : (geometricJacobian hu ≅ geometricJacobian hu) → Prop) (f : SchemeEnd hu) : Prop :=
  ∃ a, preserves a ∧ groupMap a=f

theorem torelli_on_points {u : ℚ} {hu : u∉ZInQ.contactSet} (D : DivisorData hu)
    {preserves : (geometricJacobian hu ≅ geometricJacobian hu) → Prop}
    (T : PolarizedTorelli D preserves) : TorelliOnDifferences D.comparison (correction preserves) := by
  rintro _ ⟨a,ha,rfl⟩
  refine ⟨groupAction a,⟨Over.w _,?_⟩,T a ha⟩
  intro g
  change g.toMul.left ≫ a.hom.hom.hom.hom.left = (g.toMul ≫ a.hom.hom.hom.hom).left
  rfl

/-- Construction of the actual MarkedAction with canonical geometric point group. -/
def markedAction_of_divisors {u : ℚ} {hu : u∉ZInQ.contactSet} (D : DivisorData hu)
    (preserves : (geometricJacobian hu ≅ geometricJacobian hu) → Prop) (T : PolarizedTorelli D preserves)
    (i : realOrder →+* End (geometricJacobian hu)) (hi : Function.Injective i)
    (hlabel : Labelled i (correction preserves)) : MarkedAction u (SixJacobian.jacobian hu) :=
  markedAction D.comparison _ (torelli_on_points D T) i hi hlabel

end
end ZInQBlueprint.GeometricMarking
#print axioms ZInQBlueprint.GeometricMarking.geometricPointEquiv
#print axioms ZInQBlueprint.GeometricMarking.DivisorData.comparison
#print axioms ZInQBlueprint.GeometricMarking.groupAction
#print axioms ZInQBlueprint.GeometricMarking.torelli_on_points
#print axioms ZInQBlueprint.GeometricMarking.markedAction_of_divisors
