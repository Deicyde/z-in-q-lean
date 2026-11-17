import MarkedAbelDeterminant
import RosatiPolynomial

/-! On a rational Jacobian the comparison to a conjugate can be expressed
on the Abel curve. The resulting endomorphism descent needs no determinant,
its rationality, or a statement about all polarized automorphisms. -/
open CategoryTheory AlgebraicGeometry Polynomial NumberField Real
open JacobianVarieties.Picard.Unpointed
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.CMRepair
open BinaryCover AbelianModel NormalDescent QuaternionMarking GeometricMarking SixAbelMap
open WeightedCurvePoints ThetaClass JacobianHeight TorsionHeight MarkedForm SixThetaRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2500000

/-- The ordinary group automorphism obtained after returning from a conjugate
Jacobian is induced on divisor differences by a genuine automorphism of the
curve. Base point translations cancel on these differences. -/
def OnAbelDifferences {C : Over (Spec (.of Qbar))} {A : GroupScheme Qbar}
    (m : C ⟶ A.X) (a : A ≅ A) : Prop :=
  ∃ c : C ≅ C, ∀ p q : base Qbar ⟶ C,
    (Additive.ofMul ((p ≫ m) ≫ (underlying a).hom) : sections A) -
      (Additive.ofMul ((q ≫ m) ≫ (underlying a).hom) : sections A) =
      (Additive.ofMul ((p ≫ c.hom) ≫ m) : sections A) - Additive.ofMul ((q ≫ c.hom) ≫ m)

theorem differences_of_abel_translate {C : Over (Spec (.of Qbar))} {A : GroupScheme Qbar}
    (m : C ⟶ A.X) (a : A ≅ A) (c : C ≅ C) (t : sections A)
    (h : ∀ p : base Qbar ⟶ C, (Additive.ofMul ((p ≫ m) ≫ (underlying a).hom) : sections A) =
      Additive.ofMul ((p ≫ c.hom) ≫ m) + t) : OnAbelDifferences m a := by
  refine ⟨c, fun p q => ?_⟩
  rw [h,h]
  abel

/-- The sextic is assumed rational. The comparison returning the conjugate
Jacobian to that rational model is canonical. The faithful quaternion action
and the particular labelled isomorphism precede the curve comparison. -/
def RationalAbelMarking {C : Over (Spec (.of Qbar))} (A : GroupScheme ℚ)
    (m : C ⟶ ((baseChange (algebraMap ℚ Qbar)).obj A).X) (z : Qbar) : Prop :=
  let J := (baseChange (algebraMap ℚ Qbar)).obj A
  ∃ act : LevelThree.O →+* End J, Function.Injective act ∧
    ∀ σ : Qbar ≃ₐ[ℚ] Qbar, σ z = z → ∃ φ : J ≅ (conjugation σ.toRingEquiv).mapCommGrp.obj J,
      (act sqrtThree).asHom ≫ φ.hom =
        φ.hom ≫ (conjugation σ.toRingEquiv).mapCommGrp.map (act sqrtThree).asHom ∧
      OnAbelDifferences m (φ ≪≫ (rationalGroupComparison A σ).symm)

def CurveCoordinateLifts {u : ℚ} (hu : u ∉ ZInQ.contactSet) : Prop :=
  ∀ c : paperCurve u ≅ paperCurve u, ∃ l : Lift u (δ u), ∀ p : FibrePoints u,
    weightedEquiv_pullback hu (l.action p) = weightedEquiv_pullback hu p ≫ c.hom

/-- The action over the algebraic closure and the descended real action on
the rational Jacobian. The comparison for a single marked lift of each σ
is sufficient. -/
theorem actions_of_rational_abel_marking {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (coordinates : CurveCoordinateLifts hu) {z : Qbar}
    (hz : z^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar))
    (marked : RationalAbelMarking (SixJacobian.jacobian hu) (rigidMorphism hu) z) :
    QuaternionOrderOn (SixJacobian.jacobian hu) ∧ RationalRM (SixJacobian.jacobian hu) := by
  obtain ⟨act, faithful, fixed⟩ := marked
  refine ⟨⟨act,faithful⟩, ?_⟩
  let compatible := OnAbelDifferences (rigidMorphism hu)
  have lifts : PolarizedTorelli (rigidDivisors hu) compatible := by
    intro a ha
    obtain ⟨c,h⟩ := ha
    obtain ⟨l,hl⟩ := coordinates c
    refine ⟨l,fun p q => ?_⟩
    rw [map_sub,rigid_on_points,rigid_on_points,rigid_on_points,rigid_on_points,hl,hl]
    exact h (weightedEquiv_pullback hu p) (weightedEquiv_pullback hu q)
  apply rationalRM_of_marked
  apply marked_of_printed (rigidDivisors hu) compatible lifts (Iso.refl _) act faithful
  intro square σ
  obtain ⟨φ,gen,curve⟩ := fixed σ (fixes_sqrt_of_rational_square hz square σ)
  exact ⟨φ,gen,by simpa [compatible, correctionIso, rationalOnPrinted] using curve⟩

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.differences_of_abel_translate
#print axioms ZInQBlueprint.CMRepair.actions_of_rational_abel_marking
