import OrdinaryEndomorphismAlgebra
import RationalQuaternionAction
import QuaternionCentralizerGeneration

/-! The specified integral action is full at a fibre with scalar centre
and commutative centralizer of its quaternionic action. -/
namespace ZInQBlueprint.LevelThree.IntegralOrder
noncomputable section

variable {E D : Type*} [Ring E] [Module.Finite ℤ E] [Ring D] [Algebra ℚ D] [Nontrivial D]

/-- The two generators have commuting common centralizer in the rational
endomorphism algebra. -/
def commutingQuaternionCentralizer (f : B →ₐ[ℚ] D) : Prop :=
  ∀ (x y : D), f (unitI:B)*x=x*f (unitI:B) → f (unitJ:B)*x=x*f (unitJ:B) →
    f (unitI:B)*y=y*f (unitI:B) → f (unitJ:B)*y=y*f (unitJ:B) → x*y=y*x

/-- Given the actual integral order action and a faithful rational
realization, a scalar centre and a commutative quaternionic centralizer
give the full integral order. No dimension assumption is required. -/
def fullActionOfScalarCenter (a : O →+* E) (incl : E →+* D)
    (faithful : Function.Injective incl)
    (comm : commutingQuaternionCentralizer (extendRationalAction (incl.comp a)))
    (center : ∀ x : D, (∀ y : D, x*y=y*x) → ∃ r : ℚ, x = algebraMap ℚ D r) :
    O ≃+* E := by
  let f := extendRationalAction (incl.comp a)
  have surj := rational_action_surjective_of_scalar_center f comm center
  let e := AlgEquiv.ofBijective f ⟨rational_action_injective f,surj⟩
  exact fullAction a (e.symm.toRingHom.comp incl) (e.symm.injective.comp faithful) (fun x =>
    (congrArg e.symm (extendRationalAction_embed (incl.comp a) x).symm).trans
      (e.symm_apply_apply (embed x)))

theorem fullActionOfScalarCenter_apply (a : O →+* E) (incl : E →+* D)
    (faithful : Function.Injective incl)
    (comm : commutingQuaternionCentralizer (extendRationalAction (incl.comp a)))
    (center : ∀ x : D, (∀ y : D, x*y=y*x) → ∃ r : ℚ, x = algebraMap ℚ D r)
    (x : O) : fullActionOfScalarCenter a incl faithful comm center x = a x := rfl

end
end ZInQBlueprint.LevelThree.IntegralOrder
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.fullActionOfScalarCenter
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.fullActionOfScalarCenter_apply
