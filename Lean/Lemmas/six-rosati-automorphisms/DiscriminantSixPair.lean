import DiscriminantSixUnits

/-! The integral unit test is the preservation of just one value of the
primitive Riemann pairing. No dual abelian variety needs to be built. -/
namespace ZInQBlueprint.RosatiSigns
open LevelThree QuaternionAlgebra
noncomputable section

theorem riemann_pair_value (q : B) :
    tracePair q (q*mu) = -2*(dagger q * q).re := by
  simp [tracePair,dagger,trd,mu,muInv]
  ring

theorem primitive_pair : tracePair 1 mu = -2 := by
  norm_num [tracePair,trd,mu,muInv]

theorem normalized_pair_iff (x : O) :
    tracePair (embed x) (embed x*mu) = tracePair 1 mu ↔ x = 1 ∨ x = -1 := by
  constructor
  · obtain ⟨a,b,c,d,rfl⟩ := span_printed x
    intro h
    rw [riemann_pair_value,primitive_pair] at h
    have t := trace_form a b c d
    have value : (dagger (embed (printed a b c d)) * embed (printed a b c d)).re = 1 := by linarith
    rw [value] at t
    have integral : (2*a+c)^2 + 6*(c-d)^2 + 2*(2*b+d)^2 + 3*(2*d-c)^2 = 4 := by
      exact_mod_cast t.symm
    obtain ⟨ha,rfl,rfl,rfl⟩ := integral_minimum a b c d integral
    rcases ha with rfl|rfl
    · left; ext <;> norm_num [printed]
    · right; ext <;> norm_num [printed]
  · intro h
    have unit := (polarized_order_iff x).mpr h
    rw [riemann_pair_value,unit,primitive_pair]
    norm_num

theorem riemann_pair_of_isometry (q : B)
    (h : ∀ x y : B, tracePair (q*x) (q*y) = tracePair x y) :
    tracePair q (q*mu) = tracePair 1 mu := by simpa only [mul_one] using h 1 mu

end
end ZInQBlueprint.RosatiSigns
#print axioms ZInQBlueprint.RosatiSigns.riemann_pair_value
#print axioms ZInQBlueprint.RosatiSigns.primitive_pair
#print axioms ZInQBlueprint.RosatiSigns.normalized_pair_iff
#print axioms ZInQBlueprint.RosatiSigns.riemann_pair_of_isometry
