import QuaternionToricRank

namespace ZInQBlueprint.LevelThree.IntegralOrder

/-- Any unital action of the printed order on a nonzero rational algebra yields
the inclusion of a nonsplit quaternion algebra in LSSV, Lemma 4.1. -/
theorem rational_quaternion_inclusion {D : Type*} [Ring D] [Algebra ℚ D] [Nontrivial D]
    (rho : O →+* D) : Function.Injective (extendRationalAction rho) := by
  intro x y h
  by_contra ne
  have unit := (isUnit_of_quaternion_ne_zero (sub_ne_zero.mpr ne)).map
    (extendRationalAction rho).toMonoidHom
  change IsUnit (extendRationalAction rho (x-y)) at unit
  rw [map_sub,h,sub_self] at unit
  exact not_isUnit_zero unit

end ZInQBlueprint.LevelThree.IntegralOrder
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.rational_quaternion_inclusion
