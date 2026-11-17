import FiniteEndomorphismOrder
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Recover the ordinary integral order from the rational endomorphism
algebra of dimension at most four, keeping the given quaternionic action. -/
namespace ZInQBlueprint.LevelThree.IntegralOrder
open QuaternionAlgebra
noncomputable section

private def i : B := ⟨0,1,0,0⟩
private def j : B := ⟨0,0,1,0⟩
private def k : B := ⟨0,0,0,1⟩

private theorem scalar_projection (x : B) :
    algebraMap ℚ B (24*x.re) = 6*x + 3*(i*x*i) - 2*(j*x*j) + k*x*k := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq,i,j,k] <;> ring

/-- The explicit rational quaternion algebra has no proper two-sided
ideal other than zero. Only the scalar projection and three products are needed. -/
theorem rational_action_injective {D : Type*} [Ring D] [Algebra ℚ D] [Nontrivial D]
    (f : B →ₐ[ℚ] D) : Function.Injective f := by
  have realPart (x : B) (hx : f x = 0) : x.re = 0 := by
    have h := congrArg f (scalar_projection x)
    simp only [AlgHom.commutes,map_add,map_sub,map_mul,map_ofNat,hx,mul_zero,zero_mul,
      add_zero,sub_zero] at h
    have hz : (24:ℚ)*x.re = 0 := (algebraMap ℚ D).injective (by simpa only [map_mul, map_ofNat, map_zero] using h)
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have kernel (x : B) (hx : f x = 0) : x = 0 := by
    have slot (a : B) := realPart (x*a) (by rw [map_mul,hx,zero_mul])
    have hi := slot i
    have hj := slot j
    have hk := slot k
    simp [i,j,k] at hi hj hk
    exact QuaternionAlgebra.ext (realPart x hx) hi hj hk
  intro a b h
  exact sub_eq_zero.mp (kernel (a-b) (by rw [map_sub,h,sub_self]))

/-- If the rational endomorphism algebra has dimension at most four,
the integral order action is already full. The embedding of E in D need
only be faithful; no inverse comparison to the rational quaternions is supplied. -/
def fullActionOfDimension {E D : Type*} [Ring E] [Module.Finite ℤ E]
    [Ring D] [Nontrivial D] [Algebra ℚ D] [FiniteDimensional ℚ D]
    (a : O →+* E) (incl : E →+* D) (injective : Function.Injective incl)
    (rational : B →ₐ[ℚ] D) (commutes : ∀ x, incl (a x) = rational (embed x))
    (dim : Module.finrank ℚ D ≤ 4) : O ≃+* E := by
  have inj := rational_action_injective rational
  have four : Module.finrank ℚ B = 4 := QuaternionAlgebra.finrank_eq_four _ _ _
  have eq : Module.finrank ℚ B = Module.finrank ℚ D :=
    le_antisymm (LinearMap.finrank_le_finrank_of_injective (f := rational.toLinearMap) inj) (four.symm ▸ dim)
  have surj : Function.Surjective rational :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank eq (f:=rational.toLinearMap)).mp inj
  let e := AlgEquiv.ofBijective rational ⟨inj,surj⟩
  exact fullAction a (e.symm.toRingHom.comp incl) (e.symm.injective.comp injective)
    (fun x => (congrArg e.symm (commutes x)).trans (e.symm_apply_apply (embed x)))

theorem fullActionOfDimension_apply {E D : Type*} [Ring E] [Module.Finite ℤ E]
    [Ring D] [Nontrivial D] [Algebra ℚ D] [FiniteDimensional ℚ D]
    (a : O →+* E) (incl : E →+* D) (injective : Function.Injective incl)
    (rational : B →ₐ[ℚ] D) (commutes : ∀ x, incl (a x) = rational (embed x))
    (dim : Module.finrank ℚ D ≤ 4) (x : O) :
    fullActionOfDimension a incl injective rational commutes dim x = a x := rfl

end
end ZInQBlueprint.LevelThree.IntegralOrder
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.rational_action_injective
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.fullActionOfDimension
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.fullActionOfDimension_apply
