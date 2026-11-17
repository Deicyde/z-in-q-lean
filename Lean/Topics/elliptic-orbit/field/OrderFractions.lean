import QuadraticFieldBridge
import FractionArithmetic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.NumberTheory.NumberField.Basic

namespace EllipticOrbit.Field
open EllipticHeight.QuadraticInt

private theorem asOrder_add (a b : R) : asOrder (plus a b)=asOrder a+asOrder b := rfl
private theorem asOrder_mul (a b : R) : asOrder (mul a b)=asOrder a*asOrder b := rfl

/-- The field of literal quadratic coefficient pairs admits primitive presentations in
Mathlib's quadratic order, with the two integral Bézout multipliers. -/
theorem primitive_presentation (z : K) :
    ∃ a b u v : O, b≠0 ∧ z*orderMap b=orderMap a ∧ a*u+b*v=1 := by
  obtain ⟨a,b,nz,rep,u,v,bez⟩:=EllipticHeight.Reduction.primitive_coefficients (coeffs z)
  refine ⟨asOrder a,asOrder b,asOrder u,asOrder v,?_,?_,?_⟩
  · intro h
    exact nz (congrArg (fun p : O=>(p.re,p.im)) h)
  · simpa using (fraction_iff (coeffs z) a b).mp rep
  · have h:=congrArg asOrder bez
    simpa only [asOrder_add,asOrder_mul] using h

instance orderAlgebra : Algebra O K := orderMap.toAlgebra
theorem algebraMap_order : algebraMap O K=orderMap := rfl

instance orderFaithful : FaithfulSMul O K :=
  (faithfulSMul_iff_algebraMap_injective O K).mpr orderMap_injective

instance fractionField : IsFractionRing O K := by
  apply IsFractionRing.of_field
  intro z
  obtain ⟨a,b,_,_,nz,eq,_⟩:=primitive_presentation z
  exact ⟨a,b,(eq_div_iff ((map_ne_zero_iff orderMap orderMap_injective).mpr nz)).mpr eq⟩

private theorem coefficient_finite (m : Module ℚ K) : @Module.Finite ℚ K _ _ m := by
  have transfer (n : Module ℚ K) (h : @Module.Finite ℚ K _ _ n) : @Module.Finite ℚ K _ _ m := by
    cases Subsingleton.elim n m
    exact h
  letI basisModule : Module ℚ K := QuadraticAlgebra.instModule
  exact transfer basisModule (Module.Finite.of_basis (QuadraticAlgebra.basis (2:ℚ) 0))

instance numberField : NumberField K where
  to_charZero := inferInstance
  to_finiteDimensional := coefficient_finite _

theorem coefficient_degree : Module.finrank ℚ K=2 := by
  have transfer (m n : Module ℚ K) (h : @Module.finrank ℚ K _ _ m=2) : @Module.finrank ℚ K _ _ n=2 := by
    cases Subsingleton.elim m n
    exact h
  exact transfer _ _ (QuadraticAlgebra.finrank_eq_two (2:ℚ) 0)

#print axioms primitive_presentation
#print axioms fractionField
#print axioms numberField
#print axioms coefficient_degree
end EllipticOrbit.Field
