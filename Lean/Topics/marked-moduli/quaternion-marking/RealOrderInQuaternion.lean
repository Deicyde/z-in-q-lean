import QuaternionOrder

/-! The designated real order in the maximal order of discriminant six.
Baba--Granath, §3, uses j + ij as its generator. -/
namespace ZInQBlueprint.QuaternionMarking
open LevelThree

/-- In the basis 1, ω, i, ωi, with ω=(1+j)/2, the generator is
−1 + 2ω + i − 2ωi. -/
def sqrtThree : O := ⟨-1, 2, 1, -2⟩

theorem embed_sqrtThree : embed sqrtThree = (⟨0, 0, 1, 1⟩ : B) := by
  ext <;> norm_num [embed,sqrtThree]

theorem sqrtThree_sq : sqrtThree ^ 2 = 3 := by
  let : DecidableEq O := (QuaternionAlgebra.equivProd (-1 : ℤ) 1 2).decidableEq
  decide

/-- The integral inclusion a+b√3 ↦ a+b(j+ij). -/
def realInclusion : QuadraticAlgebra ℤ 3 0 →+* O where
  toFun x := ⟨x.re-x.im,2*x.im,x.im,-2*x.im⟩
  map_zero' := by ext <;> rfl
  map_one' := by ext <;> rfl
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp <;> ring

theorem inclusion_generator : realInclusion QuadraticAlgebra.omega = sqrtThree := rfl

theorem inclusion_injective : Function.Injective realInclusion := by
  intro x y e
  have hi : x.im = y.im := congrArg QuaternionAlgebra.imJ e
  have hr : x.re - x.im = y.re - y.im := congrArg QuaternionAlgebra.re e
  exact QuadraticAlgebra.ext (by omega) hi

end ZInQBlueprint.QuaternionMarking
#print axioms ZInQBlueprint.QuaternionMarking.embed_sqrtThree
#print axioms ZInQBlueprint.QuaternionMarking.sqrtThree_sq
#print axioms ZInQBlueprint.QuaternionMarking.inclusion_generator
#print axioms ZInQBlueprint.QuaternionMarking.inclusion_injective
