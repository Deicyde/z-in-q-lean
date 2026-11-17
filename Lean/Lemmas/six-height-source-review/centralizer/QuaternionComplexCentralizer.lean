import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import QuaternionOrder
import Mathlib.Tactic

/-! The centralizer of a real two-dimensional complex structure. -/
namespace ZInQBlueprint.LevelThree.IntegralOrder
noncomputable section

abbrev RealMatrix₂ := Matrix (Fin 2) (Fin 2) ℝ

/-- A complex structure on a real plane has centralizer exactly the plane
spanned by the identity and the complex structure itself. -/
theorem complexStructure_centralizer (J X : RealMatrix₂) (hJ : J * J = -1) :
    X * J = J * X ↔ ∃ a b : ℝ, X = a • (1 : RealMatrix₂) + b • J := by
  constructor
  · intro h
    have j00 := congrFun (congrFun hJ 0) 0
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply,Fin.sum_univ_two] at j00 h00 h01
    have b : J 0 1 ≠ 0 := by
      intro zero
      rw [zero,zero_mul,add_zero] at j00
      nlinarith [sq_nonneg (J 0 0)]
    refine ⟨X 0 0 - X 0 1 / J 0 1 * J 0 0, X 0 1 / J 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp <;> field_simp [b] <;> nlinarith [h00,h01]
  · rintro ⟨a,b,rfl⟩
    simp [add_mul,mul_add,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]

/-- In particular the complex centralizer is commutative. -/
theorem complexStructure_centralizer_comm (J X Y : RealMatrix₂) (hJ : J*J = -1)
    (hx : X*J = J*X) (hy : Y*J = J*Y) : X*Y = Y*X := by
  obtain ⟨a,b,rfl⟩ := (complexStructure_centralizer J X hJ).mp hx
  simp [add_mul,mul_add,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,hy]

/-- Two rational quaternions commute exactly when their pure parts are
proportional, provided the second quaternion is not scalar. -/
theorem nonscalar_quaternion_centralizer (q p : B)
    (noncentral : q.imI ≠ 0 ∨ q.imJ ≠ 0 ∨ q.imK ≠ 0) :
    p*q = q*p ↔ ∃ a b : ℚ, p = a • (1:B) + b • q := by
  constructor
  · intro h
    have i := congrArg QuaternionAlgebra.imI h
    have j := congrArg QuaternionAlgebra.imJ h
    have k := congrArg QuaternionAlgebra.imK h
    simp at i j k
    rcases noncentral with s | s | s
    · refine ⟨p.re-p.imI/q.imI*q.re,p.imI/q.imI,?_⟩
      ext <;> simp <;> field_simp [s] <;> nlinarith only [i,j,k]
    · refine ⟨p.re-p.imJ/q.imJ*q.re,p.imJ/q.imJ,?_⟩
      ext <;> simp <;> field_simp [s] <;> nlinarith only [i,j,k]
    · refine ⟨p.re-p.imK/q.imK*q.re,p.imK/q.imK,?_⟩
      ext <;> simp <;> field_simp [s] <;> nlinarith only [i,j,k]
  · rintro ⟨a,b,rfl⟩
    simp [add_mul,mul_add,Algebra.smul_mul_assoc,Algebra.mul_smul_comm]

/-- Once a nonscalar rational quaternion commutes with the real complex
structure, every rational quaternion commuting with it lies in the same
specific two-dimensional rational subalgebra. -/
theorem rational_centralizer_of_complexStructure (ρ : B →+* RealMatrix₂)
    (faithful : Function.Injective ρ) (J : RealMatrix₂) (hJ : J*J = -1)
    (q : B) (hq : q.imI ≠ 0 ∨ q.imJ ≠ 0 ∨ q.imK ≠ 0) (hqJ : ρ q * J = J * ρ q)
    (p : B) (hpJ : ρ p * J = J * ρ p) : ∃ a b : ℚ, p = a • (1:B) + b • q := by
  apply (nonscalar_quaternion_centralizer q p hq).mp
  apply faithful
  simpa only [map_mul] using complexStructure_centralizer_comm J (ρ p) (ρ q) hJ hpJ hqJ

end
end ZInQBlueprint.LevelThree.IntegralOrder

#print axioms ZInQBlueprint.LevelThree.IntegralOrder.complexStructure_centralizer
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.complexStructure_centralizer_comm
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.nonscalar_quaternion_centralizer
#print axioms ZInQBlueprint.LevelThree.IntegralOrder.rational_centralizer_of_complexStructure
