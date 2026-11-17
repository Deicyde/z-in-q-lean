import Std
namespace WitnessTransfer
open Lean.Grind

theorem scalar_comm {G : Type} [IntModule G] (a b : Int) (P : G) : a • (b • P)=b • (a • P) := by
  rw [← IntModule.mul_zsmul,← IntModule.mul_zsmul,Int.mul_comm]

private theorem compare {G : Type} [IntModule G] (m u : Int) (P T : G) (kill : (2:Int) • T=0) :
    m • (u • ((2:Int) • P))=(2*u) • (m • P+T) := by
  have tk : (2*u) • T=0 := by rw [Int.mul_comm,IntModule.mul_zsmul,kill,IntModule.zsmul_zero]
  rw [IntModule.zsmul_add,tk,AddCommMonoid.add_zero,← IntModule.mul_zsmul,
      ← IntModule.mul_zsmul,← IntModule.mul_zsmul]
  congr 1
  grobner

/-- The two source equalities of actual group points hold for an arbitrary
two-torsion translate and signed, including odd, multipliers. -/
theorem source_points {G : Type} [IntModule G] (m u n : Int) (P₀ T : G) (kill : (2:Int) • T=0) :
    let P:=(2:Int) • P₀
    let H:=m • P₀+T
    m • (u • P)=(2*u) • H ∧
      (m-2) • (u • P-n • P)=(2*(u-n)) • (H-P) := by
  dsimp only
  refine ⟨compare _ _ _ _ kill,?_⟩
  have h : m • P₀+T-(2:Int) • P₀=(m-2) • P₀+T := by
    rw [IntModule.sub_zsmul,AddCommGroup.sub_eq_add_neg,AddCommGroup.sub_eq_add_neg]
    rw [AddCommMonoid.add_assoc,AddCommMonoid.add_comm T,← AddCommMonoid.add_assoc]
  rw [← IntModule.sub_zsmul,h]
  exact compare _ _ _ _ kill

#print axioms scalar_comm
#print axioms source_points
end WitnessTransfer
