import QuadraticFactors

/-! Rational square classes of the three quadratic factors. -/
namespace ZInQBlueprint.BranchHeight
open Polynomial
noncomputable section

def rootClass₁ (u : ℚ) := 6*(u+15)*(u+20)*(u+30)*(u+60)
def rootClass₂ (u : ℚ) := 10*u*(u+15)*(u+24)*(u+30)
def rootClass₃ (u : ℚ) := -15*u*(u+20)*(u+24)*(u+60)

theorem rootClasses_product (u : ℚ) :
    rootClass₁ u * rootClass₂ u * rootClass₃ u = -(30*SixContact.F u)^2 := by
  unfold rootClass₁ rootClass₂ rootClass₃ SixContact.F
  ring

theorem quad_discriminant (b c : ℚ) : (quad b c).discr = b^2-4*c := by
  obtain ⟨hm,hd⟩ := quad_degree b c
  let f := quad b c
  have hp : 0 < f.degree := natDegree_pos_iff_degree_pos.mp (by change 0 < (quad b c).natDegree; rw [hd]; decide)
  have h := resultant_deriv hp
  change f.natDegree=2 at hd
  rw [hd,hm.leadingCoeff] at h
  norm_num only [Nat.reduceSub,Nat.reduceMul,Nat.reduceDiv,pow_one,neg_one_mul,mul_one] at h
  have df : f.derivative = C (2:ℚ)*(X+C (b/2)) := by
    have hb : C (b/2 : ℚ) = (C b : ℚ[X]) * C (1/2:ℚ) := by rw [← C_mul]; congr 1; ring
    have h2 : (C (1/2:ℚ):ℚ[X]) * C (2:ℚ) = 1 := by rw [← C_mul]; norm_num
    simp [f,quad,derivative_pow,derivative_mul, hb, mul_add]
    simp only [one_div] at h2
    linear_combination -C b * h2
  rw [df,resultant_C_mul_right,resultant_X_add_C_right _ _ _ hd.le] at h
  simp [f,quad] at h
  unfold quad
  linear_combination h

theorem factor_discriminants {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (firstFactor u).discr = (2/(u*(u+30)))^2 * rootClass₁ u ∧
    (secondFactor u).discr = (4/(3*u*(u+20)))^2 * rootClass₂ u ∧
    (thirdFactor u).discr = (1/(3*(u+20)*(u+30)))^2 * rootClass₃ u := by
  have hn : u ≠ 0 ∧ u+20 ≠ 0 ∧ u+30 ≠ 0 := by
    simp [ZInQ.contactSet] at hu
    rcases hu with ⟨h0,_,h20,_,h30,_⟩
    exact ⟨h0,fun h => h20 (by linarith),fun h => h30 (by linarith)⟩
  obtain ⟨h0,h20,h30⟩ := hn
  simp only [firstFactor,secondFactor,thirdFactor,quad_discriminant,rootClass₁,rootClass₂,rootClass₃]
  constructor
  · field_simp
    ring
  constructor <;> field_simp <;> ring

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.rootClasses_product
#print axioms ZInQBlueprint.BranchHeight.quad_discriminant
#print axioms ZInQBlueprint.BranchHeight.factor_discriminants
