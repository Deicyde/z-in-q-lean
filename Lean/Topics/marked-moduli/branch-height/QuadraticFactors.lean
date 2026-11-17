import BranchFields

/-! The six-contact pullback splits the monic sextic into three rational quadratics. -/
namespace ZInQBlueprint.BranchHeight
open Polynomial ThetaPeriod SexticThetaHeight SexticIgusaChart DirectCharts IntegralSextic
noncomputable section

def quad (b c : ℚ) : ℚ[X] := X^2 + C b * X + C c

def firstFactor (u : ℚ) : ℚ[X] :=
  quad (-2*(u+60)/u) (-5*(u+24)*(u+60)/(u*(u+30)))

def secondFactor (u : ℚ) : ℚ[X] :=
  quad (8*(u+15)/(3*(u+20))) (-8*(u+15)*(u+60)/(3*u*(u+20)))

def thirdFactor (u : ℚ) : ℚ[X] :=
  quad (5*(u+24)/(u+30)) (20*(u+15)*(u+24)/(3*(u+20)*(u+30)))

private theorem units {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    u ≠ 0 ∧ u+20 ≠ 0 ∧ u+30 ≠ 0 := by
  simp [ZInQ.contactSet] at hu
  exact ⟨by tauto, fun h => by rcases hu with ⟨_,_,hu,_,_,_⟩; exact hu (by linarith),
    fun h => by rcases hu with ⟨_,_,_,_,hu,_⟩; exact hu (by linarith)⟩

/-- The homogeneous cubic forms defining the parameter may be evaluated at (u,1). -/
theorem affine_parameter {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    parameter u = (10*(u+15)*(u+24)*(u+60))/(3*u*(u+20)*(u+30)) := by
  obtain ⟨h0,h20,h30⟩ := units hu
  let b : ℚ := u.den
  have hb : b ≠ 0 := by dsimp [b]; exact_mod_cast u.den_ne_zero
  have ha : (u.num:ℚ) = u*b := by
    exact ((eq_div_iff hb).mp u.num_div_den.symm).symm
  unfold parameter right left n m
  change (10*((u.num:ℚ)+15*b)*((u.num:ℚ)+24*b)*((u.num:ℚ)+60*b)) /
    (3*(u.num:ℚ)*((u.num:ℚ)+20*b)*((u.num:ℚ)+30*b)) = _
  rw [ha]
  have hmul (k : ℚ) : u*b+k*b = (u+k)*b := by ring
  simp only [hmul]
  field_simp

theorem quad_degree (b c : ℚ) : (quad b c).Monic ∧ (quad b c).natDegree = 2 := by
  unfold quad
  have hd : (X^2+C b*X+C c).natDegree=2 := by compute_degree!
  refine ⟨?_,hd⟩
  unfold Monic leadingCoeff
  rw [hd]
  compute_degree!

/-- The polynomial identity holds for each admissible parameter and every scalar twist. -/
theorem three_quadratics {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ : ℚ) :
    sextic u δ = C (scalar u δ) * (firstFactor u * secondFactor u * thirdFactor u) := by
  unfold sextic
  congr 1
  apply Polynomial.funext
  intro x
  rw [monic_eval,affine_parameter hu]
  simp [firstFactor,secondFactor,thirdFactor,quad,form,alpha,beta,gamma]
  obtain ⟨h0,h20,h30⟩ := units hu
  field_simp
  ring

end
end ZInQBlueprint.BranchHeight
#print axioms ZInQBlueprint.BranchHeight.affine_parameter
#print axioms ZInQBlueprint.BranchHeight.quad_degree
#print axioms ZInQBlueprint.BranchHeight.three_quadratics
