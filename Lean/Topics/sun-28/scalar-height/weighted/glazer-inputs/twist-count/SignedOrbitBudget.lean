import OrbitCount

/-! Sum the signed orbits across all intrinsic support assignments. -/
namespace ZInQBlueprint.TwistCount
open Finset Sun28.FiveDescent ZInQBlueprint.OriginalHeightCount
open scoped Classical
noncomputable section
set_option maxRecDepth 1800
set_option maxHeartbeats 100000
attribute [local irreducible] D E Sun28.Ordinary.glazerConstant24

theorem certificate_of_four_points {C : ℝ} (c : 0≤C) (point : PointCount C) :
    TwistCountCertificate (C/4) := by
  intro m s f X properties
  rcases X.eq_empty_or_nonempty with empty|live
  · have nonneg : 0 ≤ C := c
    subst X
    simp only [card_empty,Nat.cast_zero]
    positivity
  obtain ⟨base,basein⟩:=live
  obtain ⟨offB,labB,signB,codeB⟩:=properties base basein
  obtain ⟨sd,se,_⟩:=forward offB
  have lifts (x : ↥X) : ∃ q : ℚ×ℚ, q.1≠0 ∧ q.2≠0 ∧
      (E base.num base.den:ℚ)*q.2^2=sextic (D base.num base.den) q.1 ∧
      parameter (D base.num base.den) q.1=(x:ℚ) := by
    obtain ⟨off,lab,sg,cd⟩:=properties x x.2
    obtain ⟨dx,ex⟩:=same_twist off offB lab labB (sg.trans signB.symm) (cd.trans codeB.symm)
    obtain ⟨_,_,u,v,un,vn,eq,back⟩:=forward off
    rw [dx,ex] at eq
    rw [dx] at back
    exact ⟨(u,v),un,vn,eq,back.trans (x:ℚ).num_div_den⟩
  have z:=four_points C point sd se X lifts
  rw [cost_eq labB,codeB] at z
  linarith only [z]

theorem four_lift_count {B K : ℕ} {C : ℝ} (c : 0≤C) (point : PointCount C)
    (threshold : Real.log (B:ℝ)≤((K+1:ℕ):ℝ)^24) :
    ((exceptions B).card:ℝ)≤C*(K:ℝ)*(1+Real.log (K:ℝ))^2498 := by
  have z:=exceptional_count_of_twists (C:=C/4) (by positivity)
    (certificate_of_four_points c point) threshold
  rw [show 4*(C/4)=C by ring] at z
  exact z

end
end ZInQBlueprint.TwistCount
#print axioms ZInQBlueprint.TwistCount.certificate_of_four_points
#print axioms ZInQBlueprint.TwistCount.four_lift_count
