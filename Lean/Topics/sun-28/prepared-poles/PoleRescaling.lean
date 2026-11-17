import SourceTwists
import PoleParameters

namespace Sun28.PreparedPoles
open Sun28.Ordinary ZInQ.RouteK
noncomputable section

/-- Two rational points of abscissa class β give the exact +3 pole branch.
Their ordinates may be zero. The common twist and the two changes of scale
are chosen before the two witnesses e and z. -/
theorem branch_of_twist_points {μ B : ℚ} {β θ n : ℕ} (hn : 0<n)
    {a d : ℚ} (ha : a≠0) (hd : d≠0) (hA : μ*B≠0)
    (A : μ*B=(β:ℚ)*a^2) (H : (μ*B)*(μ*B-B^2)=(θ:ℚ)*d^2)
    (hH : (μ*B)*(μ*B-B^2)≠0)
    (first : TwistPoint β n) (second : TwistPoint β (n*θ)) :
    ∃ e z : ℚ, poleBranch μ B e z := by
  obtain ⟨u,y,hu,ey⟩ := first
  obtain ⟨v,w,hv,ew⟩ := second
  dsimp only at ey ew
  push_cast at ew
  let t:=a/u
  let z:=d*v/u
  have ht : t≠0 := div_ne_zero ha hu
  have hz : z≠0 := div_ne_zero (mul_ne_zero hd hv) hu
  have nt : (n:ℚ)≠0 := by exact_mod_cast hn.ne'
  refine ⟨(n:ℚ)*t^2,z,?_,y*t^3,w*(t*d)^3/z,?_,?_⟩
  · exact mul_ne_zero (mul_ne_zero (mul_ne_zero hA (mul_ne_zero nt (pow_ne_zero _ ht))) hH) hz
  · dsimp only [t]
    rw [A]
    field_simp [hu]
    linear_combination ey
  · rw [H,A]
    dsimp only [t,z]
    field_simp [hu,hv,hd]
    linear_combination ew

end
end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.branch_of_twist_points
