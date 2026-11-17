import PreparedPoleData
import PoleRescaling

namespace Sun28.PreparedPoles
open Ordinary ScalarHeight FixedPreparation
noncomputable section

/-- Companion Proposition 2.3 for the actual +3 pole polynomial and the
fixed 64 multipliers. The only arithmetic assumption here is paired twist realization. -/
theorem pole_of_prepared (twists : SimultaneousTwists) {B : ℚ} (h : Prepared B) :
    polePredicate smallMultipliers B := by
  obtain ⟨m,β,θ,member,hc⟩ := choose_classes h
  obtain ⟨a,an,A⟩ := hc.beta_scale
  obtain ⟨d,dn,H⟩ := hc.theta_scale
  have live : (m:ℚ)*B ≠ 0 := by
    rw [A]; exact mul_ne_zero (by exact_mod_cast hc.beta_positive.ne') (pow_ne_zero 2 an)
  have nonempty : ((m:ℚ)*B)*((m:ℚ)*B-B^2) ≠ 0 := by
    rw [H]; exact mul_ne_zero (by exact_mod_cast hc.theta_positive.ne') (pow_ne_zero 2 dn)
  obtain ⟨n,hn,_,_,u,v⟩ := twists β θ hc.beta_positive hc.theta_positive hc.beta_sf hc.theta_sf
    hc.disjoint hc.beta_six hc.theta_six hc.beta_mod hc.theta_mod hc.beta_local hc.theta_local
  exact Or.inr ⟨m,member,branch_of_twist_points hn an dn live A H nonempty u v⟩

end
end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.pole_of_prepared
