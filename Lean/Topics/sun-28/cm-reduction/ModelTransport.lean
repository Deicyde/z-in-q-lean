import ZInQKernel.Density.Description
import ZInQKernel.Model.Descent.PointCounts

namespace Sun28.CMReduction
open ZInQ ZInQ.Density

/-- Twisting the short coefficient by a fourth power preserves its point count. -/
theorem pointCount_fourth {p : ℕ} [Fact p.Prime] (odd : p≠2) (u A : ZMod p) (unit : u≠0) :
    pointCount p (u^4*A)=pointCount p A := by
  apply (Nat.cast_inj (R:=ℤ)).mp
  rw [pointCount_eq odd,pointCount_eq odd,show u^4=(u^2)^2 by ring,
    jac_sq_mul (pow_ne_zero 2 unit),quadraticChar_sq_one' unit,one_mul]

/-- The unit from Sun's short curve to the public generator model. -/
theorem transport_unit {p : ℕ} [Fact p.Prime] {r : ZMod p} (hr : r^2=2) :
    (3-2*r)*(3+2*r)=1 ∧ (3-2*r)^2*(3-r)=75-53*r := by
  constructor
  · linear_combination (-4 : ZMod p) * hr
  · linear_combination (24-4*r) * hr

theorem pointCount_transport {p : ℕ} [Fact p.Prime] (odd : p≠2) {r : ZMod p} (hr : r^2=2) :
    pointCount p (-(75-53*r)^2)=pointCount p (-(3-r)^2) ∧
    pointCount p (-(75+53*r)^2)=pointCount p (-(3+r)^2) := by
  have step (s : ZMod p) (hs : s^2=2) : pointCount p (-(75-53*s)^2)=pointCount p (-(3-s)^2) := by
    obtain ⟨inv,eq⟩:=transport_unit hs
    have nz : 3-2*s≠0 := by intro h; rw [h,zero_mul] at inv; exact zero_ne_one inv
    rw [← eq,show -((3-2*s)^2*(3-s))^2=(3-2*s)^4 * (-(3-s)^2) by ring]
    exact pointCount_fourth odd _ _ nz
  refine ⟨step r hr,?_⟩
  simpa only [mul_neg,sub_neg_eq_add] using step (-r) (by simpa using hr)

end Sun28.CMReduction
#print axioms Sun28.CMReduction.pointCount_fourth
#print axioms Sun28.CMReduction.transport_unit
#print axioms Sun28.CMReduction.pointCount_transport
