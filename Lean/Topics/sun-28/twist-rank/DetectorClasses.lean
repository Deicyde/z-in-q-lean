import FixedLocalSymbols
import JointPreparation

namespace Sun28.TwistRank
open ZInQ.RouteK PreparedPoles PairedClasses FixedPreparation ScalarHeight
open Ordinary ContactFactors
noncomputable section

theorem beta_of_scaled_product {B F z : ℚ} {m : ℤ} {β θ : ℕ}
    (h : PreparedClasses B m β θ) (value : B=z^2*F) :
    (β:ℤ)=sqf ((m:ℚ)*F) := by
  obtain ⟨a,an,e⟩:=h.beta_scale
  have unit : (m:ℚ)*B≠0 := by rw [e];exact mul_ne_zero (by exact_mod_cast h.beta_positive.ne') (pow_ne_zero _ an)
  have zn : z≠0 := by rintro rfl; simp [value] at unit
  apply Eq.symm
  apply sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr h.beta_sf) (div_ne_zero an zn)
  push_cast
  field_simp [zn]
  rw [value] at e
  linear_combination e

theorem scalar_class {X : ℤ} {δ W : ℚ} {m : ℤ} {β θ : ℕ}
    (hc : PreparedClasses (signedValue (scalarRadicand (beta X)) δ gamma denominator W) m β θ)
    (pos : 0 < signedValue (scalarRadicand (beta X)) δ gamma denominator W)
    (absolute : δ*scalarRadicand (beta X)=((integerRadicand X).natAbs:ℚ)) :
    0 < m ∧ (β:ℤ)=sqf ((m:ℚ)*((integerRadicand X).natAbs:ℚ)) := by
  obtain ⟨a,an,e⟩:=hc.beta_scale
  have mp : 0 < m := by
    have z : 0<(m:ℚ)*signedValue (scalarRadicand (beta X)) δ gamma denominator W := by
      rw [e];exact mul_pos (by exact_mod_cast hc.beta_positive) (sq_pos_of_ne_zero an)
    exact_mod_cast pos_of_mul_pos_left z pos.le
  refine ⟨mp,?_⟩
  apply beta_of_scaled_product hc
  unfold signedValue
  rw [←absolute]

end
end Sun28.TwistRank
#print axioms Sun28.TwistRank.beta_of_scaled_product
#print axioms Sun28.TwistRank.scalar_class
