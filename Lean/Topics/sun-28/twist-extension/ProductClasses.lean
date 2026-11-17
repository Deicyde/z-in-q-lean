import SignedSurface
import NewTwistPrimes
import FixedLocalSymbols

namespace Sun28.TwistExtension
open PreparedPoles PairedClasses TwistRank
noncomputable section

theorem point_scale {b l c : ℚ} (cn : c≠0) (pt : Point b l) : Point b (l*c^2) := by
  obtain ⟨t,y,tn,h⟩:=pt
  refine ⟨t*c,y*c^3,mul_ne_zero tn cn,?_⟩
  linear_combination c^6*h

/-- A factor is covered by either known section at the fixed twist β. -/
def Factor (β d : ℕ) : Prop := Family β d ∨ SquareSection β d

theorem factor_point {β d : ℕ} (bp : 0<β) (dp : 0<d) (fac : Factor β d) :
    Point (β:ℚ) ((β:ℚ)*d) := by
  have pt : TwistPoint β (β*d) := by
    rcases fac with f|⟨u,v,w,_,vn,h,p|p⟩
    · exact (TwistPrimes.fixed_points_of_family bp dp f).2
    · exact fixed_first_twist bp vn h p
    · exact fixed_first_twist_other bp vn h p
  obtain ⟨t,y,tn,e⟩:=pt
  exact ⟨t,y,tn,by simpa only [Nat.cast_mul] using e⟩

def FactorPair (β θ : ℕ) : Prop := ∃ d e : ℕ, 0<d ∧ 0<e ∧ θ=d*e ∧ Factor β d ∧ Factor β e

theorem factor_pair_points {β θ d e : ℕ} (bp : 0<β) (dp : 0<d) (ep : 0<e)
    (prod : θ=d*e) (f : Factor β d) (g : Factor β e) :
    Point (β:ℚ) ((β:ℚ)*d) ∧ Point (β:ℚ) ((β:ℚ)*d*θ) := by
  have dn : (d:ℚ)≠0:=by exact_mod_cast dp.ne'
  refine ⟨factor_point bp dp f,?_⟩
  have second:=point_scale dn (factor_point bp ep g)
  rw [prod,Nat.cast_mul,show (β:ℚ)*d*((d:ℚ)*e)=(β*e)*d^2 by ring]
  exact second

theorem surface_of_factors {β θ : ℕ} (bp : 0<β) (tp : 0<θ) (cover : FactorPair β θ) :
    Surface (β:ℚ) (θ:ℚ) := by
  obtain ⟨d,e,dp,ep,prod,f,g⟩:=cover
  exact (surface_iff_pair (by exact_mod_cast bp) (by exact_mod_cast tp.ne')).mpr
    ⟨(β:ℚ)*d,mul_ne_zero (by exact_mod_cast bp.ne') (by exact_mod_cast dp.ne'),factor_pair_points bp dp ep prod f g⟩

theorem shared_divisor {β d e : ℕ} (larger : 1<d) : ¬(β*d).Coprime (d*e) := by
  intro co
  have x : d∣1:=co ▸ Nat.dvd_gcd (dvd_mul_left ..) (dvd_mul_right ..)
  exact larger.ne' (Nat.eq_one_of_dvd_one x)

theorem surface_of_old {β θ : ℕ} (bp : 0<β) (tp : 0<θ) (has : Realized β θ) :
    Surface (β:ℚ) (θ:ℚ) := by
  obtain ⟨l,lp,_,_,pt,two⟩:=has
  apply (surface_iff_pair (by exact_mod_cast bp) (by exact_mod_cast tp.ne')).mpr
  obtain ⟨t,y,tn,e⟩:=two
  exact ⟨l,by exact_mod_cast lp.ne',pt,t,y,tn,by simpa only [Nat.cast_mul] using e⟩

end
end Sun28.TwistExtension
#print axioms Sun28.TwistExtension.point_scale
#print axioms Sun28.TwistExtension.factor_point
#print axioms Sun28.TwistExtension.factor_pair_points
#print axioms Sun28.TwistExtension.surface_of_factors
#print axioms Sun28.TwistExtension.shared_divisor
#print axioms Sun28.TwistExtension.surface_of_old
