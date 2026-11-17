import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace ZInQBlueprint.DiamondHeight
noncomputable section
set_option exponentiation.threshold 250

/-- The Belyi and isogeny estimates with their two independent arguments:
the degree of the modular curve and the degree of the definition field. -/
structure JacobianComparison (D d h : ℝ) where
  g : ℝ
  J : ℝ
  Z : ℝ
  genus_pos : 1≤g
  genus_bound : g≤D
  belyi : J≤13000000*D^5*g
  isogeny : h+Z ≤ J+2*g^2*(8*g^2*Real.log (7*g)+
    Real.log d+Real.log (max 1 (max (Real.log d) J)))
  complement : -(3/2:ℝ)*g≤Z

theorem jacobian_height {D d h T : ℝ} (one : 1≤T) (dp : 1≤d) (dT : d≤T)
    (DT : D≤T) (F : JacobianComparison D d h) : h≤2^24*T^6 := by
  obtain ⟨g,J,Z,gp,gD,belyi,isog,low⟩:=F
  have Tpos : 0<T:=by linarith
  have Dpos : 0≤D:=by linarith
  have gpos : 0≤g:=by linarith
  have gT:=gD.trans DT
  have T6 : T≤T^6:=by simpa using pow_le_pow_right₀ one (show 1≤6 by decide)
  have lT:=Real.log_le_sub_one_of_pos Tpos
  have jT : J≤13000000*T^6 := belyi.trans <| calc
    13000000*D^5*g ≤13000000*T^5*T := by gcongr
    _ = _ := by ring
  have lg : Real.log (7*g)≤7*T:=by
    have t:=Real.log_le_sub_one_of_pos (by positivity : 0<7*g)
    linarith only [t,gT]
  have ld : Real.log d≤T:=by linarith only [Real.log_le_sub_one_of_pos (by linarith : 0<d),dT]
  have a : T^6≤(2:ℝ)^24*T^6 := le_mul_of_one_le_left (by positivity) (by norm_num)
  have cap : max 1 (max (Real.log d) J)≤(2:ℝ)^24*T^6 :=
    max_le (one.trans (T6.trans a)) (max_le (ld.trans (T6.trans a))
      (jT.trans (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))))
  have lm : Real.log (max 1 (max (Real.log d) J))≤30*T := by
    have v:=Real.log_le_log (by positivity : 0<max 1 (max (Real.log d) J)) cap
    rw [Real.log_mul (by norm_num) (pow_pos Tpos _).ne',Real.log_pow,Real.log_pow] at v
    norm_num only [Nat.cast_ofNat] at v
    linarith only [v,Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2),lT,one]
  have lgpos : 0≤Real.log (7*g):=Real.log_nonneg (by linarith)
  have ldpos : 0≤Real.log d:=Real.log_nonneg dp
  have lmpos : 0≤Real.log (max 1 (max (Real.log d) J)):=Real.log_nonneg (le_max_left ..)
  have err : 2*g^2*(8*g^2*Real.log (7*g)+Real.log d+Real.log (max 1 (max (Real.log d) J))) ≤174*T^6 := calc
    _ ≤ 2*T^2*(8*T^2*(7*T)+T+30*T) := by gcongr
    _ = 112*T^5+62*T^3 := by ring
    _ ≤ 112*T^6+62*T^6 := by
      exact add_le_add (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one (show 5≤6 by decide)) (by norm_num))
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ one (show 3≤6 by decide)) (by norm_num))
    _ = 174*T^6 := by ring
  have lower : -Z≤(3/2:ℝ)*T^6:=by linarith only [low,gT,T6]
  norm_num only [Nat.reducePow, Nat.cast_ofNat] at *
  linarith only [isog,err,lower,jT,pow_nonneg Tpos.le 6]

theorem cm_linear {R h:ℝ} (one : 1≤R)
    (cm : h≤6*R+8*Real.log (14^32*576*max 1 (max (Real.log 576) (6*R)))) :
    h≤854*R := by
  have rp : 0<R:=by linarith
  have ld:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<576)
  have largest : max 1 (max (Real.log 576) (6*R))≤576*R :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  have size : 14^32*576*max 1 (max (Real.log 576) (6*R))≤(2:ℝ)^148*R := calc
    _ ≤ 14^32*576*(576*R) := by gcongr
    _ ≤ _ := by rw [←mul_assoc];gcongr; norm_num
  have z:=Real.log_le_log (by positivity : 0<14^32*576*max 1 (max (Real.log 576) (6*R))) size
  rw [Real.log_mul (by norm_num) rp.ne',Real.log_pow] at z
  norm_num only [Nat.cast_ofNat] at z cm
  linarith only [cm,z,Real.log_two_lt_d9,
    Real.log_le_sub_one_of_pos rp,one]

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.jacobian_height
#print axioms ZInQBlueprint.DiamondHeight.cm_linear
