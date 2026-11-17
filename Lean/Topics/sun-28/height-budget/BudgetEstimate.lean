import FullPell

namespace Sun28.HeightBudget
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.FiveMarkUnits Sun28.Ordinary
noncomputable section
set_option exponentiation.threshold 140

theorem budget_numeric {T D r h rS P Q c f : ℝ} (one : 1≤T) (dpos:1≤D) (budget:D≤T)
    (rs:0<rS) (pp:1≤P) (p:P≤D^4) (qq:0≤Q) (q:Q≤4*Real.log D)
    (capR:r≤2^12*T*(ell T)^3) (capH:h≤5*2^12*T*(ell T)^3)
    (capS:rS≤(2^12*T*(ell T)^3)*D^2)
    (lower:0≤r) (hn:0≤h) (cost:c≤2^1310800*D^14)
    (out:f≤c*P*rS*(1+logStar rS)*(r+h*Q+5*Real.log (2^32*T))) :
    f≤2^1310860*T^24 := by
  let E:=ell T
  have tp:0<T:=by linarith
  have ep:1≤E:=by dsimp [E,ell];linarith [Real.log_nonneg one]
  have lp:0<E:=by linarith
  have lgT:Real.log T=E-1:=by dsimp [E,ell];ring
  have lg2:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
  have lgD:=Real.log_le_log (by linarith:0<D) budget
  have qp:Q≤4*E:=by linarith only [q,lgD,lgT]
  have pq:P≤T^4:=p.trans (pow_le_pow_left₀ (by linarith) budget _)
  have reg:rS≤2^12*T^3*E^3:=calc
    _ ≤ _:=capS
    _ ≤ (2^12*T*E^3)*T^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) budget _) (by positivity)
    _ = _:=by ring
  have lg:=Real.log_le_log rs reg
  rw [Real.log_mul (by positivity) (pow_ne_zero _ lp.ne'),Real.log_mul (by positivity) (pow_ne_zero _ tp.ne'),
    Real.log_pow,Real.log_pow,Real.log_pow] at lg
  norm_num at lg
  have stars:1+logStar rS≤128*E:=by
    unfold logStar;rw [add_max];apply max_le <;> linarith only [ep,lg,lgT,lg2,Real.log_le_sub_one_of_pos lp]
  have coef:Real.log (2^32*T)≤32*E:=by
    rw [Real.log_mul (by positivity) tp.ne',Real.log_pow];norm_num;linarith only [ep,lgT,lg2]
  have hq:=mul_le_mul capH qp qq (show 0≤5*2^12*T*E^3 by positivity)
  have e3:E^3≤E^4:=pow_le_pow_right₀ ep (by decide)
  have b3:=mul_le_mul_of_nonneg_left e3 tp.le
  have e4:E≤T*E^4 := calc
    _ ≤ E^4:=by simpa using pow_le_pow_right₀ ep (by decide:1≤4)
    _ ≤ _:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right one (pow_nonneg lp.le 4)
  have high:r+h*Q+5*Real.log (2^32*T)≤2^20*T*E^4:=by
    rw [show (5:ℝ)*2^12*T*E^3*(4*E)=20*2^12*T*E^4 by ring] at hq
    linarith only [capR,hq,coef,e4,b3,ep]
  have cpos : 0≤Real.log (2^32*T):=Real.log_nonneg (by linarith)
  have pos:0≤r+h*Q+5*Real.log (2^32*T):=by linarith only [lower,mul_nonneg hn qq,cpos]
  have st0:0≤1+logStar rS:=by unfold logStar;linarith only [le_max_left (1:ℝ) (Real.log rS)]
  have powers:E^8≤(625:ℝ)^2*T^2:=by
    have hp:=pow_le_pow_left₀ (pow_nonneg lp.le 4) (ell_four one) 2
    simpa only [←pow_mul,mul_pow] using hp
  let V:ℝ:=2^1310800
  have vc:0≤V:=by positivity
  have cp:c≤V*T^14:=cost.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) budget _) vc)
  dsimp only [V] at cp vc
  generalize same : (2:ℝ)^1310800 = U at cp vc
  change _ ≤ 2^(1310800+60)*T^24
  rw [pow_add,same]
  calc
    _ ≤ _:=out
    _ ≤ U*T^14*T^4*(2^12*T^3*E^3)*(128*E)*(2^20*T*E^4) :=
      mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul cp pq (by linarith) (by positivity))
        reg rs.le (by positivity)) stars st0 (by positivity)) high pos (by positivity)
    _ = U*(2^39)*(T^22*E^8):=by ring
    _ ≤ U*(2^39)*(T^22*(625^2*T^2)):=by gcongr
    _ = (U*2^39*625^2)*T^24:=by ring
    _ ≤ (U*2^60)*T^24:=by
      rw [mul_assoc U]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by norm_num : (2:ℝ)^39*625^2≤2^60) vc) (pow_nonneg tp.le _)

end
end Sun28.HeightBudget
#print axioms Sun28.HeightBudget.budget_numeric
