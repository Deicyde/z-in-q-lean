import FinitePell

namespace Sun28.HeightExtension
open Sun28.HeightFibres Sun28.HeightFibres.Sharp
noncomputable section
set_option exponentiation.threshold 2000
set_option maxRecDepth 8192

/-- A range uniform in the field regulator, ideal class number, finite
regulator and multiplicities of the S-integral denominators. -/
theorem finitePell_numeric {T D r h rS P Q f : ℝ} (one : 1≤T) (dpos:1≤D) (sparse:D≤T^4)
    (rs:0<rS) (_pp:1≤P) (p:P≤D^4) (qq:0≤Q) (q:Q≤4*Real.log D)
    (capR:r≤2^12*T*(ell T)^3) (capH:h≤5*2^12*T*(ell T)^3)
    (capS:rS≤(2^12*T*(ell T)^3)*(max 1 (4*Real.log D))^16)
    (lower:0≤r) (hn:0≤h)
    (out:f≤2^512*P*rS*(1+logStar rS)*(r+h*Q+5*Real.log (2^32*T))) :
    f≤2^720*T^24 := by
  let E:=ell T
  have tp:0<T:=by linarith
  have ep:1≤E:=by dsimp [E,ell];linarith [Real.log_nonneg one]
  have lp:0<E:=by linarith
  have lgT:Real.log T=E-1:=by dsimp [E,ell];ring
  have lg2:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
  have lgD:=Real.log_le_log (by linarith : 0<D) sparse
  rw [Real.log_pow] at lgD
  norm_num at lgD
  have qp:Q≤16*E:=by linarith only [q,lgD,lgT]
  have regfac:max 1 (4*Real.log D)≤16*E:=max_le (by linarith) (by linarith only [lgD,lgT])
  change rS≤(2^12*T*E^3)*(max 1 (4*Real.log D))^16 at capS
  change r≤2^12*T*E^3 at capR
  change h≤5*2^12*T*E^3 at capH
  have pq:P≤T^16:=p.trans (by simpa only [←pow_mul] using pow_le_pow_left₀ (by linarith) sparse 4)
  have reg:rS≤2^76*T*E^19:=calc
    rS ≤ _:=capS
    _ ≤ (2^12*T*E^3)*(16*E)^16:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_trans (by norm_num : (0:ℝ)≤1) (le_max_left ..)) regfac _) (by positivity)
    _ = _:=by ring
  have lg:=Real.log_le_log rs reg
  rw [Real.log_mul (by positivity) (pow_ne_zero _ lp.ne'),Real.log_mul (by positivity) tp.ne',Real.log_pow,Real.log_pow] at lg
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
    rw [show (5:ℝ)*2^12*T*E^3*(16*E)=80*2^12*T*E^4 by ring] at hq
    linarith only [capR,hq,coef,e4,b3,ep]
  have cpos : 0≤Real.log (2^32*T):=Real.log_nonneg (by linarith)
  have pos:0≤r+h*Q+5*Real.log (2^32*T):=by linarith only [lower,mul_nonneg hn qq,cpos]
  have st0:0≤1+logStar rS:=by unfold logStar;linarith only [le_max_left (1:ℝ) (Real.log rS)]
  have powers:E^24≤(625:ℝ)^6*T^6:=by
    have hp:=pow_le_pow_left₀ (pow_nonneg lp.le 4) (ell_four one) 6
    simpa only [←pow_mul,mul_pow] using hp
  calc
    _ ≤ _:=out
    _ ≤ (2:ℝ)^512*T^16*(2^76*T*E^19)*(128*E)*(2^20*T*E^4) :=
      mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left pq (by positivity))
        reg rs.le (by positivity)) stars st0 (by positivity)) high pos (by positivity)
    _ = 2^615*T^18*E^24:=by ring
    _ ≤ 2^615*T^18*(625^6*T^6):=mul_le_mul_of_nonneg_left powers (by positivity)
    _ = (2^615*625^6)*T^24:=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_right (by exact_mod_cast (by decide : (2:ℕ)^615*625^6≤2^720)) (pow_nonneg tp.le _)

end
end Sun28.HeightExtension
#print axioms Sun28.HeightExtension.finitePell_numeric
