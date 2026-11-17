import CharacterField
import PellSectors

namespace Sun28.HeightFibres.Sharp
noncomputable section

def ell (T : ℝ) := 1+Real.log T

theorem ell_four {T:ℝ} (one : 1≤T) : (ell T)^4≤625*T := by
  have tp : 0≤T:=by linarith
  let q:=T^((1:ℝ)/4)
  have qo : 1≤q:=Real.one_le_rpow one (by norm_num)
  have lg:=Real.log_le_rpow_div tp (by norm_num : (0:ℝ)<1/4)
  change Real.log T≤q/(1/4) at lg
  have sum : ell T≤5*q:=by unfold ell;linarith
  have e:q^4=T:=by
    dsimp [q]
    rw [←Real.rpow_mul_natCast tp]
    norm_num
  calc
    _ ≤ (5*q)^4 := pow_le_pow_left₀ (by unfold ell;linarith [Real.log_nonneg one]) sum _
    _ = _ := by rw [mul_pow,e];norm_num

theorem sharp_regulator {D T r:ℝ} (one : 1≤T) (dp:1≤D) (cap:D≤64*T^2)
    (reg:r≤Real.sqrt D*(logStar D)^3) : r≤2^12*T*(ell T)^3 := by
  have tp:0<T:=by linarith
  have de:Real.sqrt D≤8*T := by apply (Real.sqrt_le_left (by positivity)).mpr; nlinarith only [cap]
  have lg:=Real.log_le_log (by linarith : 0<D) cap
  rw [Real.log_mul (by norm_num) (pow_ne_zero _ tp.ne'),Real.log_pow] at lg
  have c : Real.log 64≤6 := by
    rw [show (64:ℝ)=2^6 by norm_num,Real.log_pow];norm_num
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have star : logStar D≤8*ell T:=by
    unfold logStar ell;apply max_le <;> norm_num at lg <;> linarith only [Real.log_nonneg one,lg,c]
  have ps : 0≤logStar D:=(le_trans (by norm_num : (0:ℝ)≤1) (le_max_left ..))
  calc
    _ ≤ _:=reg
    _ ≤ (8*T)*(8*ell T)^3:=mul_le_mul de (pow_le_pow_left₀ ps star _) (pow_nonneg ps _) (by positivity)
    _ = _:=by ring

theorem sharp_numeric {T r J h : ℝ} (one : 1≤T) (rp : 0<r)
    (reg:r≤2^12*T*(ell T)^3) (jp : 0≤J)
    (bound:h≤2^140*r*(1+logStar r)*(r+4*Real.log (2^32*T)+J)) :
    h≤2^170*T^2*(ell T)^7+2^160*T*(ell T)^4*J := by
  let E:=ell T
  have eo:1≤E:=by dsimp [E,ell];linarith [Real.log_nonneg one]
  have ep:0<E:=by linarith
  have tp:0<T:=by linarith
  change r≤2^12*T*E^3 at reg
  have lg:=Real.log_le_log rp reg
  rw [Real.log_mul (by positivity) (pow_ne_zero _ ep.ne'),Real.log_mul (by positivity) tp.ne',Real.log_pow,Real.log_pow] at lg
  have logT:Real.log T=E-1:=by dsimp [E,ell];ring
  have log2:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have s:1+logStar r ≤32*E:=by
    unfold logStar;rw [add_max];apply max_le <;> norm_num at lg <;> linarith only [eo,logT,log2,lg,Real.log_le_sub_one_of_pos ep]
  have logco:Real.log (2^32*T) ≤ 32*E:=by
    rw [Real.log_mul (by positivity) tp.ne',Real.log_pow];norm_num
    linarith only [eo,logT,log2]
  have e3:E≤T*E^3:=by
    calc
      _ ≤ E^3 := by simpa using pow_le_pow_right₀ eo (by decide : 1≤3)
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right one (pow_nonneg ep.le 3)
  have rr:r+4*Real.log (2^32*T)+J≤2^13*T*E^3+J:=by linarith only [reg,logco,e3,eo]
  have yp:0≤r+4*Real.log (2^32*T)+J:=by
    have near : 1≤(2:ℝ)^32*T:=by linarith
    linarith only [Real.log_nonneg near,rp,jp]
  have xp : 0≤1+logStar r:=by unfold logStar;linarith only [le_max_left (1:ℝ) (Real.log r)]
  calc
    _ ≤ _:=bound
    _ ≤ (2:ℝ)^140*(2^12*T*E^3)*(32*E)*(2^13*T*E^3+J):=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left reg (by positivity)) s xp (by positivity)) rr yp (by positivity)
    _ ≤ _:=by
      change _ ≤ 2^170*T^2*E^7+2^160*T*E^4*J
      nlinarith only [mul_nonneg (sq_nonneg T) (pow_nonneg ep.le 7),mul_nonneg (mul_nonneg tp.le (pow_nonneg ep.le 4)) jp]

end
end Sun28.HeightFibres.Sharp
#print axioms Sun28.HeightFibres.Sharp.ell_four
#print axioms Sun28.HeightFibres.Sharp.sharp_regulator
#print axioms Sun28.HeightFibres.Sharp.sharp_numeric
