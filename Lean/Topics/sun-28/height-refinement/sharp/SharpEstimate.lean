import PrimeBlocks

namespace Sun28.HeightRefinement.Sharp
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.HeightBudget
noncomputable section
set_option exponentiation.threshold 160
set_option maxRecDepth 8192

/-- Keep the archimedean contribution of the complementary factor separate
from the finite-place contribution of the stripped square. -/
theorem sharp_numeric {T D r h rS P Q k X Z : ℝ} (one : 1≤T) (dpos:1≤D) (budget:D≤T)
    (non : 0≤Z) (test : D^18*(ell T)^4*Z≤625*T^23)
    (rs:0<rS) (pp:1≤P) (p:P≤D^4) (qq:0≤Q) (q:Q≤4*Real.log D)
    (capR:r≤2^12*T*(ell T)^3) (capH:h≤5*2^12*T*(ell T)^3)
    (capS:rS≤(2^12*T*(ell T)^3)*D^2)
    (lower:0≤r) (hn:0≤h) (cost:k≤2^1310800*D^12)
    (out:X≤k*P*rS*(1+logStar rS)*(r+h*Q+5*Real.log (2^32*T)+Z)) :
    X≤2^1310861*T^24 := by
  let E:=ell T
  let F:=k*P*rS*(1+logStar rS)
  have tp:0<T:=by linarith
  have ep:1≤E:=by dsimp [E,ell];linarith [Real.log_nonneg one]
  have lp:0<E:=by linarith
  have dn:0≤D:=by linarith
  have pn:0≤P:=by linarith
  have lgT:Real.log T=E-1:=by dsimp [E,ell];ring
  have lg2:=Real.log_le_sub_one_of_pos (by norm_num:(0:ℝ)<2)
  have reg:rS≤2^12*T^3*E^3:=calc
    _≤_:=capS
    _≤(2^12*T*E^3)*T^2:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ dn budget 2) (by positivity)
    _= _:=by ring
  have lg:=Real.log_le_log rs reg
  rw [Real.log_mul (by positivity) (pow_ne_zero _ lp.ne'),Real.log_mul (by positivity) (pow_ne_zero _ tp.ne'),
    Real.log_pow,Real.log_pow,Real.log_pow] at lg
  norm_num at lg
  have stars:1+logStar rS≤128*E:=by
    unfold logStar;rw [add_max];apply max_le <;> linarith only [ep,lg,lgT,lg2,Real.log_le_sub_one_of_pos lp]
  have ss:0≤1+logStar rS:=by unfold logStar;linarith only [le_max_left (1:ℝ) (Real.log rS)]
  have fb:F≤(2:ℝ)^1310800*2^19*T*(D^18*E^4) := calc
    _≤(2^1310800*D^12)*D^4*((2^12*T*E^3)*D^2)*(128*E):=
      mul_le_mul (mul_le_mul (mul_le_mul cost p pn (by positivity)) capS rs.le (by positivity))
        stars ss (by positivity)
    _= _:=by generalize (2:ℝ)^1310800=V;ring
  let L:=r+h*Q+5*Real.log (2^32*T)
  have legacyCost:k≤2^1310800*D^14:=cost.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ dpos (by decide:12≤14)) (by positivity))
  have main:F*L≤2^1310860*T^24:=budget_numeric one dpos budget rs pp p qq q capR capH capS lower hn legacyCost le_rfl
  have extra:F*Z≤(2:ℝ)^1310860*T^24 := calc
    _≤(2^1310800*2^19*T*(D^18*E^4))*Z:=mul_le_mul_of_nonneg_right fb non
    _= (2^1310800*2^19*T)*(D^18*E^4*Z):=by ac_rfl
    _≤(2^1310800*2^19*T)*(625*T^23):=mul_le_mul_of_nonneg_left test (by positivity)
    _= (2^1310800*(2^19*625))*T^24:=by generalize (2:ℝ)^1310800=V;ring
    _≤ _:=by
      rw [show 1310860=1310800+60 by decide,pow_add]
      gcongr
      norm_num
  change X≤F*(L+Z) at out
  rw [mul_add] at out
  rw [show 1310861=1310860+1 by decide,pow_succ,mul_assoc,two_mul]
  generalize (2:ℝ)^1310860=V at main extra ⊢
  linarith only [out,main,extra]

end
end Sun28.HeightRefinement.Sharp
#print axioms Sun28.HeightRefinement.Sharp.sharp_numeric
