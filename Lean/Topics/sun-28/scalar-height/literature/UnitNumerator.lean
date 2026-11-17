import ScalarEstimates

namespace Sun28.ScalarPencil
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.Ordinary Sun28.FiveMarkUnits
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK Height
open private int_height from ContactHeight
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 1200

def totalRadical (x:ℚ) := heightRadical (beta x).num (beta x).den

theorem totalRadical_eq (x:ℚ) : totalRadical x=cutoffProduct*primeProduct (scalarPrimes x):=by
  simp only [totalRadical,heightRadical,oddProduct,oddSupport,scalar_support_exact]

theorem of_small_numerator (pell:PublishedPell312) (regulator:Regulator35) (disc:ConductorDiscriminants)
    (x:ℚ) (nonzero:x≠0) (test:small (totalRadical x) (numberLog x.num)) :
    logHeight₁ (beta x)≤glazerConstant24*(primeProduct (scalarPrimes x):ℝ)^24 := by
  let T:ℝ:=totalRadical x
  let E:=ell T
  let F:=numberLog x.num
  have den:=denominator_log pell regulator disc x nonzero
  have nh:=frac_height (Rat.num_ne_zero.mpr nonzero) x.num_div_den.symm
  have bn:(x.den:ℤ)≠0:=by exact_mod_cast x.den_nz
  have ib:=int_height bn
  push_cast at ib
  rw [ib] at nh
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd _ _))
  have tp:0≤T:=by linarith
  have eo:1≤E:=by dsimp [E,ell];linarith [Real.log_nonneg t]
  have ep:0≤E:=by linarith
  have eT:E≤T:=by dsimp [E,ell];linarith only [Real.log_le_sub_one_of_pos (lt_of_lt_of_le (by norm_num) t)]
  have A1 : T^2*E^7≤T^24:=calc
    _ ≤ T^2*T^7:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ep eT _) (sq_nonneg T)
    _ = T^9:=by ring
    _ ≤ _:=pow_le_pow_right₀ t (by decide)
  have A2 : T*E^4≤T^24:=calc
    _ ≤ T*T^4:=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ep eT _) tp
    _ = T^5:=by ring
    _ ≤ _:=pow_le_pow_right₀ t (by decide)
  change E^4*F≤625*T^23 at test
  have pr:T*E^4*F≤625*T^24:=calc
    _ = T*(E^4*F):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left test tp
    _ = _:=by ring
  have ww:1≤T*E^4:=one_le_mul_of_one_le_of_one_le t (one_le_pow₀ eo)
  have ff:F≤T*E^4*F:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right ww (nonneg_numberLog (Rat.num_ne_zero.mpr nonzero))
  change numberLog (x.den:ℤ)≤2^170*T^2*E^7+2^160*T*E^4*(2*F+6) at den
  rw [show (2:ℝ)^170*T^2*E^7=2^170*(T^2*E^7) by ring,
    show (2:ℝ)^160*T*E^4*(2*F+6)=2*2^160*(T*E^4*F)+6*2^160*(T*E^4) by ring] at den
  change logHeight₁ (beta x)≤2*F+2*numberLog (x.den:ℤ)+4 at nh
  have cmp:logHeight₁ (beta x)≤2^810*T^24:=by linarith only [A1,A2,pr,ff,den,nh,one_le_pow₀ t (n:=24)]
  have eq:oddProduct (beta x).num (beta x).den=primeProduct (scalarPrimes x):=by
    simp only [oddProduct,oddSupport,scalar_support_exact]
  exact cmp.trans (eq ▸ original_margin (beta x).num (beta x).den)

theorem unit_numerator (pell:PublishedPell312) (regulator:Regulator35) (disc:ConductorDiscriminants)
    (x:ℚ) (unit:x.num.natAbs=1) :
    logHeight₁ (beta x)≤glazerConstant24*(primeProduct (scalarPrimes x):ℝ)^24 := by
  have xn:x≠0:=by intro z;subst x;norm_num at unit
  apply of_small_numerator pell regulator disc x xn
  simp only [small,numberLog,unit,Nat.cast_one,Real.log_one,mul_zero]
  positivity
end
end Sun28.ScalarPencil
#print axioms Sun28.ScalarPencil.totalRadical_eq
#print axioms Sun28.ScalarPencil.of_small_numerator
#print axioms Sun28.ScalarPencil.unit_numerator
