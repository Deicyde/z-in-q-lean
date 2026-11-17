import PellArithmetic

/-! A bound on a primitive rational slope when the height of one contact is small. -/
namespace Sun28.HeightFibres
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors
noncomputable section

theorem nonneg_numberLog {n : ℤ} (hn:n≠0) : 0≤numberLog n := by
  apply Real.log_nonneg
  exact_mod_cast (show 1≤n.natAbs from Int.natAbs_pos.mpr hn)

private theorem numberLog_le {n : ℤ} {T : ℝ} (hn : n≠0) (h:(n.natAbs:ℝ)≤T) :
    numberLog n ≤ Real.log T :=
  Real.log_le_log (by exact_mod_cast Int.natAbs_pos.mpr hn) h

theorem pell_integer_height (pell : PublishedPell312) (regulator : RegulatorBound)
    (disc : BiquadraticDiscriminants)
    {g h k a b c I J : ℤ} {T Z : ℝ} (one : 1≤T) (zp : 0≤Z)
    (ng : g≠0) (nh : h≠0) (nk : k≠0)
    (gT : (g.natAbs:ℝ)≤T) (hT : (h.natAbs:ℝ)≤T) (kT : (k.natAbs:ℝ)≤T)
    (i : I≠0) (j : J≠0) (ij : I≠J) (iZ : numberLog I≤Z) (jZ : numberLog J≤Z)
    (first : g*a^2-h*b^2=I) (second : g*a^2-k*c^2=J) :
    numberLog a≤2^185*T^19+2^165*T^10*Z := by
  obtain ⟨L,finite,dim,sr,sw,d⟩:=pell_field ng nh nk disc
  let _ : FiniteDimensional ℚ L:=finite
  let D : ℝ:=(NumberField.discr L).natAbs
  have dp : 1≤D := by dsimp only [D];exact_mod_cast (show 1≤(NumberField.discr L).natAbs from Int.natAbs_pos.mpr (NumberField.discr_ne_zero L))
  have product : (g.natAbs:ℝ)*h.natAbs*k.natAbs≤T*T*T :=
    mul_le_mul (mul_le_mul gT hT (by positivity) (by linarith)) kT (by positivity) (by positivity)
  have cap : D≤64*T^6 := calc
    D ≤ 64*(((g.natAbs:ℝ)*h.natAbs*k.natAbs)^2) := by dsimp only [D];exact_mod_cast d
    _ ≤ 64*((T*T*T)^2) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) product 2) (by norm_num)
    _ = _ := by ring
  have reg:=regulator_estimate one dp cap (regulator L dim)
  have result:=pell L dim g h k a b c I J ng nh nk i j ij sr sw first second _ _
    (numberLog_le ng gT) (numberLog_le nh hT) (numberLog_le nk kT) iZ jZ
  exact pell_numeric one (NumberField.Units.regulator_pos L) reg zp result

theorem pair_as_max {A B : ℤ} (na:A≠0) (nb:B≠0) :
    pairLogHeight A B=max (numberLog A) (numberLog B) := by
  have a0:(0:ℝ)<A.natAbs := by exact_mod_cast Int.natAbs_pos.mpr na
  have b0:(0:ℝ)<B.natAbs := by exact_mod_cast Int.natAbs_pos.mpr nb
  have form : ((max |A| |B|:ℤ):ℝ)=max (A.natAbs:ℝ) (B.natAbs:ℝ) := by
    rw [←Int.natCast_natAbs,←Int.natCast_natAbs]
    norm_cast
  change Real.log ((max |A| |B|:ℤ):ℝ)=max (Real.log (A.natAbs:ℝ)) (Real.log (B.natAbs:ℝ))
  rw [form]
  rcases le_total (A.natAbs:ℝ) (B.natAbs:ℝ) with le|le
  · rw [max_eq_right le,max_eq_right (Real.log_le_log a0 le)]
  · rw [max_eq_left le,max_eq_left (Real.log_le_log b0 le)]

theorem log_mul_int {a b : ℤ} (na:a≠0) (nb:b≠0) :
    numberLog (a*b)=numberLog a+numberLog b := by
  rw [numberLog,Int.natAbs_mul,Nat.cast_mul,Real.log_mul (by exact_mod_cast (Int.natAbs_ne_zero.mpr na))
    (by exact_mod_cast (Int.natAbs_ne_zero.mpr nb))]
  rfl

/-- The denominator enters the height bound only through its real logarithm,
irrespective of its prime divisors and the even orders of the three other rows. -/
theorem denominator_height (pell : PublishedPell312) (regulator : RegulatorBound)
    (disc : BiquadraticDiscriminants) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    let T:ℝ:=heightRadical A B
    pairLogHeight A B≤2^190*T^19+2^170*T^10*(numberLog B+12) := by
  obtain ⟨g,h,k,a,b,c,ng,nh,nk,na,_,_,gh,hh,kh,eq,first,second⟩:=simultaneous_rows off
  let T : ℝ:=heightRadical A B
  have one : 1≤T := by
    exact Nat.one_le_cast.mpr (show 1≤heightRadical A B from Nat.mul_pos pos_cutoff (pos_odd A B))
  have nb : B≠0 := off 0
  have np : A≠0 := off 1
  have lg:=nonneg_numberLog nb
  have lconst : numberLog 2401≤12 := by
    have cap : numberLog 2401≤Real.log (2^12) := Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at cap
    norm_num at cap
    linarith only [cap,Real.log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have right : numberLog (2401*B)≤numberLog B+12 := by
    rw [log_mul_int (by decide : (2401:ℤ)≠0) nb]
    linarith only [lconst]
  have bounds : numberLog a≤2^185*T^19+2^165*T^10*(numberLog B+12) :=
    pell_integer_height pell regulator disc one (by linarith) ng nh nk
      (Nat.cast_le.mpr gh) (Nat.cast_le.mpr hh) (Nat.cast_le.mpr kh) nb
      (mul_ne_zero (by decide) nb) (by omega) (by linarith) right first second
  have ga : numberLog A=numberLog g+2*numberLog a := by
    rw [eq,pow_two,log_mul_int ng (mul_ne_zero na na),log_mul_int na na];ring
  have gcap : numberLog g≤Real.log T := numberLog_le ng (Nat.cast_le.mpr gh)
  have t19 : T≤T^19 := by simpa using pow_le_pow_right₀ one (by decide : 1≤19)
  have t10 : 1≤T^10 := one_le_pow₀ one
  have t0 : 0≤T:=by linarith
  have t19p : 0≤T^19:=by positivity
  have mult : numberLog B+12≤T^10*(numberLog B+12) := by
    simpa using mul_le_mul_of_nonneg_right t10 (show 0≤numberLog B+12 by linarith)
  have p : 0≤T^10*(numberLog B+12) := mul_nonneg (pow_nonneg t0 _) (by linarith)
  rw [pair_as_max np nb]
  apply max_le
  · linarith only [bounds,ga,gcap,Real.log_le_sub_one_of_pos (by linarith : 0<T),t19,t19p,p]
  · linarith only [mult,p,t19p]

end
end Sun28.HeightFibres
#print axioms Sun28.HeightFibres.pell_integer_height
#print axioms Sun28.HeightFibres.denominator_height
