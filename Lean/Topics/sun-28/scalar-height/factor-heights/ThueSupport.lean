import FiniteCharts

namespace Sun28.FactorHeights
open Sun28.WitnessHeight ZInQ.RouteK
noncomputable section

/-- The non-Weierstrass point 17/6 belongs to the negative surviving system. -/
theorem nonempty_negative : conics (17/6) 14 (-35) 7 ∧ scalarClass (17/6)= -910 := by
  constructor
  · exact ⟨7/6,35/6,70/6,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num,by norm_num⟩
  · have sf10 : Squarefree (10:ℕ) := (Nat.squarefree_mul (by decide : Nat.Coprime 2 5)).mpr
      ⟨(by decide : Nat.Prime 2).squarefree,(by decide : Nat.Prime 5).squarefree⟩
    have sf91 : Squarefree (91:ℕ) := (Nat.squarefree_mul (by decide : Nat.Coprime 7 13)).mpr
      ⟨(by decide : Nat.Prime 7).squarefree,(by decide : Nat.Prime 13).squarefree⟩
    have sf : Squarefree (910:ℕ) := (Nat.squarefree_mul (by decide : Nat.Coprime 10 91)).mpr ⟨sf10,sf91⟩
    exact sqf_eq_of_eq_mul_sq (Int.squarefree_natAbs.mp (by exact sf : Squarefree (Int.natAbs (-910))))
      (by norm_num : (600250/1296:ℚ)≠0) (by norm_num [octic] : octic (17/6)=(-910:ℤ)*(600250/1296:ℚ)^2)

/-- No prescribed integer N can absorb all prime divisors of the second
binary row outside the signed scalar squareclass. -/
theorem unmeasured_prime (N:ℕ) :
    ∃x:ℚ, ∃p:ℕ, p.Prime ∧ ¬p∣N+1 ∧ ¬p∣210 ∧ (p:ℤ)^2∣value 1 x ∧ ¬p∣(scalarClass x).natAbs := by
  let s:=210*(N+1)
  let t:=2*s
  let a:ℤ:=(t:ℤ)^2-1
  let b:ℤ:=2*(t:ℤ)
  let x:ℚ:=(a:ℚ)/(b:ℚ)
  have hp0:0<b:=by dsimp [b,t,s];positivity
  have bn:(b:ℚ)≠0:=by exact_mod_cast hp0.ne'
  have cop:IsCoprime a b:=⟨-1,s,by dsimp [a,b,t];ring⟩
  have xc:x.num=a:=Rat.num_div_eq_of_coprime hp0 (Int.isCoprime_iff_nat_coprime.mp cop)
  have xd:(x.den:ℤ)=b:=Rat.den_div_eq_of_coprime hp0 (Int.isCoprime_iff_nat_coprime.mp cop)
  let p:=(t^2+1).minFac
  have tpos : 0<t^2 := by dsimp [t,s]; positivity
  have pp:p.Prime:=Nat.minFac_prime (by omega : t^2+1≠1)
  have pv:p∣t^2+1:=Nat.minFac_dvd _
  have pt:¬p∣t:=by
    intro h
    exact pp.not_dvd_one (by have d:=Nat.dvd_sub pv (dvd_pow h (by decide : 2≠0));simpa using d)
  have ps:¬p∣210:=fun h=>pt (h.trans (by dsimp [t,s];exact ⟨2*(N+1),by ring⟩))
  have ps':¬p∣N+1:=fun h=>pt (h.trans (by dsimp [t,s];exact ⟨420,by ring⟩))
  have B:value 1 x=((t^2+1:ℕ):ℤ)^2:=by
    unfold value;rw [xc,xd];norm_num [row,alpha,gamma,a,b];ring
  have pv':(p:ℤ)∣((t^2+1:ℕ):ℤ):=by exact_mod_cast pv
  refine ⟨x,p,pp,ps',ps,by rw [B];exact pow_dvd_pow_of_dvd pv' _,?_⟩
  let H:=row 0 a b*row 2 a b*row 3 a b
  have hn:H≠0:=by
    have E (i:Fin 4):row i a b≠0:=by have z:=row_ne x i;simpa [value,xc,xd] using z
    exact mul_ne_zero (mul_ne_zero (E 0) (E 2)) (E 3)
  have re : octic x=(H:ℚ)*((((t^2+1:ℕ):ℚ)/(b:ℚ)^4)^2) := by
    dsimp [octic,x,H,row,alpha,gamma];push_cast;field_simp
    dsimp [a,b];push_cast;ring
  have klass:scalarClass x=sqfInt H:=by
    unfold scalarClass;rw [re,sqf_mul_sq (by exact_mod_cast hn) (by positivity),sqf_intCast]
  intro hit
  rw [klass] at hit
  obtain ⟨_,u,_,eu⟩:=sqfInt_spec hn
  have ph:(p:ℤ)∣H:=(Int.natAbs_dvd_natAbs.mp (by simpa using hit)).trans (show sqfInt H∣H from ⟨u^2,eu⟩)
  let _:Fact p.Prime:=⟨pp⟩
  have ht:(t:ZMod p)^2+1=0:=by simpa using (ZMod.natCast_eq_zero_iff ..).2 pv
  have ha:(a:ZMod p)= -2:=by dsimp [a];push_cast;linear_combination ht
  have hb:(b:ZMod p)^2= -4:=by dsimp [b];push_cast;linear_combination 4*ht
  have zh:(H:ZMod p)=0:=(ZMod.intCast_zmod_eq_zero_iff_dvd ..).2 ph
  dsimp [H,row,alpha,gamma] at zh
  push_cast at zh
  rw [ha,hb] at zh
  norm_num at zh
  have dv:p∣28800000 := (ZMod.natCast_eq_zero_iff ..).1 (by exact_mod_cast zh : (28800000:ZMod p)=0)
  exact ps (pp.dvd_of_dvd_pow (dv.trans (by decide : 28800000∣210^10)))

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.nonempty_negative
#print axioms Sun28.FactorHeights.unmeasured_prime
