import RankConicLines
import OcticExclusion

namespace Sun28.ConicRemaining
open Sun28.OcticResidues
open private signed_factor both from OcticExclusion
set_option maxHeartbeats 400000
set_option maxRecDepth 5000

private theorem bz00 (u v:ℤ) : 7378273*u^3=((481866:ℤ)*u+(679336:ℤ)*v)*f₁ 0 u v+((4977805:ℤ)*u+(244124244:ℤ)*v)*g₁ 0 u v := by
  change 7378273*u^3=((481866:ℤ)*u+(679336:ℤ)*v)*((-57)*u^2-2*(1733)*u*v+((2)*(-57)+735*7)*v^2)+((4977805:ℤ)*u+(244124244:ℤ)*v)*(7*(u^2-2*v^2))
  ring

private theorem bz01 (u v:ℤ) : 7378273*v^3=((169834:ℤ)*u+(240933:ℤ)*v)*f₁ 0 u v+((1382934:ℤ)*u+(86053975:ℤ)*v)*g₁ 0 u v := by
  change 7378273*v^3=((169834:ℤ)*u+(240933:ℤ)*v)*((-57)*u^2-2*(1733)*u*v+((2)*(-57)+735*7)*v^2)+((1382934:ℤ)*u+(86053975:ℤ)*v)*(7*(u^2-2*v^2))
  ring

private theorem bz10 (u v:ℤ) : 3073*u^3=((9163:ℤ)*u+(71148:ℤ)*v)*f₁ 1 u v+((39725:ℤ)*u+(394548:ℤ)*v)*g₁ 1 u v := by
  change 3073*u^3=((9163:ℤ)*u+(71148:ℤ)*v)*((-4)*u^2-2*(6)*u*v+((77)*(-4)+735*1)*v^2)+((39725:ℤ)*u+(394548:ℤ)*v)*(1*(u^2-77*v^2))
  ring

private theorem bz11 (u v:ℤ) : 3073*v^3=((12:ℤ)*u+(119:ℤ)*v)*f₁ 1 u v+((48:ℤ)*u+(620:ℤ)*v)*g₁ 1 u v := by
  change 3073*v^3=((12:ℤ)*u+(119:ℤ)*v)*((-4)*u^2-2*(6)*u*v+((77)*(-4)+735*1)*v^2)+((48:ℤ)*u+(620:ℤ)*v)*(1*(u^2-77*v^2))
  ring

private theorem bz20 (u v:ℤ) : 248913*u^3=((-358974:ℤ)*u+(3415104:ℤ)*v)*f₁ 2 u v+((-874293:ℤ)*u+(7192416:ℤ)*v)*g₁ 2 u v := by
  change 248913*u^3=((-358974:ℤ)*u+(3415104:ℤ)*v)*((-8)*u^2-2*(8)*u*v+((154)*(-8)+735*3)*v^2)+((-874293:ℤ)*u+(7192416:ℤ)*v)*(3*(u^2-154*v^2))
  ring

private theorem bz21 (u v:ℤ) : 248913*v^3=((144:ℤ)*u+(-2331:ℤ)*v)*f₁ 2 u v+((384:ℤ)*u+(-5448:ℤ)*v)*g₁ 2 u v := by
  change 248913*v^3=((144:ℤ)*u+(-2331:ℤ)*v)*((-8)*u^2-2*(8)*u*v+((154)*(-8)+735*3)*v^2)+((384:ℤ)*u+(-5448:ℤ)*v)*(3*(u^2-154*v^2))
  ring

private theorem share (j:Fin 3) {u v:ℤ} {p:ℕ} (pp:p.Prime) (cop:u.natAbs.Coprime v.natAbs)
    (hf:(p:ℤ)∣f₁ j u v) (hg:(p:ℤ)∣g₁ j u v) : p∣support₁ j := by
  let R:Fin 3→ℤ:=![7378273,3073,248913]
  have hr:(R j).natAbs∣(support₁ j)^5 := by
    fin_cases j
    · change 7378273∣(3073:ℕ)^5
      exact ⟨37141383841, by norm_num⟩
    · change 3073∣(3073:ℕ)^5
      exact ⟨89176462602241, by norm_num⟩
    · change 248913∣(9219:ℕ)^5
      exact ⟨267529387806723, by norm_num⟩
  have hu:(p:ℤ)∣R j*u^3:=by
    fin_cases j
    · change (p:ℤ)∣7378273*u^3
      rw[bz00];exact dvd_add (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)
    · change (p:ℤ)∣3073*u^3
      rw[bz10];exact dvd_add (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)
    · change (p:ℤ)∣248913*u^3
      rw[bz20];exact dvd_add (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)
  have hv:(p:ℤ)∣R j*v^3:=by
    fin_cases j
    · change (p:ℤ)∣7378273*v^3
      rw[bz01];exact dvd_add (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)
    · change (p:ℤ)∣3073*v^3
      rw[bz11];exact dvd_add (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)
    · change (p:ℤ)∣248913*v^3
      rw[bz21];exact dvd_add (dvd_mul_of_dvd_right hf _) (dvd_mul_of_dvd_right hg _)
  let prime:=Nat.prime_iff_prime_int.mp pp
  by_contra bad
  have pr:¬(p:ℤ)∣R j := fun h=>bad (pp.dvd_of_dvd_pow ((show p∣(R j).natAbs by simpa using Int.natAbs_dvd_natAbs.mpr h).trans hr))
  exact both cop pp (prime.dvd_of_dvd_pow ((prime.dvd_mul.mp hu).resolve_left pr))
    (prime.dvd_of_dvd_pow ((prime.dvd_mul.mp hv).resolve_left pr))

theorem common_class (j:Fin 3) {u v:ℤ} (cop:u.natAbs.Coprime v.natAbs) (fn:f₁ j u v≠0)
    (joint:IsSquare (f₁ j u v*g₁ j u v)) :
    ∃m U V:ℤ,m.natAbs∣support₁ j ∧ m*f₁ j u v=U^2 ∧ m*g₁ j u v=V^2 := by
  obtain ⟨Y,hy⟩:=joint
  have eq:f₁ j u v*g₁ j u v=Y^2:=by simpa only [pow_two] using hy
  have seven:7∣support₁ j:=by fin_cases j <;> decide
  have nz:support₁ j≠0:=by fin_cases j <;> decide
  obtain ⟨m,h,hm,fh⟩:=signed_factor fn nz seven (show f₁ j u v*(7*g₁ j u v)=7*Y^2 by linear_combination 7*eq) (by
    intro p pp hf hg
    rcases (Nat.prime_iff_prime_int.mp pp).dvd_mul.mp hg with se|oth
    · exact (show p∣7 by exact_mod_cast se).trans seven
    · exact share j pp cop hf oth)
  have hn:h≠0:=fun hz=>fn (by rw[fh,hz];ring)
  have sq:IsSquare (((m*g₁ j u v:ℤ):ℚ)):=by
    refine ⟨(Y:ℚ)/h,?_⟩
    have eq':(m:ℚ)*(h:ℚ)^2*(g₁ j u v:ℚ)=(Y:ℚ)^2:=by exact_mod_cast (show m*h^2*g₁ j u v=Y^2 by rw[←fh,eq])
    push_cast;field_simp[show (h:ℚ)≠0 by exact_mod_cast hn];linear_combination eq'
  obtain ⟨V,ev⟩:=Rat.isSquare_intCast_iff.mp sq
  exact ⟨m,m*h,V,hm,by rw[fh];ring,by simpa only [pow_two] using ev⟩

end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.common_class
