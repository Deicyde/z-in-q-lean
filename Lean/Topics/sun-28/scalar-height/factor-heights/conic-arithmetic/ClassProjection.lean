import OcticExclusion

namespace Sun28.OcticResidues
noncomputable section

/-- Coefficients in Q(sqrt(-7194)) of s−(349+2 sqrt(-7194))/686
    being d times a nonzero square in that literal root field. -/
def imaginaryClass (d s:ℚ) : Prop :=
  ∃u v:ℚ,s-349/686=d*(u^2-7194*v^2) ∧ -(1/343:ℚ)=2*d*u*v

/-- Once the rational-root components are fixed, the entire -231 class is impossible. -/
theorem negative231_excluded {s r z:ℚ} (rng:4<s) (rs:s=r^2) (az:7*(s-4)=z^2) :
    ¬ imaginaryClass (-231) s := by
  rintro ⟨u,v,realpart,imagpart⟩
  have un:u≠0:=fun zero=>by rw[zero] at imagpart;norm_num at imagpart
  have ar:(u.num:ℚ)=u*u.den:=(div_eq_iff (by exact_mod_cast u.den_nz)).mp u.num_div_den
  let b:ℚ:=u.den
  have bn:b≠0:=by dsimp[b];exact_mod_cast u.den_nz
  have zn:z≠0:=fun e=>by rw[e] at az; nlinarith
  have rn:r≠0:=fun e=>by rw[e] at rs; nlinarith
  have vr:v=1/(158466*u):=by apply (eq_div_iff (mul_ne_zero (by norm_num) un)).mpr;linarith only [imagpart]
  have sv:s*u^2=(-231)*u^4+(349/686)*u^2+(-7194)/(4*343^2*(-231)) := by
    rw [vr] at realpart
    field_simp [un] at realpart
    linear_combination realpart/(686*25111473156)
  let F:=f (u.num^2) ((u.den:ℤ)^2)
  let G:=g (u.num^2) ((u.den:ℤ)^2)
  let H:=h (u.num^2) ((u.den:ℤ)^2)
  let V:=235298*b^4*u^2*r*z
  have eqQ : ((F*G*H:ℤ):ℚ)=7*V^2:=by
    have ident: f (u^2) 1*g (u^2) 1*h (u^2) 1=
        387556041628*(7*((-231)*u^4+(349/686)*u^2+(-7194)/(4*343^2*(-231)))*
          (((-231)*u^4+(349/686)*u^2+(-7194)/(4*343^2*(-231)))-4*u^2)):=by unfold f g h;ring
    have hom: ((F*G*H:ℤ):ℚ)=b^8*(f (u^2) 1*g (u^2) 1*h (u^2) 1):=by
      dsimp [F,G,H,b,f,g,h];push_cast;rw [ar];ring
    rw [hom,ident,←sv]
    dsimp [V];rw [mul_pow,mul_pow,mul_pow,←rs,←az];ring
  have eqZ:IsSquare (((7*(F*G*H):ℤ):ℚ)):=by
    refine ⟨7*V,?_⟩
    push_cast at eqQ ⊢
    linear_combination 7*eqQ
  obtain ⟨W,ew⟩:=Rat.isSquare_intCast_iff.mp eqZ
  have dvd7:(7:ℤ)∣W:=((Nat.prime_iff_prime_int.mp (by decide:Nat.Prime 7)).dvd_of_dvd_pow
    (n:=2) (by rw[pow_two,←ew];exact dvd_mul_right ..))
  obtain ⟨Y,hy⟩:=dvd7
  have eqn:F*G*H=7*Y^2:=by apply mul_left_cancel₀ (by decide:(7:ℤ)≠0);rw[hy] at ew;linear_combination ew
  have yn:Y≠0:=by
    intro zy
    have Vn:V≠0:=by dsimp [V];exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
      (pow_ne_zero 4 bn)) (pow_ne_zero 2 un)) rn) zn
    have eq0:F*G*H=0:=by rw[eqn,zy];ring
    have nzero:=mul_ne_zero (by norm_num : (7:ℚ)≠0) (pow_ne_zero 2 Vn)
    rw[eq0,Int.cast_zero] at eqQ
    exact nzero eqQ.symm
  exact no_octic (by simpa using u.reduced) (by exact_mod_cast u.den_nz) yn eqn

end
end Sun28.OcticResidues
#print axioms Sun28.OcticResidues.negative231_excluded
