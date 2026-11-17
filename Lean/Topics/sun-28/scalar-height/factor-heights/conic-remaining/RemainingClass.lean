import RemainingKernels

namespace Sun28.ConicRemaining
open Sun28.OcticResidues Sun28.FactorHeights
noncomputable section
set_option maxHeartbeats 800000
set_option maxRecDepth 5500

/-- The rational point group of this explicit curve has order two in the independent
full 2-descent computation. This header only uses its absence of positive abscissas. -/
def ShortCurveBound : Prop := ∀X Y:ℚ, 0<X → Y^2=X*(X^2+735*X+134288) → False

private theorem sqrt_integral {A:ℤ} {w:ℚ} (hw:(A:ℚ)=w^2) : ∃z:ℤ,A=z^2 := by
  obtain ⟨k,e⟩:=Rat.isSquare_intCast_iff.mp (show IsSquare ((A:ℤ):ℚ) from ⟨w,by rw[hw,pow_two]⟩)
  exact ⟨k,by simpa only [pow_two] using e⟩

/-- The squarefree kernel of T²+7194 is 3 at every admissible rational parameter. -/
theorem separated_roots {T L J:ℚ} (e:q (T^2) 1=L^2)
    (w:q' (T^2) 1=J^2) : ∃h:ℚ, 2*n (T^2) 1=h^2 := by
  let a:=T.num
  let b:ℤ:=T.den
  have db:(b:ℚ)≠0:=by dsimp[b];exact_mod_cast T.den_nz
  have ar:(a:ℚ)=T*b:=by dsimp[a,b];exact (div_eq_iff (by exact_mod_cast T.den_nz)).mp T.num_div_den
  have qr:((q (a^2) (b^2):ℤ):ℚ)=(L*b^2)^2 := by
    dsimp [q] at *;push_cast;rw[ar];linear_combination (b:ℚ)^4*e
  have qs:((q' (a^2) (b^2):ℤ):ℚ)=(J*b^2)^2 := by
    dsimp [q',n,c] at *;push_cast;rw[ar];linear_combination (b:ℚ)^4*w
  obtain ⟨U,eu⟩:=sqrt_integral qr
  obtain ⟨V,ev⟩:=sqrt_integral qs
  obtain ⟨k,ek⟩:=unique_kernel (a:=a) (b:=b) (by simpa [a,b] using T.reduced)
    (by dsimp[b];exact_mod_cast T.den_nz) eu ev
  have kc:(((k:ℚ)/b)^2)*3=c (T^2) 1:=by
    have zz:=congrArg (Int.castRingHom ℚ) ek
    simp [c] at zz ⊢;rw[ar] at zz;field_simp [db];linear_combination -zz
  have kp:0<c (T^2) 1:=by dsimp[c];positivity
  let v:ℚ:=(k:ℚ)/b
  have vn:v≠0:=fun hz=>by change v^2*3=_ at kc;rw[hz] at kc;norm_num at kc;linarith only [kc,kp]
  refine ⟨J/(3*v),?_⟩
  change v^2*3=_ at kc
  change 6*n (T^2) 1*c (T^2) 1=J^2 at w
  rw[←kc] at w
  field_simp [vn];linear_combination w

/-- Every point in the −42 class forces a strictly positive rational abscissa on E. -/
theorem forces_short {s r z:ℚ} (rng:4<s) (rs:s=r^2) (az:7*(s-4)=z^2)
    (sel:imaginaryClass (-42) s) : ∃X Y:ℚ,0<X ∧ Y^2=X*(X^2+735*X+134288) := by
  obtain ⟨u,v,re,im⟩:=sel
  have un:u≠0:=fun hz=>by rw[hz] at im;norm_num at im
  have ev:v=1/(28812*u):=by apply (eq_div_iff (mul_ne_zero (by norm_num) un)).mpr;linarith only [im]
  have ee:s*u^2=(-42)*u^4+(349/686)*u^2+(-7194)/(4*343^2*(-42)):=by
    rw[ev] at re;field_simp [un] at re
    linear_combination re/(686*28812^2)
  let T:=294*u
  let L:=86436*u*r
  let J:=12348*u*z
  have tn:T≠0:=by dsimp[T];exact mul_ne_zero (by norm_num) un
  have ql:q (T^2) 1=L^2:=by
    dsimp[q,T,L];linear_combination -(86436:ℚ)^2*ee+(86436:ℚ)^2*u^2*rs
  have qj:q' (T^2) 1=J^2:=by
    dsimp[q',n,c,T,J];linear_combination -(12348:ℚ)^2*7*ee+(12348:ℚ)^2*u^2*az
  have delta:0<n (T^2) 1:=by
    have pp:0<c (T^2) 1:=by dsimp[c];positivity
    have zz:z≠0:=by intro ez;rw[ez] at az;linarith only [az,rng]
    have jn:J≠0:=by dsimp[J];exact mul_ne_zero (mul_ne_zero (by norm_num) un) zz
    have ps:=sq_pos_of_ne_zero jn
    change 6*n (T^2) 1*c (T^2) 1=J^2 at qj
    exact lt_of_not_ge (fun d=> ps.not_ge (qj ▸ mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (by norm_num) d) pp.le))
  obtain ⟨H,hh⟩:=separated_roots ql qj
  let K:ℚ:=9/T^2-1
  let X:ℚ:=2398*K/7
  let Y:ℚ:=2398*(H*L)/(98*T^3)
  have kn:0<K:=by dsimp[K];apply sub_pos.mpr;(apply (lt_div_iff₀ (sq_pos_of_ne_zero tn)).mpr);dsimp[n] at delta;linarith
  refine ⟨X,Y,by dsimp[X];positivity,?_⟩
  dsimp [X,Y,K];rw[div_pow,mul_pow,mul_pow,←hh,←ql]
  dsimp [n,q];field_simp [tn];ring

theorem negative42_excluded (h:ShortCurveBound) {s r z:ℚ} (rng:4<s) (rs:s=r^2) (az:7*(s-4)=z^2) :
    ¬imaginaryClass (-42) s := by
  intro cl
  obtain ⟨X,Y,xp,eq⟩:=forces_short rng rs az cl
  exact h X Y xp eq

end
end Sun28.ConicRemaining
#print axioms Sun28.ConicRemaining.separated_roots
#print axioms Sun28.ConicRemaining.forces_short
#print axioms Sun28.ConicRemaining.negative42_excluded
