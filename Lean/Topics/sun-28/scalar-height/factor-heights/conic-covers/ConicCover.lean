import ConicCells

namespace Sun28.ConicCovers
open Sun28.FactorHeights
noncomputable section

private def f {R:Type*} [CommRing R] (s:Bool) (a b:R) := if s then 2*(b^2-a^2) else a^2-b^2
private def g {R:Type*} [CommRing R] (s:Bool) (a b:R) := (if s then 14 else 5)*(225*b^2-a^2)
private def h {R:Type*} [CommRing R] (s:Bool) (a b:R) := if s then 3*a^2+2398*b^2 else 343*a^2-439*b^2
private def c (s:Bool) : ℤ := if s then 7 else 5

private theorem square_int {v:ℤ} {w:ℚ} (H:(v:ℚ)=w^2) : ∃a:ℤ,v=a^2 := by
  apply scaled_square (Y:=w) (B:=1)
  simpa using H

/-- Positive or negative chart membership ascends to its unique pair of linear blocks. -/
theorem cross_class (s:Bool) (t:ℚ) (pos:0<block s t 1) (first:ratSquare (f s t 1))
    (second:ratSquare (g s t 1)) (last:ratSquare (h s t 1)) :
    ∃d:ℕ, (if s then d=2 ∨ d=14 else d=5) ∧ ratSquare ((d:ℚ)*block s t 1) := by
  let a:=t.num
  let b:ℤ:=t.den
  have bn:(b:ℚ)≠0:=by dsimp [b];exact_mod_cast t.den_nz
  have ta:(a:ℚ)=t*b:= (div_eq_iff bn).mp t.num_div_den
  have B:((block s a b:ℤ):ℚ)=block s t 1*(b:ℚ)^2 := by
    cases s <;> simp only [block,left,Bool.false_eq_true,ite_false,ite_true,Int.cast_mul,
      Int.cast_sub,Int.cast_ofNat,ta] <;> ring
  have ep:0<block s a b:=by
    exact_mod_cast (show 0<((block s a b:ℤ):ℚ) from by rw [B];exact mul_pos pos (sq_pos_of_ne_zero bn))
  obtain ⟨u,eu⟩:=first
  obtain ⟨v,ev⟩:=second
  obtain ⟨w,ew⟩:=last
  have ff:((f s a b:ℤ):ℚ)=(u*b)^2 := by
    cases s <;> simp only [f,Bool.false_eq_true,ite_false,ite_true,one_pow] at eu ⊢ <;>
      push_cast <;> rw [ta] <;> linear_combination (b:ℚ)^2*eu
  have gg:((g s a b:ℤ):ℚ)=(v*b)^2 := by
    cases s <;> simp only [g,Bool.false_eq_true,ite_false,ite_true,one_pow] at ev ⊢ <;>
      push_cast <;> rw [ta] <;> linear_combination (b:ℚ)^2*ev
  have hh:((h s a b:ℤ):ℚ)=(w*b)^2 := by
    cases s <;> simp only [h,Bool.false_eq_true,ite_false,ite_true,one_pow] at ew ⊢ <;>
      push_cast <;> rw [ta] <;> linear_combination (b:ℚ)^2*ew
  obtain ⟨U,EU⟩:=square_int ff
  obtain ⟨V,EV⟩:=square_int gg
  obtain ⟨W,EW⟩:=square_int hh
  have total:∃Y:ℤ,block s a b*partner a b=c s*Y^2 := by
    have hU := congrArg (Int.castRingHom ℚ) EU
    have hV := congrArg (Int.castRingHom ℚ) EV
    let z : ℚ := (U:ℚ)*V / (if s then 14 else 5)
    have E:((block s a b*partner a b:ℤ):ℚ)=(c s:ℚ)*z^2 := by
      cases s
      · simp [z,c,block,partner,left,f,g] at hU hV ⊢
        linear_combination (225*(b:ℚ)^2-a^2)*hU + (U:ℚ)^2/5*hV
      · simp [z,c,block,partner,left,f,g] at hU hV ⊢
        linear_combination (225*(b:ℚ)^2-a^2)/2*hU + (U:ℚ)^2/28*hV
    by_cases zz:z=0
    · refine ⟨0,?_⟩
      exact_mod_cast (show ((block s a b*partner a b:ℤ):ℚ)=(c s:ℚ)*(0:ℚ)^2 from zz ▸ E)
    · have cs:Squarefree (c s):=by
        cases s <;> apply Int.squarefree_natCast.mpr <;> exact (by decide : Nat.Prime _).squarefree
      have L:=ZInQ.RouteK.sqf_eq_of_eq_mul_sq cs zz E
      have nz:block s a b*partner a b≠0:=by
        intro ee
        rw [ee,Int.cast_zero] at E
        exact (mul_ne_zero (show (c s:ℚ)≠0 by cases s <;> norm_num [c]) (pow_ne_zero 2 zz)) E.symm
      obtain ⟨_,q,_,hq⟩:=ZInQ.RouteK.sqfInt_spec nz
      exact ⟨q,by rwa [←ZInQ.RouteK.sqf_intCast _,L] at hq⟩
  have ab:a.natAbs.Coprime b.natAbs:=by simpa [a,b] using t.reduced
  obtain ⟨Y,ey⟩:=total
  obtain ⟨d,dd,Z,eZ⟩:=block_support ab ep (c:=c s) (by cases s <;> decide) ey
  have Zn:Z≠0:=by intro z;rw [eZ,z] at ep;norm_num at ep
  have dn:0<d:=Nat.pos_of_dvd_of_pos dd (by decide)
  have Bn:block s a b≠0:=ep.ne'
  have blockR:((block s a b:ℤ):ℚ)=(d:ℚ)*(Z:ℚ)^2:=by exact_mod_cast eZ
  have r₂:∃y:ℤ,row s (d:ℤ) a b 2=y^2 := by
    apply square_int (w:=(U:ℚ)*(15*(b:ℚ)-a)/Z)
    have zn:(Z:ℚ)≠0:=by exact_mod_cast Zn
    have FF:=congrArg (Int.castRingHom ℚ) EU
    cases s
    · simp [row,block,left,f] at blockR FF ⊢;field_simp
      linear_combination (15*(b:ℚ)-a)^2*FF - (15*(b:ℚ)-a)*((b:ℚ)+a)*blockR
    · simp [row,block,left,f] at blockR FF ⊢;field_simp
      linear_combination (15*(b:ℚ)-a)^2*FF - 2*(15*(b:ℚ)-a)*((b:ℚ)+a)*blockR
  have r₃:∃y:ℤ,row s (d:ℤ) a b 3=y^2 := by
    apply square_int (w:=(V:ℚ)*(left s a b:ℤ)/Z)
    have zn:(Z:ℚ)≠0:=by exact_mod_cast Zn
    have GG:=congrArg (Int.castRingHom ℚ) EV
    cases s
    · simp [row,block,complementary,left,g] at blockR GG ⊢;field_simp
      linear_combination ((a:ℚ)-b)^2*GG - 5*((a:ℚ)-b)*(15*(b:ℚ)+a)*blockR
    · simp [row,block,complementary,left,g] at blockR GG ⊢;field_simp
      linear_combination ((b:ℚ)-a)^2*GG - 14*((b:ℚ)-a)*(15*(b:ℚ)+a)*blockR
  have allR:integral s d a b := by
    intro i;fin_cases i
    · exact ⟨U,by cases s <;> simpa [row,f] using EU⟩
    · exact ⟨W,by cases s <;> simpa [row,h] using EW⟩
    · exact r₂
    · exact r₃
  refine ⟨d,surviving ab dd allR,⟨(d:ℚ)*Z/b,?_⟩⟩
  field_simp
  exact B.symm.trans blockR

/-- Up to the free sign on the original v ordinate the positive class is 2. -/
theorem positive_cross {x:ℚ} (hc:conics x 2 1 1) :
    ∃t:ℚ, |t|<1 ∧ ratSquare (2*(1-t)*(15-t)) ∧
      ratSquare (2*(1-t^2)) ∧ ratSquare (14*(225-t^2)) ∧
      ratSquare (3*t^2+2398) ∧ 3*t^2+2398=2401*(x^2/(x^2+3/2)) := by
  obtain ⟨t,bound,F,G,H,idn⟩:=positive_lines hc
  have lt:t<1:=lt_of_le_of_lt (le_abs_self _) bound
  have bs:0<block true t 1 := by
    simp [block,left];exact mul_pos (by linarith) (by linarith)
  obtain ⟨d,alive,z,eq⟩:=cross_class true t bs (by simpa [f] using F) (by simpa [g] using G) (by simpa [h] using H)
  change d=2 ∨ d=14 at alive
  rcases alive with rfl|rfl
  · exact ⟨t,bound,⟨z,by simpa [block,left,mul_assoc] using eq⟩,F,G,H,idn⟩
  · obtain ⟨u,eu⟩:=F
    obtain ⟨v,ev⟩:=G
    simp [block,left] at eq
    have zn:z≠0:=by intro e;rw [e] at eq;simp [block,left] at bs;nlinarith only [bs,eq]
    have opposite:2*(1-(-t))*(15-(-t))=(u*v/z)^2 := by
      field_simp
      linear_combination (14*(225-t^2))*eu+u^2*ev-2*(1+t)*(15+t)*eq
    exact ⟨-t,by simpa using bound,⟨_,opposite⟩,by simpa using (show ratSquare (2*(1-t^2)) from ⟨u,eu⟩),by simpa using (show ratSquare (14*(225-t^2)) from ⟨v,ev⟩),
      by simpa using H,by simpa using idn⟩

/-- The negative conic system forces the single cross-squareclass 5. -/
theorem negative_cross {x:ℚ} (hc:conics x 14 (-35) 7) :
    ∃t:ℚ, 1<t ∧ t<15 ∧ ratSquare (5*(t-1)*(15-t)) ∧
      ratSquare (t^2-1) ∧ ratSquare (5*(225-t^2)) ∧ 343*t^2-439=(8*x)^2 := by
  obtain ⟨t,lb,ub,F,G,idn⟩:=negative_lines hc
  have bs:0<block false t 1 := by
    simp [block,left];exact mul_pos (by linarith) (by linarith)
  obtain ⟨d,alive,Y,eq⟩:=cross_class false t bs (by simpa [f] using F) (by simpa [g] using G) ⟨8*x,by simpa [h] using idn⟩
  change d=5 at alive
  subst d
  exact ⟨t,lb,ub,⟨Y,by simpa [block,left,mul_assoc] using eq⟩,F,G,idn⟩

end
end Sun28.ConicCovers
#print axioms Sun28.ConicCovers.cross_class
#print axioms Sun28.ConicCovers.positive_cross
#print axioms Sun28.ConicCovers.negative_cross
