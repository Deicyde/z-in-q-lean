import ConicCover

namespace Sun28.ConicCovers
open Sun28.FactorHeights
noncomputable section

/-- One bounded rational parameter for the positive conic system. -/
theorem positive_parameter {x:ℚ} (hc:conics x 2 1 1) :
    ∃r:ℚ, 4<r^2 ∧ ratSquare (7*(r^2-4)) ∧ ratSquare (16*r^2-15) ∧
      ratSquare (7*(1372*r^4-1396*r^2+439)) ∧
      let n:=15-2*r^2; let D:=1-2*r^2
      (3*n^2+2398*D^2)*(x^2+3/2)=2401*D^2*x^2 := by
  obtain ⟨t,ht,⟨z,eq⟩,⟨u,eu⟩,⟨v,ev⟩,⟨w,ew⟩,ex⟩:=positive_cross hc
  have tv:=abs_lt.mp ht
  have ne:1-t≠0 := by linarith
  let r:=z/(2*(1-t))
  have ident:2*(1-t)*r^2=15-t := by
    dsimp [r];field_simp;linear_combination -eq
  let n:=15-2*r^2
  let D:=1-2*r^2
  have idn:n=t*D :=by dsimp [n,D];linear_combination -ident
  have ge:r^2>4 := by
    by_contra! le
    have a:=mul_le_mul_of_nonneg_left le (show 0≤1-t by linarith [tv.2])
    nlinarith only [a,ident,tv.1]
  have rn:r≠0 := by intro er;rw [er] at ge;norm_num at ge
  have eu':2*(D^2-n^2)=(u*D)^2 := by rw [idn];linear_combination D^2*eu
  have ev':14*(225*D^2-n^2)=(v*D)^2 :=by rw [idn];linear_combination D^2*ev
  have ew':3*n^2+2398*D^2=(w*D)^2 :=by rw [idn];linear_combination D^2*ew
  refine ⟨r,ge,⟨u*D/4,?_⟩,⟨v*D/(28*r),?_⟩,⟨w*D,?_⟩,?_⟩
  · dsimp [n,D] at eu' ⊢;linear_combination eu'/16
  · dsimp [n,D] at ev' ⊢;field_simp;linear_combination ev'
  · dsimp [n,D] at ew' ⊢;linear_combination ew'
  · change (3*n^2+2398*D^2)*(x^2+3/2)=2401*D^2*x^2
    have pp:x^2+3/2≠0:=by positivity
    have e: (3*t^2+2398)*(x^2+3/2)=2401*x^2 :=by field_simp at ex ⊢;linear_combination ex
    rw [idn];linear_combination D^2*e

/-- One rational parameter for the second conic system and its original abscissa. -/
theorem negative_parameter {x:ℚ} (hc:conics x 14 (-35) 7) :
    ∃r:ℚ, r≠0 ∧ ratSquare (7*(5*r^2+8)) ∧ ratSquare (35*(8*r^2+3)) ∧
      343*(15+5*r^2)^2-439*(1+5*r^2)^2=(8*x*(1+5*r^2))^2 := by
  obtain ⟨t,lt,gt,⟨z,eq⟩,⟨u,eu⟩,⟨v,ev⟩,ex⟩:=negative_cross hc
  have ne:t-1≠0:=by linarith
  let r:=z/(5*(t-1))
  have ident:5*(t-1)*r^2=15-t:=by dsimp [r];field_simp;linear_combination -eq
  have rn:r≠0:=by intro zz;rw [zz] at ident;nlinarith
  let n:=15+5*r^2
  let D:=1+5*r^2
  have idn:n=t*D:=by dsimp [n,D];linear_combination -ident
  have eu':n^2-D^2=(u*D)^2 :=by rw [idn];linear_combination D^2*eu
  have ev':5*(225*D^2-n^2)=(v*D)^2 :=by rw [idn];linear_combination D^2*ev
  refine ⟨r,rn,⟨u*D/2,?_⟩,⟨v*D/(10*r),?_⟩,?_⟩
  · dsimp [n,D] at eu' ⊢;linear_combination eu'/4
  · dsimp [n,D] at ev' ⊢;field_simp;linear_combination ev'
  · change 343*n^2-439*D^2=(8*x*D)^2
    rw [idn];linear_combination D^2*ex

end
end Sun28.ConicCovers
#print axioms Sun28.ConicCovers.positive_parameter
#print axioms Sun28.ConicCovers.negative_parameter
