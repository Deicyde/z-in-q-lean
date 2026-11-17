import ScalarOctic

namespace Sun28.ScalarQuotients
open Sun28.WitnessHeight Sun28.ScalarHeight
noncomputable section

/-- The quotient by changing the sign of the scalar coordinate. -/
def abscissa (x : ℚ) : ℚ := (2401-beta x)/(75*beta x)

def cubic (m X : ℚ) : ℚ := X*(X-32*m)*(X+3*m)

def elliptic (m : ℚ) : WeierstrassCurve ℚ := ⟨0,-29*m,0,-96*m^2,0⟩

theorem discriminant (m:ℚ) : (elliptic m).Δ = 16*32^2*3^2*35^2*m^6 := by
  simp [elliptic,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,
    WeierstrassCurve.b₆,WeierstrassCurve.b₈]
  ring

theorem quotient_identity (x : ℚ) :
    21*cubic 1 (abscissa x)=octic x*(686/(375*(beta x)^2))^2 := by
  have t:0<beta x:=by unfold beta; positivity
  unfold cubic abscissa octic
  field_simp
  unfold beta
  ring

def twistX (d x:ℚ) : ℚ := 21*d*abscissa x

def twistY (d x y:ℚ) : ℚ := 21*d^2*y*(686/(375*(beta x)^2))

theorem elliptic_point {x d y:ℚ} (h:octic x=d*y^2) :
    (twistY d x y)^2=cubic (21*d) (twistX d x) := by
  have q:=quotient_identity x
  rw [h] at q
  unfold twistY twistX cubic at *
  linear_combination -441*d^3*q

theorem elliptic_strict {x d y:ℚ} (dn:d≠0) (yn:y≠0) (h:octic x=d*y^2) :
    twistY d x y≠0 ∧ twistX d x≠0 ∧ twistX d x≠32*(21*d) ∧ twistX d x≠ -3*(21*d) := by
  have t:0<beta x:=by unfold beta;positivity
  have nz:twistY d x y≠0:=by unfold twistY; positivity [sq_pos_of_ne_zero dn, yn]
  have nc:cubic (21*d) (twistX d x)≠0:=by rw [←elliptic_point h];exact pow_ne_zero _ nz
  refine ⟨nz,?_,?_,?_⟩
  · rintro e; exact nc (by simp [cubic,e])
  · rintro e; exact nc (by simp [cubic,e])
  · rintro e; exact nc (by simp [cubic,e])

/-- This condition tests whether an elliptic quotient point lifts to the octic. -/
def liftCoordinate (w : ℚ) : ℚ := (2398-225*w)/(2*(75*w+1))

theorem coordinate_inverse (x:ℚ) : 75*abscissa x+1≠0 ∧ liftCoordinate (abscissa x)=x^2 := by
  have t:0<beta x:=by unfold beta;positivity
  have val:75*abscissa x+1=2401/beta x:=by unfold abscissa;field_simp;ring
  refine ⟨by rw [val];positivity,?_⟩
  unfold liftCoordinate
  rw [val]
  unfold abscissa
  field_simp
  unfold beta
  ring

theorem coordinate_of_lift {v x:ℚ} (h:75*v+1≠0) (s:x^2=liftCoordinate v) : abscissa x=v := by
  unfold liftCoordinate at s
  have e:= (eq_div_iff (mul_ne_zero (by norm_num) h)).mp s
  have pos:0<beta x:=by unfold beta;positivity
  unfold abscissa
  apply (div_eq_iff (mul_ne_zero (by norm_num) pos.ne')).mpr
  unfold beta
  linear_combination -e

/-- The nonzero rational points of the octic are exactly the elliptic points with one square constraint. -/
theorem lift_iff {d:ℚ} (dn:d≠0) :
    (∃ x y:ℚ,y≠0 ∧ octic x=d*y^2) ↔
      ∃ v Y:ℚ, Y≠0 ∧ Y^2=cubic (21*d) (21*d*v) ∧ 75*v+1≠0 ∧ IsSquare (liftCoordinate v) := by
  constructor
  · rintro ⟨x,y,yn,h⟩
    obtain ⟨unit,val⟩:=coordinate_inverse x
    exact ⟨abscissa x,twistY d x y,(elliptic_strict dn yn h).1,elliptic_point h,
      unit,x,by simp [val,pow_two]⟩
  · rintro ⟨v,Y,Yn,curve,den,x,hx⟩
    have eq:=coordinate_of_lift den (by simpa [pow_two] using hx.symm)
    let factor:=21*d^2*(686/(375*(beta x)^2))
    have t:0<beta x:=by unfold beta;positivity
    have fn:factor≠0:=by dsimp [factor];positivity [sq_pos_of_ne_zero dn]
    let y:=Y/factor
    have prod:y*factor=Y:=by dsimp [y];field_simp
    have q:=quotient_identity x
    rw [←eq] at curve
    change Y^2=cubic (21*d) (twistX d x) at curve
    have c:cubic (21*d) (twistX d x)=((21*d)^3)*cubic 1 (abscissa x):=by unfold cubic twistX;ring
    rw [c,←prod] at curve
    refine ⟨x,y,div_ne_zero Yn fn,?_⟩
    have a:(21*d)^3*(686/(375*(beta x)^2))^2*(octic x-d*y^2)=0:=by
      dsimp [factor] at curve
      linear_combination -21*curve-(21*d)^3*q
    exact sub_eq_zero.mp ((mul_eq_zero.mp a).resolve_left (by positivity [sq_pos_of_ne_zero dn, dn]))

/-- The second quotient comes from changing both signs. Its branch polynomial has degree five. -/
def quintic (z:ℚ) := z*(2*z+3)*(z+1)*(z-1199)*(64*z+439)

theorem second_quotient {x d y:ℚ} (h:octic x=d*y^2) : (d*x*y)^2=d*quintic (x^2) := by
  unfold quintic octic at *
  linear_combination -d*x^2*h

theorem actual_scalar (x:ℚ) :
    ∃ Y:ℚ,Y≠0 ∧ Y^2=cubic (21*(scalarClass x:ℚ)) (twistX (scalarClass x) x) ∧
      liftCoordinate (abscissa x)=x^2 := by
  obtain ⟨sf,y,yn,h⟩:=octic_twist x
  have d : (scalarClass x:ℚ)≠0 := by exact_mod_cast sf.ne_zero
  exact ⟨_,(elliptic_strict d yn h).1,elliptic_point h,(coordinate_inverse x).2⟩

end
end Sun28.ScalarQuotients
#print axioms Sun28.ScalarQuotients.discriminant
#print axioms Sun28.ScalarQuotients.quotient_identity
#print axioms Sun28.ScalarQuotients.elliptic_point
#print axioms Sun28.ScalarQuotients.elliptic_strict
#print axioms Sun28.ScalarQuotients.coordinate_inverse
#print axioms Sun28.ScalarQuotients.coordinate_of_lift
#print axioms Sun28.ScalarQuotients.lift_iff
#print axioms Sun28.ScalarQuotients.second_quotient
#print axioms Sun28.ScalarQuotients.actual_scalar
