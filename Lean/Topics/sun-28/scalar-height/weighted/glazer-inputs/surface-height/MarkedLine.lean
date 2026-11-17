import Mathlib.Tactic

/-! Recover the two coordinates from the four genus-one quotient models. -/
namespace ZInQBlueprint.FiveMetric
set_option maxHeartbeats 2000000
def invariant (a b c d e : ℚ) : ℚ :=
  let I := 12*a*e-3*b*d+c^2
  let J := 72*a*c*e+9*b*c*d-27*a*d^2-27*b^2*e-2*c^3
  6912*I^3/(4*I^3-J^2)

def legendre (x : ℚ) := 256*(x^2-x+1)^3/(x^2*(x-1)^2)
def orbit (t : ℚ) : Fin 6→ℚ := ![t,1-t,1/t,t/(t-1),(t-1)/t,1/(1-t)]

theorem quartic_table :
    invariant (-43) (-686) (-2915) (-1372) (-172) = legendre (1/2401) ∧
    invariant (-43) 600 (-986) (-600) (-43) = legendre (32/375) ∧
    invariant (-43) 256 (-130) (-768) (-387) = legendre (1/225) ∧
    invariant (-43) 2 505 12 (-1548) = legendre (5/1029) := by norm_num [invariant,legendre]

private theorem orbit_of_equal {x t : ℚ} (x0 : x≠0) (x1 : x≠1) (t0 : t≠0) (t1 : t≠1)
    (eq : legendre x=legendre t) : ∃ i, x=orbit t i := by
  have xt : x-1≠0:=sub_ne_zero.mpr x1
  have tt : t-1≠0:=sub_ne_zero.mpr t1
  have a:= (div_eq_div_iff (mul_ne_zero (pow_ne_zero 2 x0) (pow_ne_zero 2 xt))
      (mul_ne_zero (pow_ne_zero 2 t0) (pow_ne_zero 2 tt))).mp eq
  have f : (x-t)*(x+t-1)*(t*x-1)*((t-1)*x-t)*(t*x-(t-1))*((t-1)*x+1)=0 := by
    linear_combination a / 256
  simp only [mul_eq_zero] at f
  rcases f with (((((h|h)|h)|h)|h)|h)
  · exact ⟨0,by change x=t; linarith⟩
  · exact ⟨1,by change x=1-t; linarith⟩
  · exact ⟨2,(eq_div_iff t0).mpr (by linarith only [h] : x*t=1)⟩
  · exact ⟨3,(eq_div_iff tt).mpr (by linarith only [h] : x*(t-1)=t)⟩
  · exact ⟨4,(eq_div_iff t0).mpr (by linarith only [h] : x*t=t-1)⟩
  · exact ⟨5,(eq_div_iff (sub_ne_zero.mpr (Ne.symm t1))).mpr (by linarith only [h] : x*(1-t)=1)⟩

private theorem unique_rows : ∀ i j : Fin 6,
    let x:=orbit (1/2401) i
    let y:=orbit (32/375) j
    legendre (y/x)=legendre (1/225) →
    legendre ((y-1)/(x-1))=legendre (5/1029) → x=2401 ∧ y=-343/32 := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [orbit,legendre]

/-- Normalize the labeled points 210,105,70 to infinity, zero and one.
The four remaining quotient-invariant equations determine the labeled rational pair. -/
theorem marked_coordinates {x y : ℚ} (x0:x≠0) (x1:x≠1) (y0:y≠0) (y1:y≠1)
    (a:legendre x=invariant (-43) (-686) (-2915) (-1372) (-172))
    (b:legendre y=invariant (-43) 600 (-986) (-600) (-43))
    (c:legendre (y/x)=invariant (-43) 256 (-130) (-768) (-387))
    (d:legendre ((y-1)/(x-1))=invariant (-43) 2 505 12 (-1548)) :
    x=2401 ∧ y=-343/32 := by
  obtain ⟨v,w,q,r⟩:=quartic_table
  obtain ⟨i,hi⟩:=orbit_of_equal x0 x1 (by norm_num) (by norm_num) (a.trans v)
  obtain ⟨j,hj⟩:=orbit_of_equal y0 y1 (by norm_num) (by norm_num) (b.trans w)
  subst x; subst y
  exact unique_rows i j (c.trans q) (d.trans r)

end ZInQBlueprint.FiveMetric
#print axioms ZInQBlueprint.FiveMetric.quartic_table
#print axioms ZInQBlueprint.FiveMetric.marked_coordinates
