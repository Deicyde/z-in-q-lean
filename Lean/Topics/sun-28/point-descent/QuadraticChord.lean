import ZeroOrdinateCore

namespace Sun28.PointDescent
open TwistExtension

def realPart (a k l : ℚ) := a*(a-l)*(a+3*l)+k*(3*a+2*l)
def linearPart (a k l : ℚ) := 3*a^2+k+4*a*l-3*l^2

/-- The remaining root of the cubic cut out by a (possibly twisted) rational line. -/
theorem remaining_root {a k l m n t : ℚ}
    (hr : t*((m*a+n)^2+k*m^2)=realPart a k l)
    (hi : t*(2*(m*a+n)*m)=linearPart a k l) :
    let r := t*m^2-2*l-2*a
    (a^2-k)*r=t*n^2 ∧ t*(m*r+n)^2=r*(r-l)*(r+3*l) := by
  dsimp only
  unfold realPart at hr
  unfold linearPart at hi
  constructor
  · linear_combination a*hi-hr
  · linear_combination (t*m^2-2*l-3*a)*hi+hr

/-- The two line intercepts are nonzero for a positive norm. -/
theorem intercept_product {a c d e t l : ℚ}
    (hr : d^2+t*e^2=realPart a (t*c^2) l)
    (hi : 2*d*e=c*linearPart a (t*c^2) l) :
    2*(a*d-t*c*e)*(a*e-c*d) =
      c*(a^2-t*c^2)*((a^2-t*c^2)+3*l^2) := by
  unfold realPart at hr
  unfold linearPart at hi
  linear_combination (a^2+t*c^2)*hi-2*a*c*hr

private theorem scale_x {b s k r : ℚ} (bn : b≠0) (sn : s≠0)
    (h : (b*s^2)*r=k^2) : r=b*(k/(b*s))^2 := by
  field_simp
  linear_combination h

private theorem ordinate_nonzero {a k l m n t : ℚ}
    (tn : t≠0) (nn : n≠0)
    (hr : t*((m*a+n)^2+k*m^2)=realPart a k l)
    (hi : t*(2*(m*a+n)*m)=linearPart a k l)
    (ex : a^2-k≠l*(3*l+2*a) ∧ a^2-k≠3*l*(l-2*a)) :
    m*(t*m^2-2*l-2*a)+n≠0 := by
  let r := t*m^2-2*l-2*a
  obtain ⟨N,E⟩:=remaining_root hr hi
  change (a^2-k)*r=t*n^2 at N
  change t*(m*r+n)^2=r*(r-l)*(r+3*l) at E
  have rn : r≠0:=by intro h;apply mul_ne_zero tn (pow_ne_zero 2 nn);simpa [h] using N.symm
  intro zero
  change m*r+n=0 at zero
  have coeff : -3*l^2-2*t*m*n=(a^2-k)+2*a*r := by
    dsimp [r];unfold linearPart at hi;linear_combination -hi
  have leading : t*m^2=r+2*l+2*a := by dsimp [r];ring
  have e0 : r*(r-l)*(r+3*l)=0:=by simpa [zero] using E.symm
  rcases mul_eq_zero.mp e0 with z|z
  · have root:=sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left rn)
    rw [root] at coeff leading zero
    apply ex.1
    linear_combination -coeff+2*l*leading-2*t*m*zero
  · have root : r=-3*l:=by linarith
    rw [root] at coeff leading zero
    apply ex.2
    linear_combination -coeff-6*l*leading-2*t*m*zero

def MarkedPoint (b l : ℚ) (nondegenerate : Prop) : Prop := ∃ u y : ℚ,
  u≠0 ∧ (nondegenerate → y≠0) ∧ y^2=(b*u^2)*(b*u^2-l)*(b*u^2+3*l)

/-- Take the trace and the anti-trace of a point whose abscissa has squareclass b as norm. -/
theorem quadratic_marked_pair {a c d e t l b s : ℚ} (bp : 0<b) (tn : t≠0)
    (cn : c≠0) (sn : s≠0) (hn : a^2-t*c^2=b*s^2)
    (hr : d^2+t*e^2=realPart a (t*c^2) l)
    (hi : 2*d*e=c*linearPart a (t*c^2) l) :
    let regular := a^2-t*c^2≠l*(3*l+2*a) ∧ a^2-t*c^2≠3*l*(l-2*a)
    MarkedPoint b l regular ∧ MarkedPoint b (l*t) regular := by
  have B : 0<a^2-t*c^2 := hn ▸ mul_pos bp (sq_pos_of_ne_zero sn)
  have prod := intercept_product hr hi
  have nz : 2*(a*d-t*c*e)*(a*e-c*d)≠0 := by
    rw [prod]
    exact mul_ne_zero (mul_ne_zero cn B.ne') (by nlinarith [sq_nonneg l])
  have en : a*e-c*d≠0 := (mul_ne_zero_iff.mp nz).2
  have dn : a*d-t*c*e≠0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp nz).1).2
  constructor
  · let m := e/c
    let n := d-m*a
    have Hm : m*c=e:=by dsimp [m];field_simp
    have Hn : m*a+n=d:=by dsimp [n];ring
    have nn : n≠0:=by
      intro z
      apply en
      linear_combination -a*Hm+c*Hn-c*z
    have Hr : 1*((m*a+n)^2+t*c^2*m^2)=realPart a (t*c^2) l:=by
      rw [Hn,show t*c^2*m^2=t*e^2 by rw [← Hm];ring];simpa using hr
    have Hi : 1*(2*(m*a+n)*m)=linearPart a (t*c^2) l:=by
      rw [Hn];apply mul_left_cancel₀ cn;linear_combination hi+2*d*Hm
    obtain ⟨N,E⟩:=remaining_root Hr Hi
    rw [hn] at N
    simp only [one_mul] at N E
    have x:=scale_x bp.ne' sn N
    refine ⟨n/(b*s),m*(m^2-2*l-2*a)+n,div_ne_zero nn (mul_ne_zero bp.ne' sn),?_,?_⟩
    · intro ex;simpa only [one_mul] using ordinate_nonzero one_ne_zero nn Hr Hi ex
    · simpa only [←x] using E
  · let m := d/(t*c)
    let n := e-m*a
    have Hm : t*m*c=d:=by dsimp [m];field_simp
    have Hn : m*a+n=e:=by dsimp [n];ring
    have nn : n≠0:=by
      intro z
      apply dn
      linear_combination -a*Hm+t*c*Hn-t*c*z
    have Hr : t*((m*a+n)^2+t*c^2*m^2)=realPart a (t*c^2) l:=by
      rw [Hn,←hr];linear_combination (t*c*m+d)*Hm
    have Hi : t*(2*(m*a+n)*m)=linearPart a (t*c^2) l:=by
      rw [Hn];apply mul_left_cancel₀ cn;linear_combination hi+2*e*Hm
    obtain ⟨N,E⟩:=remaining_root Hr Hi
    rw [hn] at N
    let r := t*m^2-2*l-2*a
    change b*s^2*r=t*n^2 at N
    change t*(m*r+n)^2=r*(r-l)*(r+3*l) at E
    have x:=scale_x bp.ne' sn (r:=t*r) (k:=t*n) (by linear_combination t*N)
    refine ⟨t*n/(b*s),t^2*(m*r+n),div_ne_zero (mul_ne_zero tn nn) (mul_ne_zero bp.ne' sn),?_,?_⟩
    · exact fun ex=>mul_ne_zero (pow_ne_zero 2 tn) (ordinate_nonzero tn nn Hr Hi ex)
    · rw [←x]
      linear_combination t^3*E

theorem quadratic_pair {a c d e t l b s : ℚ} (bp : 0<b) (tn : t≠0)
    (cn : c≠0) (sn : s≠0) (hn : a^2-t*c^2=b*s^2)
    (hr : d^2+t*e^2=realPart a (t*c^2) l)
    (hi : 2*d*e=c*linearPart a (t*c^2) l) : Point b l ∧ Point b (l*t) := by
  obtain ⟨⟨u,y,un,_,hy⟩,⟨v,z,vn,_,hz⟩⟩:=quadratic_marked_pair bp tn cn sn hn hr hi
  exact ⟨⟨u,y,un,hy⟩,v,z,vn,hz⟩

end Sun28.PointDescent
#print axioms Sun28.PointDescent.remaining_root
#print axioms Sun28.PointDescent.intercept_product
#print axioms Sun28.PointDescent.quadratic_marked_pair
#print axioms Sun28.PointDescent.quadratic_pair
