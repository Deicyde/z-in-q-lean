import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic.LinearCombination

namespace EllipticOrbit.Law
open WeierstrassCurve.Affine

def curve {K : Type*} [CommRing K] (D : K) : WeierstrassCurve.Affine K :=
  ⟨0,0,0,-D,0⟩

/-- The abscissa map to the projective line, with the standard representative at infinity. -/
def abscissa {K : Type*} [CommRing K] {D : K} : (curve D).Point → K × K
  | .zero => (1,0)
  | .some (x := x) _ => (x,1)

/-- Arbitrary nonzero homogeneous coordinates for a point's abscissa. -/
def Rep {K : Type*} [Field K] {D : K} (P : (curve D).Point) (a b : K) : Prop :=
  ∃ t : K, t ≠ 0 ∧ a=t*(abscissa P).1 ∧ b=t*(abscissa P).2

def dblNum {R : Type*} [CommRing R] (D a b : R) := (a^2+D*b^2)^2
def dblDen {R : Type*} [CommRing R] (D a b : R) := 4*a*b*(a^2-D*b^2)

def Symmetric {R : Type*} [CommRing R] (D a b c e A B C E : R) : Prop :=
  (a*c+D*b*e)^2*(A*E+B*C)=(2*(a*e+b*c)*(a*c-D*b*e))*(A*C) ∧
  (a*c+D*b*e)^2*(B*E)=(a*e-b*c)^2*(A*C)

/-- All three homogeneous coefficients agree up to a single nonzero scalar. -/
def SymmetricRep {K : Type*} [Field K] (D a b c e A B C E : K) : Prop :=
  ∃ k : K, k≠0 ∧ (a*c+D*b*e)^2=k*(A*C) ∧
    2*(a*e+b*c)*(a*c-D*b*e)=k*(A*E+B*C) ∧ (a*e-b*c)^2=k*(B*E)

variable {K : Type*} [Field K] {D : K}

private theorem equation {x y : K} (h : (curve D).Nonsingular x y) : y^2=x^3-D*x := by
  have q := ((curve D).equation_iff x y).mp h.1
  simpa [curve,sub_eq_add_neg] using q

@[simp] theorem abscissa_neg (P : (curve D).Point) : abscissa (-P)=abscissa P := by
  cases P <;> rfl

theorem rep_zero {a b : K} : Rep (0 : (curve D).Point) a b ↔ a≠0 ∧ b=0 := by
  constructor
  · rintro ⟨t,nt,ha,hb⟩
    change a=t*1 at ha
    change b=t*0 at hb
    simpa [ha,hb] using nt
  · rintro ⟨nz,rfl⟩
    exact ⟨a,nz,(mul_one a).symm,(mul_zero a).symm⟩

theorem rep_some {x y a b : K} (h : (curve D).Nonsingular x y) :
    Rep (.some h) a b ↔ b≠0 ∧ a=x*b := by
  constructor
  · rintro ⟨t,nt,ha,hb⟩
    change a=t*x at ha
    change b=t*1 at hb
    simp only [mul_one] at hb
    exact ⟨hb ▸ nt,by rw [ha,hb,mul_comm]⟩
  · rintro ⟨hb,ha⟩
    exact ⟨b,hb,ha.trans (mul_comm ..),(mul_one b).symm⟩

theorem rep_neg {P : (curve D).Point} {a b : K} : Rep (-P) a b ↔ Rep P a b := by
  simp only [Rep,abscissa_neg]

private theorem tangent (D x y : K) (q : y^2=x^3-D*x) (nz : 2*y≠0) :
    (x^2+D)^2=4*x*(x^2-D)*(((3*x^2-D)/(2*y))^2-x-x) := by
  have denom : 4*x*(x^2-D)=(2*y)^2 := by linear_combination (-4)*q
  have sq : ((3*x^2-D)/(2*y))^2*(2*y)^2=(3*x^2-D)^2 := by
    rw [← mul_pow, div_mul_cancel₀ _ nz]
  rw [denom]
  linear_combination (8*x)*q-sq

variable [DecidableEq K]

private theorem normalized_double (P : (curve D).Point) :
    dblNum D (abscissa P).1 (abscissa P).2 * (abscissa (P+P)).2 =
      dblDen D (abscissa P).1 (abscissa P).2 * (abscissa (P+P)).1 := by
  cases P with
  | zero =>
    change dblNum D 1 0*(abscissa ((0 : (curve D).Point)+0)).2=dblDen D 1 0*(abscissa ((0 : (curve D).Point)+0)).1
    rw [zero_add]
    change (1^2+D*0^2)^2*0=(4*1*0*(1^2-D*0^2))*1
    ring
  | @some x y h =>
    have eqn := equation h
    by_cases vert : y=(curve D).negY x y
    · rw [Point.add_self_of_Y_eq vert]
      have hneg : y= -y := by simpa [curve,negY] using vert
      have ty : 2*y=0 := by linear_combination hneg
      change (x^2+D*1^2)^2*0 = (4*x*1*(x^2-D*1^2))*1
      have zero : (2*y)^2=0 := by rw [ty]; ring
      linear_combination 4*eqn-zero
    · rw [Point.add_self_of_Y_ne vert]
      change (x^2+D*1^2)^2*1=(4*x*1*(x^2-D*1^2))*((curve D).addX x x ((curve D).slope x x y y))
      rw [WeierstrassCurve.Affine.slope_of_Y_ne rfl vert]
      have nz : 2*y≠0 := by
        intro z
        apply vert
        change y = -y - 0*x - 0
        linear_combination z
      simpa [curve,addX,negY,sub_eq_add_neg,two_mul] using tangent D x y eqn nz

/-- Kummer doubling for arbitrary nonzero representatives of the actual input and output points. -/
theorem double_cross (P : (curve D).Point) {a b A B : K} (pin : Rep P a b)
    (pout : Rep (P+P) A B) : dblNum D a b * B = dblDen D a b * A := by
  obtain ⟨s,_,rfl,rfl⟩ := pin
  obtain ⟨t,_,rfl,rfl⟩ := pout
  have h := normalized_double P
  dsimp only [dblNum,dblDen] at h ⊢
  linear_combination (s^4*t)*h

omit [DecidableEq K] in
theorem canonical_rep (P : (curve D).Point) : Rep P (abscissa P).1 (abscissa P).2 :=
  ⟨1,one_ne_zero,(one_mul _).symm,(one_mul _).symm⟩

omit [DecidableEq K] in
private theorem rep_of_cross (P : (curve D).Point) {a b : K} (nz : a≠0 ∨ b≠0)
    (cross : a*(abscissa P).2=b*(abscissa P).1) : Rep P a b := by
  cases P with
  | zero =>
    change a*0=b*1 at cross
    have hb : b=0 := by simpa using cross.symm
    exact rep_zero.2 ⟨nz.resolve_right (fun h => h hb),hb⟩
  | @some x y h =>
    change a*1=b*x at cross
    have ha : a=x*b := by simpa only [mul_one,mul_comm b x] using cross
    apply (rep_some h).2
    refine ⟨?_,ha⟩
    intro hb
    have az : a=0 := by simp [ha,hb]
    exact nz.elim (fun h => h az) (fun h => h hb)

omit [DecidableEq K] in
private theorem raw_nonzero (P : (curve D).Point) :
    dblNum D (abscissa P).1 (abscissa P).2≠0 ∨ dblDen D (abscissa P).1 (abscissa P).2≠0 := by
  cases P with
  | zero => left; change (1^2+D*0^2)^2≠0; simp
  | @some x y h =>
    by_contra! fail
    change (x^2+D*1^2)^2=0 ∧ 4*x*1*(x^2-D*1^2)=0 at fail
    simp only [one_pow,mul_one] at fail
    have plus := (pow_eq_zero_iff (by decide : 2≠0)).mp fail.1
    have tx : (2*x)^3=0 := by linear_combination fail.2+(4*x)*plus
    have ty : (2*y)^2=0 := by linear_combination 4*(equation h)+fail.2
    have vanx := (pow_eq_zero_iff (by decide : 3≠0)).mp tx
    have vany := (pow_eq_zero_iff (by decide : 2≠0)).mp ty
    have sing := (((curve D).nonsingular_iff' x y).mp h).2
    rcases sing with dx | dy
    · apply dx
      change 0*y-(3*x^2+2*0*x+-D)=0
      linear_combination plus-(2*x)*vanx
    · apply dy
      change 2*y+0*x+0=0
      linear_combination vany

/-- The two raw quartics themselves give a nonzero representative of the actual double.
Nonsingularity built into Mathlib's Point suffices in every characteristic. -/
theorem double_rep (P : (curve D).Point) {a b : K} (pin : Rep P a b) :
    Rep (P+P) (dblNum D a b) (dblDen D a b) := by
  apply rep_of_cross _ _ (double_cross P pin (canonical_rep (P+P)))
  obtain ⟨s,hn,rfl,rfl⟩ := pin
  have top : dblNum D (s*(abscissa P).1) (s*(abscissa P).2)=s^4*dblNum D (abscissa P).1 (abscissa P).2 := by
    dsimp [dblNum]; ring
  have bot : dblDen D (s*(abscissa P).1) (s*(abscissa P).2)=s^4*dblDen D (abscissa P).1 (abscissa P).2 := by
    dsimp [dblDen]; ring
  rw [top,bot]
  exact (raw_nonzero P).imp (mul_ne_zero (pow_ne_zero _ hn)) (mul_ne_zero (pow_ne_zero _ hn))

omit [DecidableEq K] in
private theorem chord (D x y u v : K) (px : y^2=x^3-D*x) (qu : v^2=u^3-D*u) (hx : x≠u) :
    SymmetricRep D x 1 u 1 (((y-v)/(x-u))^2-x-u) 1 (((y+v)/(x-u))^2-x-u) 1 := by
  let np := (y-v)^2-(x+u)*(x-u)^2
  let nm := (y+v)^2-(x+u)*(x-u)^2
  let xp := ((y-v)/(x-u))^2-x-u
  let xm := ((y+v)/(x-u))^2-x-u
  have nz := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  have sum : np+nm=2*(x+u)*(x*u-D) := by dsimp [np,nm]; linear_combination 2*px+2*qu
  have m1 : np=(x+u)*(x*u-D)-2*y*v := by dsimp [np]; linear_combination px+qu
  have m2 : nm=(x+u)*(x*u-D)+2*y*v := by dsimp [nm]; linear_combination px+qu
  have prod : np*nm=(x-u)^2*(x*u+D)^2 := by
    rw [m1,m2]
    linear_combination (-4*v^2)*px+(-4*(x^3-D*x))*qu
  have sqdiv (t : K) : (t/(x-u))^2*(x-u)^2=t^2 := by
    rw [← mul_pow, div_mul_cancel₀ _ (sub_ne_zero.mpr hx)]
  have clp : (x-u)^2*xp=np := by dsimp [xp,np]; linear_combination sqdiv (y-v)
  have clm : (x-u)^2*xm=nm := by dsimp [xm,nm]; linear_combination sqdiv (y+v)
  have sm : (x-u)^2*(xp+xm)=2*(x+u)*(x*u-D) := by linear_combination clp+clm+sum
  have z : (x-u)^2*((x-u)^2*(xp*xm)-(x*u+D)^2)=0 := by
    linear_combination ((x-u)^2*xm)*clp+np*clm+prod
  have pr := sub_eq_zero.mp ((mul_eq_zero.mp z).resolve_left nz)
  change SymmetricRep D x 1 u 1 xp 1 xm 1
  refine ⟨(x-u)^2,nz,?_,?_,?_⟩
  · simpa only [mul_one,one_mul] using pr.symm
  · simpa only [mul_one,one_mul] using sm.symm
  · simp

omit [DecidableEq K] in
private theorem symmetric_swap {D a b c e A B C E : K}
    (h : SymmetricRep D a b c e A B C E) : SymmetricRep D a b c e C E A B := by
  obtain ⟨k,hk,top,mid,bot⟩ := h
  refine ⟨k,hk,?_,?_,?_⟩
  · linear_combination top
  · linear_combination mid
  · linear_combination bot

private theorem symmetric_diagonal (P : (curve D).Point) :
    SymmetricRep D (abscissa P).1 (abscissa P).2 (abscissa P).1 (abscissa P).2
      (abscissa (P+P)).1 (abscissa (P+P)).2 1 0 := by
  obtain ⟨k,hk,top,bot⟩ := double_rep P (canonical_rep P)
  dsimp only [dblNum] at top
  dsimp only [dblDen] at bot
  refine ⟨k,hk,?_,?_,?_⟩
  · linear_combination top
  · linear_combination bot
  · ring

private theorem normalized_symmetric (P Q : (curve D).Point) :
    SymmetricRep D (abscissa P).1 (abscissa P).2 (abscissa Q).1 (abscissa Q).2
      (abscissa (P+Q)).1 (abscissa (P+Q)).2 (abscissa (P-Q)).1 (abscissa (P-Q)).2 := by
  by_cases p0 : P=0
  · subst P
    simp only [zero_add,zero_sub,abscissa_neg]
    change SymmetricRep D 1 0 _ _ _ _ _ _
    refine ⟨1,one_ne_zero,?_,?_,?_⟩ <;> ring
  by_cases q0 : Q=0
  · subst Q
    simp only [add_zero,sub_zero]
    change SymmetricRep D _ _ 1 0 _ _ _ _
    refine ⟨1,one_ne_zero,?_,?_,?_⟩ <;> ring
  by_cases same : Q=P
  · subst Q
    simpa only [sub_self] using symmetric_diagonal P
  by_cases opposite : Q= -P
  · subst Q
    simpa only [abscissa_neg,add_neg_cancel,sub_neg_eq_add] using symmetric_swap (symmetric_diagonal P)
  cases P with
  | zero => exact (p0 rfl).elim
  | @some x y hp =>
    cases Q with
    | zero => exact (q0 rfl).elim
    | @some u v hq =>
      have hx : x≠u := by
        rintro rfl
        rcases Y_eq_of_X_eq hq.1 hp.1 rfl with eq | eq
        · subst v; exact same rfl
        · subst v; exact opposite rfl
      rw [sub_eq_add_neg,Point.neg_some,Point.add_of_X_ne hx,Point.add_of_X_ne hx]
      change SymmetricRep D x 1 u 1
        ((curve D).addX x u ((curve D).slope x u y v)) 1
        ((curve D).addX x u ((curve D).slope x u y ((curve D).negY u v))) 1
      rw [slope_of_X_ne hx,slope_of_X_ne hx]
      simpa [curve,addX,negY,sub_eq_add_neg] using chord D x y u v (equation hp) (equation hq) hx

/-- The full biquadratic addition formula as an equality of nonzero projective
representatives for the symmetric pair of actual abscissae. -/
theorem symmetric_rep (P Q : (curve D).Point) {a b c e A B C E : K}
    (p : Rep P a b) (q : Rep Q c e) (sum : Rep (P+Q) A B) (diff : Rep (P-Q) C E) :
    SymmetricRep D a b c e A B C E := by
  obtain ⟨s,hs,rfl,rfl⟩ := p
  obtain ⟨t,ht,rfl,rfl⟩ := q
  obtain ⟨u,hu,rfl,rfl⟩ := sum
  obtain ⟨v,hv,rfl,rfl⟩ := diff
  obtain ⟨k,hk,top,mid,bot⟩ := normalized_symmetric P Q
  let c := (s*t)^2*k/(u*v)
  have scale : c*(u*v)=(s*t)^2*k := div_mul_cancel₀ _ (mul_ne_zero hu hv)
  have nz : c≠0 := div_ne_zero (mul_ne_zero (pow_ne_zero _ (mul_ne_zero hs ht)) hk) (mul_ne_zero hu hv)
  refine ⟨c,nz,?_,?_,?_⟩
  · linear_combination (s*t)^2*top-((abscissa (P+Q)).1*(abscissa (P-Q)).1)*scale
  · linear_combination (s*t)^2*mid-((abscissa (P+Q)).1*(abscissa (P-Q)).2+
      (abscissa (P+Q)).2*(abscissa (P-Q)).1)*scale
  · linear_combination (s*t)^2*bot-((abscissa (P+Q)).2*(abscissa (P-Q)).2)*scale

omit [DecidableEq K] in
theorem SymmetricRep.minors {D a b c e A B C E : K} (h : SymmetricRep D a b c e A B C E) :
    Symmetric D a b c e A B C E ∧
      (2*(a*e+b*c)*(a*c-D*b*e))*(B*E)=(a*e-b*c)^2*(A*E+B*C) := by
  obtain ⟨k,_,top,mid,bot⟩ := h
  refine ⟨⟨?_,?_⟩,?_⟩
  · rw [top,mid]; ring
  · rw [top,bot]; ring
  · rw [mid,bot]; ring

/-- The two numerator minors used in the finite arithmetic bound. -/
theorem symmetric_cross (P Q : (curve D).Point) {a b c e A B C E : K}
    (p : Rep P a b) (q : Rep Q c e) (sum : Rep (P+Q) A B) (diff : Rep (P-Q) C E) :
    Symmetric D a b c e A B C E := (symmetric_rep P Q p q sum diff).minors.1

theorem orbit_double_cross (P : (curve D).Point) (A B : ℕ → K)
    (coordinates : ∀ i, Rep (i • P) (A i) (B i)) (i : ℕ) :
    dblNum D (A i) (B i)*B (2*i)=dblDen D (A i) (B i)*A (2*i) := by
  apply double_cross (i • P) (coordinates i)
  simpa only [mul_smul,two_nsmul] using coordinates (2*i)

theorem orbit_symmetric_cross (P : (curve D).Point) (A B : ℕ → K)
    (coordinates : ∀ i, Rep (i • P) (A i) (B i)) (j : ℕ) :
    Symmetric D (A (2*(j+2))) (B (2*(j+2))) (A (2*j)) (B (2*j))
      (A (4*(j+1))) (B (4*(j+1))) (A 4) (B 4) := by
  let u := 2*(j+2); let v := 2*j; let w := 4*(j+1)
  have add : u+v=w := by dsimp [u,v,w]; ring
  have apart : u=v+4 := by dsimp [u,v]; ring
  have eqs : u • P+v • P=w • P := by rw [← add_nsmul,add]
  have eqd : u • P-v • P=4 • P := by rw [apart,add_nsmul]; abel
  apply symmetric_cross (u • P) (v • P) (coordinates u) (coordinates v)
  · rw [eqs]; exact coordinates w
  · rw [eqd]; exact coordinates 4

variable {R : Type*} [CommRing R]

theorem orbit_double_cross_of_map (f : R →+* K) (inj : Function.Injective f) {d : R}
    (coeff : f d=D) (P : (curve D).Point) (A B : ℕ → R)
    (coordinates : ∀ i, Rep (i • P) (f (A i)) (f (B i))) (i : ℕ) :
    dblNum d (A i) (B i)*B (2*i)=dblDen d (A i) (B i)*A (2*i) := by
  apply inj
  simpa only [dblNum,dblDen,map_mul,map_pow,map_add,map_sub,map_ofNat,coeff] using
    orbit_double_cross P (fun k => f (A k)) (fun k => f (B k)) coordinates i

theorem orbit_symmetric_cross_of_map (f : R →+* K) (inj : Function.Injective f) {d : R}
    (coeff : f d=D) (P : (curve D).Point) (A B : ℕ → R)
    (coordinates : ∀ i, Rep (i • P) (f (A i)) (f (B i))) (j : ℕ) :
    Symmetric d (A (2*(j+2))) (B (2*(j+2))) (A (2*j)) (B (2*j))
      (A (4*(j+1))) (B (4*(j+1))) (A 4) (B 4) := by
  have h := orbit_symmetric_cross P (fun k => f (A k)) (fun k => f (B k)) coordinates j
  constructor
  · apply inj; simpa only [map_mul,map_pow,map_add,map_sub,map_ofNat,coeff] using h.1
  · apply inj; simpa only [map_mul,map_pow,map_add,map_sub,map_ofNat,coeff] using h.2

end EllipticOrbit.Law
