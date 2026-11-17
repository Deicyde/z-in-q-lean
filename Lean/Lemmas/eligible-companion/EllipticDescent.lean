import Std

namespace CompanionDescent
open Lean.Grind

def quartic (b x : Rat) := (x^2-b)*(x^2+3*b)
def D (b a k : Rat) := (a^2-b)*(k^2+3*b)
def cubic (l x : Rat) := x*(x+3)*(x+l^2-1)
def nonsquare (q : Rat) : Prop := ∀ x : Rat, x^2 ≠ q

/-- The intermediate hyperbola with a nonzero squareclass witness. -/
def Hyperbola (b θ : Rat) : Prop := ∃ a k z h : Rat, h≠0 ∧
  D b a k = z^2-4*b^2 ∧ D b a k = θ*h^2

/-- Finite abscissa in [-3b]; the relation for l has its unique solution
when θ is nonsquare. The literal squareclass coordinate is w. -/
def EllipticFibre (b θ : Rat) : Prop := ∃ u l X Y w : Rat,
  u≠0 ∧ (u^2-θ)*l=2*(u^2+θ) ∧ w≠0 ∧ X=(-3*b)*w^2 ∧ Y^2=cubic l X

private theorem nz {v w : Rat} (h : v≠0) (j : w≠0) : v*w≠0 :=
  fun e => (Rat.mul_eq_zero.mp e).elim h j

private theorem invnz {q : Rat} (hq : q≠0) : q⁻¹≠0 := by
  have hi : q*q⁻¹=1 := by grind
  intro e; rw [e] at hi; grind

private theorem sqnonneg (q : Rat) : 0≤q^2 := by
  rcases Rat.nonneg_total q with h|h
  · exact Rat.pow_nonneg h
  · have e := Rat.mul_nonneg h h
    rwa [show -q*(-q)=q^2 by grobner] at e

private theorem qnz (b x : Rat) (hb : 0<b) (ns : nonsquare b) : quartic b x≠0 := by
  have nn:=sqnonneg x
  exact nz (by have := ns x; grind) (by grind)

/-- The two composition identities for rational finite slopes. -/
theorem product_identity (b x y a k : Rat) (ha : a*(x+y)=x*y+b)
    (hk : k*(x-y)=x*y+3*b) :
    quartic b x*quartic b y = D b a k*(x^2-y^2)^2 := by
  have ha' : (a^2-b)*(x+y)^2=(x^2-b)*(y^2-b) := by
    calc _ = (a*(x+y))^2-b*(x+y)^2 := by grobner
         _ = _ := by rw [ha]; grobner
  have hk' : (k^2+3*b)*(x-y)^2=(x^2+3*b)*(y^2+3*b) := by
    calc _ = (k*(x-y))^2+3*b*(x-y)^2 := by grobner
         _ = _ := by rw [hk]; grobner
  unfold quartic D
  calc _ = ((x^2-b)*(y^2-b))*((x^2+3*b)*(y^2+3*b)) := by grobner
       _ = _ := by rw [← ha',← hk']; grobner

theorem difference_identity (b x y : Rat) :
    ((x^2+b)*(y^2+b)-4*b^2)^2-4*b^2*(x^2-y^2)^2=quartic b x*quartic b y := by
  unfold quartic; grobner

private theorem cancel_sq {f g d : Rat} (nd : d≠0) (eqn : f*d^2=g*d^2) : f=g := by
  have hi : d*d⁻¹=1 := by grind
  calc f = (f*d^2)*(d⁻¹)^2 := by grobner
       _ = g := by rw [eqn]; grobner

private theorem lift_square (θ d w f : Rat) (nt : θ≠0) (nd : d≠0)
    (nf : f≠0) (hw : w^2=θ*f*d^2) : ∃ h : Rat, h≠0 ∧ f=θ*h^2 := by
  have hf := nz (nz (nz nt nf) nd) nd
  have nw : w≠0 := by intro e; rw [e] at hw; apply hf; grobner
  have it : θ*θ⁻¹=1 := by grind
  have id : d*d⁻¹=1 := by grind
  refine ⟨w*θ⁻¹*d⁻¹,nz (nz nw (invnz nt)) (invnz nd),?_⟩
  calc f = θ*(θ*f*d^2)*(θ⁻¹)^2*(d⁻¹)^2 := by grobner
       _ = _ := by rw [← hw]; grobner

/-- Normalized homogeneous slopes: none denotes infinity (1:0). -/
def eval (b : Rat) : Option Rat → Rat
  | none => 1
  | some x => quartic b x

def Weak (b θ : Rat) : Prop := ∃ x y : Option Rat, ∃ w : Rat,
  w^2=θ*eval b x*eval b y

private theorem finite_forward (b θ x y w : Rat) (hb : 0<b) (nb : nonsquare b)
    (ns : nonsquare θ) (hw : w^2=θ*quartic b x*quartic b y) : Hyperbola b θ := by
  have hx:=qnz b x hb nb
  have hy:=qnz b y hb nb
  have nt : θ≠0 := by have := ns 0; grind
  let d:=x^2-y^2
  have nd : d≠0 := by
    intro e
    have e' : x^2=y^2 := by dsimp [d] at e; grind
    have f : quartic b x=quartic b y := by unfold quartic; rw [e']
    have i : quartic b x*(quartic b x)⁻¹=1 := by grind
    apply ns (w*(quartic b x)⁻¹)
    calc _ = w^2*((quartic b x)⁻¹)^2 := by grobner
         _ = θ := by rw [hw,← f]; grobner
  have nplus : x+y≠0 := by intro e; apply nd; dsimp [d]; grobner
  have nminus : x-y≠0 := by intro e; apply nd; dsimp [d]; grobner
  have ip : (x+y)*(x+y)⁻¹=1 := by grind
  have im : (x-y)*(x-y)⁻¹=1 := by grind
  have id : d*d⁻¹=1 := by grind
  let a:=(x*y+b)*(x+y)⁻¹
  let k:=(x*y+3*b)*(x-y)⁻¹
  let z:=((x^2+b)*(y^2+b)-4*b^2)*d⁻¹
  have ha : a*(x+y)=x*y+b := by dsimp [a]; grobner
  have hk : k*(x-y)=x*y+3*b := by dsimp [k]; grobner
  have prod : quartic b x*quartic b y=D b a k*d^2 := product_identity b x y a k ha hk
  have ng : D b a k≠0 := by intro h; have ne:=nz hx hy; apply ne; rw [prod,h]; grobner
  have hz : z*d=(x^2+b)*(y^2+b)-4*b^2 := by dsimp [z]; grobner
  have diff : (z^2-4*b^2)*d^2=D b a k*d^2 := by
    calc _ = (z*d)^2-4*b^2*d^2 := by grobner
         _ = _ := by rw [hz]; exact (difference_identity b x y).trans prod
  obtain ⟨h,nh,H⟩ := lift_square θ d w (D b a k) nt nd ng (by rw [hw]; grobner)
  exact ⟨a,k,z,h,nh,(cancel_sq nd diff).symm,H⟩

private theorem endpoint_forward (b θ y w : Rat) (hb : 0<b) (nb : nonsquare b)
    (ns : nonsquare θ) (hw : w^2=θ*quartic b y) : Hyperbola b θ := by
  have nt : θ≠0 := by have := ns 0; grind
  obtain ⟨h,nh,H⟩ := lift_square θ 1 w (quartic b y) nt (by decide) (qnz b y hb nb) (by grobner)
  refine ⟨y,y,y^2+b,h,nh,?_,H⟩
  unfold D; grobner

/-- Independent signs, zero slopes, a single endpoint and both endpoints. -/
theorem weak_to_hyperbola (b θ : Rat) (hb : 0<b) (nb : nonsquare b)
    (ns : nonsquare θ) (hw : Weak b θ) : Hyperbola b θ := by
  obtain ⟨x,y,w,H⟩ := hw
  cases x with
  | none =>
    cases y with
    | none =>
      have e : w^2=θ := by simpa [eval] using H
      exact False.elim (ns w e)
    | some y => exact endpoint_forward b θ y w hb nb ns (by simpa [eval] using H)
  | some x =>
    cases y with
    | none => exact endpoint_forward b θ x w hb nb ns (by simpa [eval] using H)
    | some y => exact finite_forward b θ x y w hb nb ns H

private theorem inverse_slopes (b a k z : Rat) (hz : D b a k=z^2-4*b^2)
    (nm : k-a≠0) (np : a+k≠0) :
    ∃ x y : Rat, a*(x+y)=x*y+b ∧ k*(x-y)=x*y+3*b := by
  let A:=b+a*k+z
  let B:=a*k-b+z
  let m:=k-a
  let p:=a+k
  have im : m*m⁻¹=1 := by apply Field.mul_inv_cancel nm
  have ip : p*p⁻¹=1 := by apply Field.mul_inv_cancel np
  have eq1 : a*(A*p+B*m)=A*B+b*m*p := by dsimp [A,B,p,m]; unfold D at hz; grobner
  have eq2 : k*(A*p-B*m)=A*B+3*b*m*p := by dsimp [A,B,p,m]; unfold D at hz; grobner
  refine ⟨A*m⁻¹,B*p⁻¹,?_,?_⟩
  · calc _ = (a*(A*p+B*m))*m⁻¹*p⁻¹ := by grobner
         _ = _ := by rw [eq1]; grobner
  · calc _ = (k*(A*p-B*m))*m⁻¹*p⁻¹ := by grobner
         _ = _ := by rw [eq2]; grobner

/-- The two equal-square parameter cases go to infinity. No ordinate is divided by. -/
theorem hyperbola_to_weak (b θ : Rat) (H : Hyperbola b θ) : Weak b θ := by
  obtain ⟨a,k,z,h,_nh,hz,hd⟩ := H
  by_cases e : k-a=0 ∨ a+k=0
  · have ek : k^2=a^2 := by rcases e with e|e <;> grobner
    have d : quartic b a=θ*h^2 := by unfold D at hd; rw [ek] at hd; exact hd
    refine ⟨none,some a,θ*h,?_⟩
    change (θ*h)^2=θ*1*quartic b a
    rw [d]; grobner
  · have nm : k-a≠0 := fun y => e (Or.inl y)
    have np : a+k≠0 := fun y => e (Or.inr y)
    obtain ⟨x,y,hx,hy⟩:=inverse_slopes b a k z hz nm np
    have prod:=product_identity b x y a k hx hy
    refine ⟨some x,some y,θ*h*(x^2-y^2),?_⟩
    change _=θ*quartic b x*quartic b y
    calc _ = θ*(D b a k*(x^2-y^2)^2) := by rw [hd]; grobner
         _ = _ := by rw [← prod]; grobner

private theorem conic_to_parameter (θ l j : Rat) (nt : θ≠0) (nj : j≠0)
    (he : l^2-4=θ*j^2) : ∃ u : Rat, u≠0 ∧ (u^2-θ)*l=2*(u^2+θ) := by
  have g := nz (nz nt nj) nj
  have np : l+2≠0 := by intro h; apply g; grobner
  have ij : j*j⁻¹=1 := by grind
  let u:=(l+2)*j⁻¹
  have h : u*j=l+2 := by dsimp [u]; grobner
  refine ⟨u,nz np (invnz nj),?_⟩
  have f : u^2*(l-2)*j^2=(θ*(l+2))*j^2 := by
    calc _ = (u*j)^2*(l-2) := by grobner
         _ = (l+2)*(l^2-4) := by rw [h]; grobner
         _ = _ := by rw [he]; grobner
  have f' := cancel_sq nj f
  grobner

private theorem parameter_to_conic (θ u l : Rat) (nu : u≠0) (ns : nonsquare θ)
    (rel : (u^2-θ)*l=2*(u^2+θ)) : ∃ j : Rat, j≠0 ∧ l^2-4=θ*j^2 := by
  let d:=u^2-θ
  have nd : d≠0 := by have := ns u; dsimp [d]; grind
  have id : d*d⁻¹=1 := by grind
  change d*l=2*(u^2+θ) at rel
  have f : (l^2-4)*d^2=θ*(4*u)^2 := by
    calc _ = (d*l)^2-4*d^2 := by grobner
         _ = _ := by rw [rel]; dsimp [d]; grobner
  refine ⟨4*u*d⁻¹,nz (nz (by decide) nu) (invnz nd),?_⟩
  calc l^2-4 = ((l^2-4)*d^2)*(d⁻¹)^2 := by grobner
       _ = _ := by rw [f]; grobner

/-- The quartic maps to the indicated abscissa class, including k=0. -/
theorem curve_identity (b a k l X Y : Rat) (nb : b≠0)
    (hx : b*X= -3*a^2) (hy : b^2*Y=3*a*k*(a^2-b))
    (hD : D b a k=b^2*(l^2-4)) : Y^2=cubic l X := by
  have ib : b*b⁻¹=1 := by grind
  have hx2 : b*(X+3)= -3*(a^2-b) := by grobner
  have hx3 : b^2*(X+l^2-1)=b^2*(l^2-1)-3*b*a^2 := by grobner
  have hk : k^2*(a^2-b)=b^2*(l^2-1)-3*b*a^2 := by unfold D at hD; grobner
  have p : b^4*cubic l X=(b^2*Y)^2 := by
    calc _ = (b*X)*(b*(X+3))*(b^2*(X+l^2-1)) := by unfold cubic; grobner
         _ = _ := by rw [hx,hx2,hx3,← hk,hy]; grobner
  calc Y^2 = (b^2*Y)^2*(b⁻¹)^4 := by grobner
       _ = _ := by rw [← p]; grobner

private theorem curve_inverse (b a k l X Y : Rat) (na : a≠0)
    (nat' : a^2-b≠0) (hx : b*X= -3*a^2) (hy : b^2*Y=3*a*k*(a^2-b))
    (hc : Y^2=cubic l X) : D b a k=b^2*(l^2-4) := by
  let t:=a^2-b
  have it : t*t⁻¹=1 := Field.mul_inv_cancel nat'
  have ia : a*a⁻¹=1 := by grind
  have hx2 : b*(X+3)= -3*t := by dsimp [t]; grobner
  have hx3 : b^2*(X+l^2-1)=b^2*(l^2-1)-3*b*a^2 := by grobner
  have p : 9*a^2*t*(b^2*(l^2-1)-3*b*a^2)=(3*a*k*t)^2 := by
    calc _ = (b*X)*(b*(X+3))*(b^2*(X+l^2-1)) := by rw [hx,hx2,hx3]; grobner
         _ = b^4*cubic l X := by unfold cubic; grobner
         _ = (b^2*Y)^2 := by rw [← hc]; grobner
         _ = _ := by rw [hy]
  have factor : (9*a^2*t)*((b^2*(l^2-1)-3*b*a^2)-k^2*t)=0 := by grobner
  have non : 9*a^2*t≠0 := nz (nz (by decide) ((show a^2≠0 from by have h:=nz na na; intro e; apply h; grobner))) nat'
  have e := (Rat.mul_eq_zero.mp factor).resolve_left non
  dsimp [t] at e
  unfold D; grobner

/-- The hyperbola supplies a rational point and its literal abscissa square. -/
theorem hyperbola_to_elliptic (b θ : Rat) (hb : 0<b) (ht : 0<θ)
    (H : Hyperbola b θ) : EllipticFibre b θ := by
  obtain ⟨a,k,z,h,nh,hz,hd⟩ := H
  have nb : b≠0 := by grind
  have nt : θ≠0 := by grind
  have ib : b*b⁻¹=1 := by grind
  have na : a≠0 := by
    intro zero
    have kn:=sqnonneg k
    have hn:=sqnonneg h
    have qneg : 0<k^2+3*b := by grind
    have negprod:=Rat.mul_lt_mul_of_pos_right (show -b<0 by grind) qneg
    have hnon:=Rat.mul_nonneg (show 0≤θ by grind) hn
    unfold D at hd; rw [zero] at hd
    have e : -b*(k^2+3*b)=θ*h^2 := by grobner
    grind
  let l:=z*b⁻¹
  let j:=h*b⁻¹
  have nj : j≠0 := nz nh (invnz nb)
  have cl : l^2-4=θ*j^2 := by dsimp [l,j]; grobner
  obtain ⟨u,nu,eq⟩:=conic_to_parameter θ l j nt nj cl
  let w:=a*b⁻¹
  let X:=(-3*b)*w^2
  let Y:=(3*a*k*(a^2-b))*(b⁻¹)^2
  refine ⟨u,l,X,Y,w,nu,eq,nz na (invnz nb),rfl,?_⟩
  exact curve_identity b a k l X Y nb (by dsimp [X,w]; grobner)
    (by dsimp [Y]; grobner) (by dsimp [l]; grobner)

/-- Every point in the specified class lifts, including zero ordinate. -/
theorem elliptic_to_hyperbola (b θ : Rat) (hb : 0<b) (nb : nonsquare b)
    (ns : nonsquare θ) (H : EllipticFibre b θ) : Hyperbola b θ := by
  obtain ⟨u,l,X,Y,w,nu,rel,nw,hX,hc⟩ := H
  obtain ⟨j,nj,eq⟩:=parameter_to_conic θ u l nu ns rel
  have b0 : b≠0 := by grind
  let a:=b*w
  have na : a≠0 := nz b0 nw
  have nat' : a^2-b≠0 := by have := nb a; grind
  let d:=3*a*(a^2-b)
  have nd : d≠0 := nz (nz (by decide) na) nat'
  have id : d*d⁻¹=1 := by grind
  let k:=b^2*Y*d⁻¹
  have hx : b*X= -3*a^2 := by rw [hX]; dsimp [a]; grobner
  have hy : b^2*Y=3*a*k*(a^2-b) := by
    calc _ = (b^2*Y*d⁻¹)*d := by grobner
         _ = _ := by dsimp [d,k]; grobner
  have e:=curve_inverse b a k l X Y na nat' hx hy hc
  refine ⟨a,k,b*l,b*j,nz b0 nj,?_,?_⟩
  · rw [e]; grobner
  · rw [e,eq]; grobner

/-- Exact criterion for two rational projective slopes, including infinity. -/
theorem weak_iff_elliptic (b θ : Rat) (hb : 0<b) (nb : nonsquare b)
    (ht : 0<θ) (ns : nonsquare θ) : Weak b θ ↔ EllipticFibre b θ := by
  constructor
  · intro hw
    exact hyperbola_to_elliptic b θ hb ht (weak_to_hyperbola b θ hb nb ns hw)
  · intro he
    exact hyperbola_to_weak b θ (elliptic_to_hyperbola b θ hb nb ns he)

/-- Reciprocal parameter, equal cubic, and explicit intersections with one line. -/
theorem reciprocal_fibre (θ u l : Rat) (nu : u≠0)
    (rel : (u^2-θ)*l=2*(u^2+θ)) :
    ((θ*u⁻¹)^2-θ)*(-l)=2*((θ*u⁻¹)^2+θ) ∧ (∀ X, cubic (-l) X=cubic l X) ∧
    (∀ X, (X+l^2-1)^2-cubic l X = -(X-(l-1))*(X-(-l-1))*(X-(1-l^2))) := by
  have iu : u*u⁻¹=1 := by grind
  refine ⟨?_,fun X => ?_,fun X => ?_⟩
  · grobner
  · unfold cubic; grobner
  · unfold cubic; grobner

/-- The homogeneous quartic and the projective predicate used in the pole. -/
def homogeneous (b X S : Rat) := (X^2-b*S^2)*(X^2+3*b*S^2)

def ProjectiveWeak (b θ : Rat) : Prop :=
  ∃ X S B A z : Rat, (X≠0 ∨ S≠0) ∧ (B≠0 ∨ A≠0) ∧
    z^2=θ*homogeneous b X S*homogeneous b B A

private theorem normalize (b X S : Rat) (ne : X≠0 ∨ S≠0) :
    ∃ x : Option Rat, ∃ c : Rat, c≠0 ∧ homogeneous b X S=eval b x*c^4 := by
  by_cases hs : S=0
  · have hx : X≠0 := ne.elim id (fun h => False.elim (h hs))
    refine ⟨none,X,hx,?_⟩
    rw [hs]; unfold homogeneous eval; grobner
  · have hi : S*S⁻¹=1 := by grind
    refine ⟨some (X*S⁻¹),S,hs,?_⟩
    unfold homogeneous eval quartic
    have h : (X*S⁻¹)^2*S^2=X^2 := by grobner
    calc _ = (((X*S⁻¹)^2*S^2)-b*S^2)*(((X*S⁻¹)^2*S^2)+3*b*S^2) := by rw [h]
         _ = _ := by grobner

private theorem representative (b : Rat) (x : Option Rat) :
    ∃ X S : Rat, (X≠0 ∨ S≠0) ∧ homogeneous b X S=eval b x := by
  cases x with
  | none => exact ⟨1,0,Or.inl (by decide),by unfold homogeneous eval; grobner⟩
  | some x => exact ⟨x,1,Or.inr (by decide),by unfold homogeneous eval quartic; grobner⟩

/-- Passing to normalized slopes and back preserves the square even at infinity. -/
theorem projective_iff_normalized (b θ : Rat) : ProjectiveWeak b θ ↔ Weak b θ := by
  constructor
  · rintro ⟨X,S,B,A,w,hX,hB,hw⟩
    obtain ⟨x,d,nd,eqx⟩:=normalize b X S hX
    obtain ⟨y,e,ne,eqy⟩:=normalize b B A hB
    have id : d*d⁻¹=1 := by grind
    have ie : e*e⁻¹=1 := by grind
    refine ⟨x,y,w*(d⁻¹)^2*(e⁻¹)^2,?_⟩
    calc _ = w^2*(d⁻¹)^4*(e⁻¹)^4 := by grobner
         _ = (θ*eval b x*eval b y)*(d*d⁻¹)^4*(e*e⁻¹)^4 := by rw [hw,eqx,eqy]; grobner
         _ = _ := by rw [id,ie]; grobner
  · rintro ⟨x,y,w,hw⟩
    obtain ⟨X,S,hX,eqx⟩:=representative b x
    obtain ⟨B,A,hB,eqy⟩:=representative b y
    exact ⟨X,S,B,A,w,hX,hB,by rw [eqx,eqy]; exact hw⟩

/-- A nontrivial squareclass and both homogeneous slope guards, with no height bound. -/
theorem projective_iff_elliptic (b θ : Rat) (hb : 0<b) (nb : nonsquare b)
    (ht : 0<θ) (ns : nonsquare θ) : ProjectiveWeak b θ ↔ EllipticFibre b θ :=
  (projective_iff_normalized b θ).trans (weak_iff_elliptic b θ hb nb ht ns)

/-- At a square second coefficient the two equal endpoints suffice. -/
theorem square_coefficient (b q : Rat) : ProjectiveWeak b (q^2) :=
  (projective_iff_normalized b (q^2)).mpr ⟨none,none,q,by simp [eval]⟩

/-- Removing the sign and reciprocal symmetries selects one real half of the conic. -/
theorem positive_parameter (b θ : Rat) (ht : 0<θ) (ns : nonsquare θ) :
    EllipticFibre b θ ↔ ∃ u l X Y w : Rat, 0<u ∧ θ<u^2 ∧
      (u^2-θ)*l=2*(u^2+θ) ∧ w≠0 ∧ X=(-3*b)*w^2 ∧ Y^2=cubic l X := by
  constructor
  · rintro ⟨u,l,X,Y,w,nu,rel,nw,hX,hY⟩
    obtain ⟨v,vpos,vsq⟩ : ∃ v : Rat, 0<v ∧ v^2=u^2 := by
      by_cases hp : 0<u
      · exact ⟨u,hp,rfl⟩
      · exact ⟨-u,by grind,by grobner⟩
    have relv : (v^2-θ)*l=2*(v^2+θ) := by rw [vsq]; exact rel
    by_cases hp : θ<v^2
    · exact ⟨v,l,X,Y,w,vpos,hp,relv,nw,hX,hY⟩
    · have neq:=ns v
      have hlt : v^2<θ := by grind
      have nv : v≠0 := by grind
      have iv : v*v⁻¹=1 := by grind
      have pos : 0<θ*v⁻¹ := Rat.mul_pos ht (Rat.inv_pos.mpr vpos)
      have pos2 : 0<θ*(v⁻¹)^2 := Rat.mul_pos ht (Rat.pow_pos (Rat.inv_pos.mpr vpos))
      have hscale:=Rat.mul_lt_mul_of_pos_right hlt pos2
      have eq1 : v^2*(θ*(v⁻¹)^2)=θ := by grobner
      have eq2 : θ*(θ*(v⁻¹)^2)=(θ*v⁻¹)^2 := by grobner
      rw [eq1,eq2] at hscale
      have recp:=reciprocal_fibre θ v l nv relv
      exact ⟨θ*v⁻¹,-l,X,Y,w,pos,hscale,recp.1,nw,hX,(recp.2.1 X).symm ▸ hY⟩
  · rintro ⟨u,l,X,Y,w,pos,_,eq,nw,hX,hY⟩
    exact ⟨u,l,X,Y,w,by grind,eq,nw,hX,hY⟩

#print axioms product_identity
#print axioms weak_to_hyperbola
#print axioms hyperbola_to_weak
#print axioms curve_identity
#print axioms hyperbola_to_elliptic
#print axioms elliptic_to_hyperbola
#print axioms projective_iff_elliptic
#print axioms square_coefficient
#print axioms reciprocal_fibre
#print axioms positive_parameter
end CompanionDescent
