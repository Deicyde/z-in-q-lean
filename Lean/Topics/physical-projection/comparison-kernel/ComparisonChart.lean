import Std
import QuadraticPivots

namespace PhysicalProjection.Comparison

section Polynomial
variable {R : Type u} [Lean.Grind.CommRing R]

def base (D c r : R) := c + D*r^2
def chart (D c b r g : R) := c*(r^2+g^2)+D*r^2*g^2+2*b*r*g-1
def first (D c b r g : R) := base D c r * g+b*r
def second (D c b r g : R) := -(base D c g * r)-b*g

/-- The chord determinant with its ordinate column scaled by a. -/
def chord (c b r g I K : R) :=
  r*(-(c*b)*g^3+K)-I*(c*g^3-g)+r^3*(-(c*K)+c*b*g)

theorem square_completions (D c b r g : R) (root : b^2=c^2-D) :
    (first D c b r g)^2-c*(1-D*r^4)=base D c r * chart D c b r g ∧
    (second D c b r g)^2-c*(1-D*g^4)=base D c g * chart D c b r g := by
  unfold first second base chart
  constructor <;> grobner

theorem chord_factor (D c b r g : R) :
    chord c b r g (first D c b r g) (second D c b r g)=c*(r^2-g^2)*chart D c b r g := by
  unfold chord first second base chart
  grobner

theorem reciprocal_row (D c b r g : R) (root : b^2=c^2-D) :
    base D c r*second D c b r g-b*first D c b r g+2*c*(c*r+b*g)=
    -(D*r*chart D c b r g) := by
  unfold first second chart base
  grobner

theorem scalar_row (D c b r g : R) (root : b^2=c^2-D) :
    base D c r*second D c b r g+2*D*r+b*first D c b r g-2*D*b*g*r^2=
    -(D*r*chart D c b r g) := by
  unfold first second chart base
  grobner

theorem zero_fibres (D c b r g : R) :
    (chart D c b 0 g=c*g^2-1 ∧ first D c b 0 g=c*g ∧ second D c b 0 g= -(b*g)) ∧
    (chart D c b r 0=c*r^2-1 ∧ first D c b r 0=b*r ∧ second D c b r 0= -(c*r)) := by
  unfold first second chart base
  repeat' constructor
  all_goals grobner

def Cancellable (x : R) := ∀ y z : R, x*y=x*z → y=z

private theorem cancel_conic {a J x : R} (ha : Cancellable a)
    (e : (a*J)^2-a^2*(1-x)=0) : J^2+x=1 := by
  apply ha
  apply ha
  calc a*(a*(J^2+x)) = ((a*J)^2-a^2*(1-x))+a^2 := by grobner
       _ = a*(a*1) := by rw [e]; grobner

private theorem swap_middle (a d k : R) : d*(a*k)=a*(d*k) := by grobner
private theorem ellipse_other {x y : R} (h : x+y=1) : 1-y=x := by grobner

/-- Only a and c+D*r² must cancel, including at both identity fibres. -/
theorem chart_iff {D c b a r g J k : R} (hc : c=a^2) (root : b^2=c^2-D)
    (ha : Cancellable a) (hd : Cancellable (base D c r)) :
    (J^2+D*r^4=1 ∧ a*J=first D c b r g ∧ base D c r*k=b*J-2*a*(c*r+b*g)) ↔
    (chart D c b r g=0 ∧ a*J=first D c b r g ∧ a*k=second D c b r g) := by
  have sq := (square_completions D c b r g root).1
  have out := reciprocal_row D c b r g root
  constructor
  · rintro ⟨conic,input,old⟩
    have hJ := ellipse_other conic
    have tc : chart D c b r g=0 := by
      apply hd
      calc base D c r * chart D c b r g = first D c b r g ^2-c*(1-D*r^4) := sq.symm
           _ = base D c r * 0 := by rw [←input,hJ,hc]; grobner
    refine ⟨tc,input, hd _ _ ?_⟩
    rw [tc,←input] at out
    have f : base D c r*second D c b r g=b*(a*J)-2*c*(c*r+b*g) := by
      clear sq conic hJ old hc root input tc hd ha; grobner
    rw [f,swap_middle a (base D c r) k,old,hc]
    grobner
  · rintro ⟨tc,input,output⟩
    refine ⟨cancel_conic ha ?_,input,ha _ _ ?_⟩
    · calc (a*J)^2-a^2*(1-D*r^4)=first D c b r g ^2-c*(1-D*r^4) := by rw [input,←hc]
           _ = 0 := by rw [sq,tc]; grobner
    · rw [←output,←input,tc] at out
      have f : base D c r*(a*k)=b*(a*J)-2*c*(c*r+b*g) := by
        clear sq input output hc root tc ha hd; grobner
      rw [(swap_middle a (base D c r) k).symm,f,hc]
      grobner

theorem difference_conic {D c b a r g k : R} (hc : c=a^2) (root : b^2=c^2-D)
    (ha : Cancellable a) (tc : chart D c b r g=0) (output : a*k=second D c b r g) :
    k^2+D*g^4=1 := by
  have sq := (square_completions D c b r g root).2
  apply cancel_conic ha
  calc (a*k)^2-a^2*(1-D*g^4)=second D c b r g ^2-c*(1-D*g^4) := by rw [output,←hc]
       _ = 0 := by rw [sq,tc]; grobner
end Polynomial

abbrev Q2 := Rat × Rat
def times (x y : Q2) : Q2 := (x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)
def sq (x : Q2) := times x x
def norm (x : Q2) := x.1^2-2*x.2^2
def delta : Q2 := (3,-1)
def D2 : Q2 := (11,-6)
def one : Q2 := (1,0)
def conic (r J : Q2) := ((sq J).1+(times D2 (sq (sq r))).1,
                           (sq J).2+(times D2 (sq (sq r))).2)=one

theorem norm_product (x y : Q2) : norm (times x y)=norm x * norm y := by
  dsimp [norm,times]; grobner

private theorem nonneg_square (x : Rat) : 0≤x^2 := by
  rcases Rat.nonneg_total x with h|h
  · exact Rat.pow_nonneg h
  · have n := Rat.mul_nonneg h h
    rwa [show -x*(-x)=x^2 by grobner] at n

private theorem nonzero_norm {r : Q2} (nz : r≠(0,0)) : norm r≠0 := by
  intro h
  obtain ⟨a,b⟩ := (CircuitTransport.Quadratic.norm_zero_iff r.1 r.2).mp h
  exact nz (Prod.ext a b)

theorem delta_square (r : Q2) : times D2 (sq (sq r)) = sq (times delta (sq r)) := by
  apply Prod.ext <;> dsimp [times,sq,delta,D2] <;> grobner

/-- For nonzero r, ((3-√2)r²)² has nonzero √2-coordinate. -/
theorem fourth_imaginary_nonzero {r : Q2} (hr : r≠(0,0)) : (times D2 (sq (sq r))).2≠0 := by
  let v := times delta (sq r)
  let n := norm r
  have normv : v.1^2-2*v.2^2=7*n^2 := by
    change norm v=7*n^2
    dsimp only [v,sq,n]
    rw [norm_product,norm_product,show norm delta=7 by unfold norm delta; grobner]
    grobner
  have nz : n≠0 := nonzero_norm hr
  rw [delta_square]
  intro zero
  have vi : v.1*v.2=0 := by
    change v.1*v.2+v.2*v.1=0 at zero
    grobner
  rcases Rat.mul_eq_zero.mp vi with ha | hb
  · rw [ha] at normv
    have npos := nonneg_square n
    have vpos := nonneg_square v.2
    have n0 : n^2=0 := by grind
    have zero' : n*n=0 := by grobner
    exact (Rat.mul_eq_zero.mp zero').elim nz nz
  · rw [hb] at normv
    let t := v.1/n
    have clear : t*n=v.1 := Rat.div_mul_cancel nz
    have square : (t^2-7)*(n*n)=0 := by
      calc (t^2-7)*(n*n)=(t*n)^2-7*n^2 := by grobner
           _ = 0 := by rw [clear]; grobner
    have van := (Rat.mul_eq_zero.mp square).resolve_right (fun bad => (Rat.mul_eq_zero.mp bad).elim nz nz)
    exact (CircuitTransport.Quadratic.no_square_in_gap (n:=7) (k:=2) (by decide) (by decide) t) (by grobner)

theorem ordinate_real_nonzero {r J : Q2} (onChart : conic r J) : J.1≠0 := by
  intro zero
  by_cases hr : r=(0,0)
  · have re := congrArg Prod.fst onChart
    rw [hr] at re
    dsimp [one,sq,D2,times] at re
    rw [zero] at re
    exact CircuitTransport.Quadratic.two_nonsquare (2*J.2) (by grobner)
  · have im := congrArg Prod.snd onChart
    change J.1*J.2+J.2*J.1+(times D2 (sq (sq r))).2=0 at im
    rw [zero] at im
    exact fourth_imaginary_nonzero hr (by clear onChart zero; grobner)

theorem ordinate_nonzero {r J : Q2} (onChart : conic r J) : J≠(0,0) := by
  intro zero
  exact ordinate_real_nonzero onChart (congrArg Prod.fst zero)

#print axioms square_completions
#print axioms chord_factor
#print axioms reciprocal_row
#print axioms scalar_row
#print axioms zero_fibres
#print axioms chart_iff
#print axioms difference_conic
#print axioms norm_product
#print axioms delta_square
#print axioms fourth_imaginary_nonzero
#print axioms ordinate_real_nonzero
#print axioms ordinate_nonzero

end PhysicalProjection.Comparison
