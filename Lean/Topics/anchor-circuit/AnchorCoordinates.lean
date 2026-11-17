import PhysicalRootCharts
import AnchorConic

namespace AnchorCircuit
open PhysicalProjection.Comparison PhysicalProjection.RootOrdinate
open StructuralReduction StructuralReduction.Transfer84
open ProjectionFibres.Comparison EllipticHeight.Labels

def H : Rat := 3^592
def J : Rat := 3^883

/-- Denominator and numerator of the translated square-root coordinate over Q(√2). -/
def divisor (h : Q2) : Q2 :=
  let s := sq (times (-1,7/4) h)
  (s.1+11,s.2-6)

def numerator (h j : Q2) : Q2 :=
  sub (times (-1,7/4) j) (times (39/8,-9/2) h)

/-- Coefficient of √2 after division in Q(√2). -/
def shifted (h j : Q2) : Rat :=
  (times (numerator h j) (conjugate (divisor h))).2 / norm (divisor h)

def productThree (x : Fin 84 → Rat) : Q2 :=
  times (times (sq (rootH x 0)) (sq (rootH x 1))) (sq (rootH x 2))

def productReal (x : Fin 84 → Rat) : Rat :=
  (times (productThree x) (sq (rootH x 3))).1

def parameter (x : Fin 84 → Rat) : Rat :=
  shifted (rootH x 1) (rootJ x 1) / 3^1475 + 4096 * productReal x

def conic (u v w t : Rat) : Rat := u^2 + 6*v^2 - 2*w^2 - 3*t^2 + 2

private theorem square_nonneg (r : Rat) : 0≤r^2 := by
  rcases Rat.nonneg_total r with h|h
  · exact Rat.pow_nonneg h
  · have n := Rat.mul_nonneg h h
    rwa [show -r*(-r)=r^2 by grobner] at n

/-- The mixed term in N(s²+(3−√2)²) is the trace of ((3+√2)s)². -/
theorem norm_positive (h : Q2) : 0 < norm (divisor h) := by
  let s := times (-1,7/4) h
  have identity : norm (divisor h) =
      (s.1^2-2*s.2^2)^2 + 2*(3*s.1+2*s.2)^2 + 4*(s.1+3*s.2)^2 + 49 := by
    dsimp [divisor,norm,sq,times,s]
    grobner
  rw [identity]
  have h₁ := square_nonneg (s.1^2-2*s.2^2)
  have h₂ := square_nonneg (3*s.1+2*s.2)
  have h₃ := square_nonneg (s.1+3*s.2)
  grind

theorem H_ne : H ≠ 0 := by decide +kernel
theorem J_ne : J ≠ 0 := by decide +kernel
theorem scale_exponents : H*J=(3:Rat)^1475 := by decide +kernel

/-- Homogenization of the conic along its four affine coordinates. -/
theorem homogeneous (d k u v w a t : Rat) (hk : k≠0) (ht : t*(d*k)=a) :
    4*((9*d*u)^2+6*(9*d*v)^2-2*(d*(w+k))^2-3*a^2+2*(d*k)^2) =
    4*(d*k)^2 * conic (9*u/k) (9*v/k) (1+w/k) t := by
  have h₁ := Rat.div_mul_cancel (a:=9*u) hk
  have h₂ := Rat.div_mul_cancel (a:=9*v) hk
  have h₃ := Rat.div_mul_cancel (a:=w) hk
  unfold conic
  grobner

end AnchorCircuit
