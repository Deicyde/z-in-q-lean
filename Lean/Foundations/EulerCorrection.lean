module

public import Std

@[expose] public section

namespace EulerCorrection

open Lean.Grind

/-- Product of the two local Frobenius factors after clearing q². -/
theorem local_factors {R : Type} [CommRing R] (q a z w : R) (hw : z*w=1) :
    (q+z^2-a*z)*(q+w^2-a*w) =
      q*(a-z-w)^2+(q-1)*(q-1-a*(a-z-w)) := by grobner

/-- The binary selector takes its two prescribed values without sign idempotents. -/
theorem selector {R : Type} [CommRing R] (v : R) :
    1+(1+(1:R))*v=1+2*v ∧ 1+(1+(-1:R))*v=1 := by
  constructor <;> grobner

/-- At an inactive sign of trace 2ε the horizontal factor has a double zero. -/
theorem central_factor {R : Type} [CommRing R] (t w ε : R) (h : (1+t)*w=1) :
    (1+t)*(2*ε-ε*((1+t)+w)) = -ε*t^2 := by grobner

/-- Trace of A U(4i) L(8j), in the basis fixed by complex conjugation. -/
theorem shear_trace {R : Type} [CommRing R] (a b c d i j : R) :
    (a+8*j*(4*i*a+b))+(4*i*c+d) = (a+d)+8*j*b+4*i*(c+8*j*a) := by grobner

/-- A progression in which either the signed trace or the point count is 0 modulo 64. -/
theorem sharp_progression (q a : Int) (hq : (q-97)%192=0)
    (h : (q+1-a)%32=0) : (a-2)%32=0 ∧ ((a-2)%64=0 ∨ (q+1-a)%64=0) := by omega

/-- The affine denominator used for the reciprocal of x(H−P) equals d² f. -/
theorem chart_denominator {K : Type} [CommRing K] (c x D f : K) (h : x*f=1) :
    (c*x+D)^2*f = c^2*x+2*c*D+D^2*f := by grobner

/-- Eliminating v is reversible on the original open chart. -/
theorem chart_abscissa {K : Type} [Field K] (d v N F f : K)
    (hd : d ≠ 0) (hv : d*v=N) : F*f=v^2 ↔ F*(d^2*f)=N^2 := by
  have hi := Field.mul_inv_cancel hd
  constructor <;> intro h <;> grobner

/-- The old and new logarithm equations differ by a nonzero scalar on that chart. -/
theorem chart_logarithm {K : Type} [Field K] (u t a B N A L V : K)
    (hu : u ≠ 0) (ha : a ≠ 0) (ht : u*t= -a*B) (hN : u*N=A) :
    t*L+a*N*V=0 ↔ B*L=A*V := by
  have iu := Field.mul_inv_cancel hu
  have ia := Field.mul_inv_cancel ha
  constructor <;> intro h <;> grobner

#print axioms local_factors
#print axioms selector
#print axioms central_factor
#print axioms shear_trace
#print axioms sharp_progression
#print axioms chart_denominator
#print axioms chart_abscissa
#print axioms chart_logarithm
end EulerCorrection
