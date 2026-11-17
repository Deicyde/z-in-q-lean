import ChordDepth
import SaturationTail

namespace EllipticHeight.Labels
open Lean.Grind CircuitTransport.Saturation
attribute [local instance] Semiring.natCast Ring.intCast

/-- A signed finite root produces a point of the other two-isogenous curve. -/
theorem dual_partner {K : Type} [Field K] {h j D : K} (chart : j^2=h^4-D) :
    let u:=2*(h^2+j)
    (2*h*u)^2=u*(u^2+4*D) ∧ u*(2*(h^2-j))=4*D := by
  dsimp; constructor <;> grobner

/-- A square root of the dual abscissa gives a half with the prescribed ordinate. -/
theorem tangent_half {K : Type} [Field K] [IsCharP K 0] {h j D t : K} (nonzero : D≠0)
    (chart : j^2=h^4-D) (square : t^2=2*(h^2+j)) :
    let a:=h*t+(h^2+j)
    let b:=a*t
    let slope:=h+t
    b≠0 ∧ b^2=a^3-D*a ∧ 2*b*slope=3*a^2-D ∧
      slope^2-2*a=h^2 ∧ slope*(a-h^2)-b=h*j := by
  dsimp
  have h2 : (h*t+(h^2+j))^2-t^2*(h*t+(h^2+j))=D := by grobner
  have a0 : h*t+(h^2+j)≠0 := by intro z; rw [z] at h2; apply nonzero; grobner
  have t0 : t≠0 := by
    intro z; rw [z] at square
    apply nonzero; grobner
  have b0 : (h*t+(h^2+j))*t≠0 := by grind
  exact ⟨b0,by grobner,by grobner,by grobner,by grobner⟩

/-- The unit class has nonsquare negative residue at the unique prime dividing δ. -/
theorem residues_seven (a : Fin 7) : a.val^2%7≠3 ∧ a.val^2%7≠6 := by
  revert a; decide

/-- On y²=X(X²+A X+B), the numerator of X(2S) is a square. -/
theorem shifted_duplication {K : Type} [Field K] {A B x y : K}
    (onCurve : y^2=x*(x^2+A*x+B)) :
    (3*x^2+2*A*x+B)^2-4*y^2*(A+2*x)=(x^2-B)^2 := by grobner

/-- The intercept of a nonvertical chord on the translated curve. -/
theorem shifted_chord {K : Type} [Field K] {A B x z slope b : K}
    (distinct : x≠z)
    (atX : (slope*x+b)^2=x*(x^2+A*x+B))
    (atZ : (slope*z+b)^2=z*(z^2+A*z+B)) :
    x*z*(slope^2-A-x-z)=b^2 := by
  have fac : (x-z)*(x*z*(slope^2-A-x-z)-b^2)=0 := by grobner
  have nz : x-z≠0 := by intro h; apply distinct; grobner
  have right := (Field.of_mul_eq_zero fac).resolve_left nz
  grobner

/-- The unit norm, the square for x−δ and its divisibility by two
determine the division point without an enumeration of integral points. -/
theorem two_translate_saturation {c d w : Int} (unit : c^2-2*d^2= -1)
    (minus : (c-3)^2-2*(d+1)^2= -w^2) (divides : w^2∣4) : c=1 ∧ d=1 := by
  have diff : (c-3)^2-2*(d+1)^2=6-6*c-4*d := by grobner
  have abs : ((w.natAbs^2:Nat):Int)=w^2 := by
    rw [←Int.natAbs_pow]; exact Int.natAbs_of_nonneg (Int.sq_nonnneg w)
  have dn : w.natAbs^2 ∣ 4 := Int.ofNat_dvd.mp (abs ▸ divides)
  have cap := Nat.le_of_dvd (by decide : 0<4) dn
  have even : w.natAbs^2%2=0 := by omega
  have nz : w.natAbs≠0 := by
    intro z; rw [z] at dn
    exact (by decide : ¬ (0:Nat)^2∣4) dn
  have big : 2≤w.natAbs := by
    by_cases one : w.natAbs=1
    · rw [one] at even
      exact False.elim ((by decide : ¬ (1:Nat)^2%2=0) even)
    · omega
  have four:=Nat.pow_le_pow_left big 2
  have ws : w.natAbs^2=4 := by omega
  rw [ws] at abs
  exact unique_coordinates unit (by omega)

/-- Congruence to a marked generator modulo any prescribed even modulus
does not determine its putative odd index in a cyclic group. -/
theorem odd_index_congruence_countermodel (N : Nat) (pos : 0<N) :
    ∃ m : Nat, m%2=1 ∧ 1<m ∧ (2*(N:Int))∣(1-(m:Int)) ∧ ¬ m∣1 := by
  refine ⟨2*N+1,by omega,by omega,⟨-1,by simp; omega⟩,?_⟩
  intro dvd
  have h:=Nat.le_of_dvd (by decide : 0<1) dvd
  omega

#print axioms dual_partner
#print axioms tangent_half
#print axioms residues_seven
#print axioms shifted_duplication
#print axioms shifted_chord
#print axioms two_translate_saturation
#print axioms odd_index_congruence_countermodel
end EllipticHeight.Labels
