import Std

namespace AnchorCollision.Translation
open Lean.Grind
variable {K : Type} [Field K]

private theorem prod_ne {a b : K} (aa:a≠0) (bb:b≠0) : a*b≠0 :=
  fun h => (Field.of_mul_eq_zero h).elim aa bb

private theorem square_ne {x : K} (nz:x≠0) : x^2≠0 := by
  rw [show x^2=x*x by grobner]
  exact prod_ne nz nz

private theorem cancel {u v k : K} (hk:k≠0) (e:u*k=v*k) : u=v := by
  have z : (u-v)*k=0 := by grobner
  have := (Field.of_mul_eq_zero z).resolve_right hk
  grobner

/-- Secant abscissa for Q-P, with the *signed* roots of the two abscissas. -/
theorem chord {a b h j D g slope x : K}
    (base : b^2=a^4-D) (root : j^2=h^4-D)
    (den : a^2*h^2+D≠0) (mixed : g*(a^2*h^2+D)=a*j-b*h)
    (distinct : h^2-a^2≠0) (line : slope*(h^2-a^2)=h*j+a*b)
    (abscissa : x=slope^2-h^2-a^2) : x*g^2=1 := by
  have factor : (a*j-b*h)*(a*j+b*h)=(h^2-a^2)*(a^2*h^2+D) := by
    calc _ = a^2*j^2-b^2*h^2 := by grobner
         _ = _ := by rw [root,base];grobner
  have u : g*(a*j+b*h)=h^2-a^2 := by
    apply cancel den
    calc g*(a*j+b*h)*(a^2*h^2+D)=(g*(a^2*h^2+D))*(a*j+b*h) := by grobner
         _ = _ := by rw [mixed,factor]
  have wing : j^2-b^2=(h^2-a^2)*(h^2+a^2) := by rw [root,base];grobner
  have q : x*(h^2-a^2)^2=(a*j+b*h)^2 := by
    calc x*(h^2-a^2)^2=(slope*(h^2-a^2))^2-(h^2+a^2)*(h^2-a^2)^2 := by rw [abscissa];grobner
         _ = (h*j+a*b)^2-(h^2+a^2)*(h^2-a^2)^2 := by rw [line]
         _ = (a*j+b*h)^2+(h^2-a^2)*((j^2-b^2)-(h^2-a^2)*(h^2+a^2)) := by grobner
         _ = _ := by rw [wing];grobner
  apply cancel (square_ne distinct)
  calc x*g^2*(h^2-a^2)^2 = g^2*(x*(h^2-a^2)^2) := by grobner
       _ = (g*(a*j+b*h))^2 := by rw [q];grobner
       _ = _ := by rw [u];grobner

/-- At Q=-P the ordinate changes sign and x(Q-P) is the doubling abscissa. -/
theorem tangent {a b h j D g x : K}
    (base : b^2=a^4-D) (root : j^2=h^4-D) (same : h^2=a^2)
    (negative : h*j= -(a*b))
    (mixed : g*(a^2*h^2+D)=a*j-b*h)
    (doubling : x*(2*(a*b))^2=(a^4+D)^2) (dy : 2*(a*b)≠0) : x*g^2=1 := by
  have d : a^2*h^2+D=a^4+D := by rw [same];grobner
  rw [d] at mixed
  have n : (a*j-b*h)^2=4*(a*b)^2 := by grobner
  have ng : g^2*(a^4+D)^2=4*(a*b)^2 := by
    calc _ = (g*(a^4+D))^2 := by grobner
         _ = _ := by rw [mixed,n]
  apply cancel (square_ne dy)
  calc x*g^2*(2*(a*b))^2=g^2*(x*(2*(a*b))^2) := by grobner
       _ = 4*(a*b)^2 := by rw [doubling,ng]
       _ = _ := by grobner

#print axioms chord
#print axioms tangent
end AnchorCollision.Translation
