import ResidueInterface

namespace IndependentIndices
open Lean.Grind
attribute [local instance] Semiring.natCast Ring.intCast

/-- The literal basis 1,√2 over a finite residue ring; its conjugation has already been
applied to the alternate ratio when the local cross congruence is supplied. -/
def quadraticMul {R : Type} [CommRing R] (x y : R×R) : R×R :=
  (x.1*y.1+2*x.2*y.2,x.1*y.2+x.2*y.1)

def quadraticSub {R : Type} [CommRing R] (x y : R×R) : R×R := (x.1-y.1,x.2-y.2)

def quadraticLucas {R : Type} [CommRing R] (a t b : R×R) : R×R :=
  let d:=quadraticSub a (2,0)
  let term:=quadraticMul (quadraticMul (quadraticMul a d) t) b
  let square:=quadraticMul (quadraticMul d d) (quadraticMul b b)
  let diff:=quadraticSub (quadraticMul t t) term
  (diff.1+square.1-1, diff.2+square.2)

theorem quadratic_lucas_at_integers {R : Type} [CommRing R] (a t b : R) :
    quadraticLucas (a,0) (t,0) (b,0)=(lucas a t b,0) := by
  unfold quadraticLucas quadraticSub quadraticMul lucas
  apply Prod.ext <;> dsimp <;> grobner

structure QuadraticLog (R : Type) [CommRing R] (m n : Int) where
  real : LogRow R m n
  imaginary : LogRow R m 0

def QuadraticLog.value {R : Type} [CommRing R] {m n} (r : QuadraticLog R m n) : R×R :=
  (r.real.primary,r.imaginary.primary)

theorem QuadraticLog.value_eq {R : Type} [CommRing R] {N : Nat} [IsCharP R N] {m n}
    (r : QuadraticLog R m n) (odd : N%2=1) : r.value=((n:R),0) := by
  have im:=r.imaginary.label odd
  simp only [Ring.intCast_zero] at im
  exact Prod.ext (r.real.label odd) im

/-- A concrete coordinate calculation for the inert residue algebra
(Z/p^k Z)[rho]/(rho²−2). The detector may be given as a pair equality. -/
theorem quadratic_finite_place (p : Nat) [NeZero (p^10)] [NeZero (p^40)] (odd : p%2=1)
    {m : Int} {ns : Labels} {B : Rat}
    (l₁ : QuadraticLog (Fin (p^10)) m ns.n₁)
    (l₂ : QuadraticLog (Fin (p^40)) m ns.n₂)
    (l₃ : QuadraticLog (Fin (p^40)) m ns.n₃)
    (l₄ : QuadraticLog (Fin (p^40)) m ns.n₄)
    (detector : ((B.den:Fin (p^10))*l₁.value.1,(B.den:Fin (p^10))*l₁.value.2)=((B.num:Fin (p^10)),0))
    (test : quadraticLucas l₂.value l₃.value l₄.value=(0,0)) : Defects p ns B ∧ B.den.Coprime (p^10) := by
  have e:=odd_power p 40 odd
  rw [l₂.value_eq e,l₃.value_eq e,l₄.value_eq e,quadratic_lucas_at_integers] at test
  apply finite_place p odd (m:=m)
  refine ⟨l₁.real,l₂.real,l₃.real,l₄.real,congrArg Prod.fst detector,?_⟩
  rw [l₂.real.label e,l₃.real.label e,l₄.real.label e]
  exact congrArg Prod.fst test

end IndependentIndices
