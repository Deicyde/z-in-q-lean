import RawPrimitive
import ChartDenominators

namespace EllipticHeight.Primitive
open QuadraticInt ProjectionFibres ProjectionFibres.Actual

private theorem root_square (x : Fin 84→Rat) (i : Fin 4) :
    roots x i=PhysicalProjection.Comparison.sq (Labels.rootH x i) := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by omega
  rcases cases with rfl|rfl|rfl|rfl <;> rfl

theorem square_fraction {z : PhysicalProjection.Comparison.Q2} {a b : R}
    (frac : represents z a b) :
    represents (PhysicalProjection.Comparison.sq z) (sq a) (sq b) := by
  obtain ⟨nonzero,eq⟩:=frac
  constructor
  · exact square_nonzero nonzero
  · change PhysicalProjection.Comparison.times (PhysicalProjection.Comparison.sq z)
        (rational (mul b b))=rational (mul a a)
    rw [rational_mul,rational_mul,←eq]
    exact square_product z (rational b)

/-- The fraction being doubled represents the actual squared abscissa in the
decoded 84-wire frame, for each of the four signed slots. -/
theorem physical_square_representation (y : Fin 80→Rat) (i : Fin 4)
    {a b : R} (frac : represents (Labels.rootH (decoded y) i) a b) :
    represents (roots (decoded y) i) (sq a) (sq b) := by
  rw [root_square]
  exact square_fraction frac

/-- On each of the four actual signed charts of a stored 80-coordinate zero,
every raw homogeneous doubling of its square abscissa is primitive in Z[√2]. -/
theorem physical_iterate (y : Fin 80→Rat) (zero : Binding.V y 9813=0) (i : Fin 4)
    {a b : R} (frac : represents (Labels.rootH (decoded y) i) a b)
    (pr : coprime a b) (n : Nat) :
    coprime (iterate n (sq a) (sq b)).1 (iterate n (sq a) (sq b)).2 := by
  obtain ⟨r,_,s⟩:=actual_bad_primes y zero i frac pr
  exact (iterate_state n (start pr r s)).1

/-- Exposed one-step Bézout witnesses at the actual abscissa, without
quotient rings, residue-field hypotheses, or divided output coordinates. -/
theorem physical_double (y : Fin 80→Rat) (zero : Binding.V y 9813=0) (i : Fin 4)
    {a b : R} (frac : represents (Labels.rootH (decoded y) i) a b) (pr : coprime a b) :
    ∃ u v : R,
      plus (mul (top (sq a) (sq b)) u) (mul (bottom (sq a) (sq b)) v)=(1,0) :=
  physical_iterate y zero i frac pr 1

#print axioms physical_iterate
#print axioms physical_double
#print axioms physical_square_representation
end EllipticHeight.Primitive
