import PhysicalPrimitive
import ProjectivePairs

namespace EllipticHeight.Primitive
open QuadraticInt ProjectionFibres ProjectionFibres.Actual
open PhysicalProjection.Comparison (Q2)

/-- Two integral presentations of one finite abscissa satisfy the projective
cross identity. Neither presentation needs to be reduced for this lemma. -/
theorem representation_cross {z : Q2} {a b c d : R}
    (left : represents z a b) (right : represents z c d) : mul a d=mul c b := by
  apply rational_injective
  rw [rational_mul,rational_mul,←left.2,←right.2]
  exact fraction_exchange z (rational b) (rational d)

/-- Replace any raw iterate of any primitive integral weighted chart with
any other primitive pair at the same projective point. -/
theorem chart_iterate_norm {a b c u v : R} (pr : coprime a b) (weighted : chart a b c)
    (n : Nat) (uv : coprime u v)
    (cross : mul (iterate n (sq a) (sq b)).1 v=mul u (iterate n (sq a) (sq b)).2) :
    (norm (iterate n (sq a) (sq b)).1).natAbs=(norm u).natAbs :=
  primitive_norm_eq (chart_iterate pr weighted n) uv cross

/-- Both the starting and the final representatives may be chosen independently.
The finite signed chart identifies the starting abscissa. The only projective
cross identity supplied to this theorem identifies the final abscissa. -/
theorem signed_iterate_norm {h j : Q2} {a b x y u v : R}
    (root : PhysicalProjection.RootOrdinate.root h j)
    (frac : represents h a b) (ab : coprime a b)
    (source : represents (PhysicalProjection.Comparison.sq h) x y) (xy : coprime x y)
    (n : Nat) (uv : coprime u v)
    (cross : mul (iterate n x y).1 v=mul u (iterate n x y).2) :
    (norm (iterate n x y).1).natAbs=(norm u).natAbs := by
  obtain ⟨c,weighted⟩:=clear_chart root frac
  have s:=start ab (dyadic_denominator weighted) (no_seven_numerator ab weighted)
  have chosen:=state_of_cross s xy (representation_cross (square_fraction frac) source)
  exact primitive_norm_eq (iterate_state n chosen).1 uv cross

theorem signed_double_norm {h j : Q2} {a b x y u v : R}
    (root : PhysicalProjection.RootOrdinate.root h j)
    (frac : represents h a b) (ab : coprime a b)
    (source : represents (PhysicalProjection.Comparison.sq h) x y) (xy : coprime x y)
    (uv : coprime u v) (cross : mul (top x y) v=mul u (bottom x y)) :
    (norm (top x y)).natAbs=(norm u).natAbs :=
  signed_iterate_norm root frac ab source xy 1 uv cross

/-- Numerator norm for any primitive representative of the raw projective
iterate of a stored signed slot. -/
theorem physical_iterate_norm (s : Fin 80→Rat) (zero : Binding.V s 9813=0) (i : Fin 4)
    {a b u v : R} (frac : represents (Labels.rootH (decoded s) i) a b) (ab : coprime a b)
    (n : Nat) (uv : coprime u v)
    (cross : mul (iterate n (sq a) (sq b)).1 v=mul u (iterate n (sq a) (sq b)).2) :
    (norm (iterate n (sq a) (sq b)).1).natAbs=(norm u).natAbs :=
  primitive_norm_eq (physical_iterate s zero i frac ab n) uv cross

/-- On the literal circuit, both input and output pairs may use their own
primitive coordinates. The doubling cross identity determines the output mass. -/
theorem physical_double_norm (s : Fin 80→Rat) (zero : Binding.V s 9813=0) (i : Fin 4)
    {a b x y u v : R} (frac : represents (Labels.rootH (decoded s) i) a b) (ab : coprime a b)
    (source : represents (roots (decoded s) i) x y) (xy : coprime x y) (uv : coprime u v)
    (cross : mul (top x y) v=mul u (bottom x y)) :
    (norm (top x y)).natAbs=(norm u).natAbs := by
  obtain ⟨dy,_,seven⟩:=actual_bad_primes s zero i frac ab
  have state:=state_of_cross (start ab dy seven) xy
    (representation_cross (physical_square_representation s i frac) source)
  exact primitive_norm_eq (step state).1 uv cross

#print axioms representation_cross
#print axioms chart_iterate_norm
#print axioms signed_iterate_norm
#print axioms signed_double_norm
#print axioms physical_iterate_norm
#print axioms physical_double_norm
end EllipticHeight.Primitive
