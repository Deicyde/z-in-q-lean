import PrimitiveDouble
import Duplication
import ComparisonChart

namespace EllipticHeight.Primitive
open QuadraticInt

theorem square_product (z w : PhysicalProjection.Comparison.Q2) :
    PhysicalProjection.Comparison.times (PhysicalProjection.Comparison.sq z)
        (PhysicalProjection.Comparison.sq w)=
      PhysicalProjection.Comparison.sq (PhysicalProjection.Comparison.times z w) := by
  apply Prod.ext <;> dsimp [PhysicalProjection.Comparison.sq,PhysicalProjection.Comparison.times] <;> grobner

theorem square_nonzero {b : R} (nonzero : b≠(0,0)) : sq b≠(0,0) := by
  intro zero
  have v:=congrArg Prod.fst zero
  change b.1*b.1+2*b.2*b.2=0 at v
  have p : 0≤b.1*b.1 := by have s:=Int.sq_nonnneg b.1; grind
  have q : 0≤b.2*b.2 := by have s:=Int.sq_nonnneg b.2; grind
  have t : 2*b.2*b.2=2*(b.2*b.2) := by grobner
  have x:=Int.mul_eq_zero.mp (by omega : b.1*b.1=0)
  have z:=Int.mul_eq_zero.mp (by omega : b.2*b.2=0)
  exact nonzero (Prod.ext (x.elim id id) (z.elim id id))

def asQuad (x : R) : Duplication.Quad := ⟨x.1,x.2⟩

/-- The integral recurrences use the identical numerator and denominator
from the physical curve's duplication-height proof. -/
theorem same_raw (x y : R) :
    asQuad (top x y)=Duplication.firstK (asQuad x) (asQuad y) ∧
    asQuad (bottom x y)=Duplication.secondK (asQuad x) (asQuad y) := by
  exact ⟨rfl,rfl⟩

#print axioms same_raw
end EllipticHeight.Primitive
