import PhysicalZero
import PhysicalSeeds
namespace Physical130
open ZeroInput.Sparse CircuitTransport PhysicalProjection

/-- The emitted integer tape. The checked lowering derives both output indices. -/
def program (g : Bool) : Program :=
  let b:=Book.make (Seeds.nodes g)
  let r:=outputs130 b g
  finish b r.ordinary r.marked

theorem pointwise (g marked : Bool) (y : Fin 130→Rat) :
    (program g).eval marked (finiteLift y)=0 ↔ chart g marked y := by
  let b:=Book.make (Seeds.nodes g)
  let r:=outputs130 b g
  have valid:=finish_value b r.ordinary r.marked (finiteLift y)
  have exactAt:=outputs_chart b g y
  cases marked with
  | false => change (finish b r.ordinary r.marked).eval false _=0 ↔ _;rw [valid.1];exact exactAt.1
  | true => change (finish b r.ordinary r.marked).eval true _=0 ↔ _;rw [valid.2];exact exactAt.2

end Physical130
