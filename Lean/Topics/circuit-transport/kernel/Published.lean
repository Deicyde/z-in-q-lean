import PublishedSeeds
import Compile
import ClosedProof
namespace CircuitTransport
open ZeroInput.Sparse
open Triangular.Data (ps top rest code)

/-- A conventional, executable straight-line program. No assumed output node or scale is used. -/
def published (g : Bool) : Program :=
  let b := Book.make (Seeds.nodes g)
  let r := outputs b (ps g) top (rest g) code
  finish b r.ordinary r.marked

theorem pointwise (g : Bool) (y : Fin 153→Rat) :
    ((published g).eval false (finiteLift y)=0 ↔ Triangular.ordinary (ps g) (top::rest g) code y=0) ∧
    ((published g).eval true (finiteLift y)=0 ↔ Triangular.marked (ps g) top (rest g) code y=0) := by
  let b := Book.make (Seeds.nodes g)
  let r := outputs b (ps g) top (rest g) code
  have eq := finish_value b r.ordinary r.marked (finiteLift y)
  have zero := outputs_zero b (ps g) top (rest g) code (Triangular.Data.good0 g) y
  change ((finish b r.ordinary r.marked).eval false _=0 ↔ _) ∧ ((finish b r.ordinary r.marked).eval true _=0 ↔ _)
  rw [eq.1,eq.2];exact zero

theorem ordinary_projection (g : Bool) (a : Rat) :
    ProjectionDescent.RowsProject 226 (Triangular.parent (ps g) (top::rest g)) a ↔
      ∃ y : Fin 153→Rat, finiteLift y 1=a ∧ (published g).eval false (finiteLift y)=0 := by
  rw [Triangular.Data.ordinary_projection]
  constructor <;> rintro ⟨y,input,h⟩
  · exact ⟨y,input,(pointwise g y).1.mpr h⟩
  · exact ⟨y,input,(pointwise g y).1.mp h⟩

theorem marked_projection (g : Bool) (a : Rat) :
    (∃ y : Fin 153→Rat, finiteLift y 1=a ∧ (published g).eval true (finiteLift y)=0) ↔
      ProjectionDescent.RowsProject 226 (Triangular.parent (ps g) (top::rest g)) a ∨ a=0 := by
  rw [←Triangular.Data.marked_projection]
  constructor <;> rintro ⟨y,input,h⟩
  · exact ⟨y,input,(pointwise g y).2.mp h⟩
  · exact ⟨y,input,(pointwise g y).2.mpr h⟩

end CircuitTransport
#print axioms CircuitTransport.pointwise
#print axioms CircuitTransport.ordinary_projection
#print axioms CircuitTransport.marked_projection
