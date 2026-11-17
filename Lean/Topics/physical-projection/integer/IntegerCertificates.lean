import IntegerProgram
namespace Physical130
open ZeroInput.Sparse ProjectionDescent CircuitTransport Triangular.Data PhysicalProjection

def book (g : Bool) := Book.make (Seeds.nodes g)
def detectorsAt (g : Bool) := detTable (book g) g
def store (g : Bool) := cells (book g) (ps g) (middleBase (book g) (detectorsAt g))
def envAt (g : Bool) := select (middleBase (book g) (detectorsAt g)) (store g)
def matrixAt (g : Bool) := makeCram (book g) (detectorsAt g) (store g)

theorem every_coordinate (g : Bool) (y : Fin 130→Rat) (i : Nat) :
    0<(envAt g i).den ∧ (envAt g i).num.value (book g) (finiteLift y)=(envAt g i).den*middle g y i :=
  middle_along (book g) g y i

theorem every_guard (g : Bool) (y : Fin 130→Rat) (k : DBlock) :
    DetCorrect (book g) (finiteLift y) k ((detectorsAt g).atBlock k) (preliminary g y) (seed130 y) :=
  table_correct (book g) g y k

theorem every_matrix (g : Bool) (y : Fin 130→Rat) (k : PPair) :
    CramerCorrect (book g) (finiteLift y) (chartPoint g y) k ((matrixAt g).atPair k) ∧
    ((matrixAt g).atPair k).d.value (book g) (finiteLift y)=
      ((line (book g) (envAt g) k.slot k.f).den:Rat)*((line (book g) (envAt g) k.slot k.g).den:Rat)*k.det (middle g y) := by
  simp only [matrixAt,makeCram_at]
  exact ⟨cramer_correct y k (every_coordinate g y),cramer_scale y k (every_coordinate g y)⟩

theorem every_signed_row (g : Bool) (y : Fin 130→Rat) (r : Nat×Polynomial) (h : r∈activeRows g) :
    rowFactor (book g) (finiteLift y) (envAt g) (matrixAt g) r≠0 ∧
    (numerator (book g) (envAt g) (matrixAt g) r).value (book g) (finiteLift y)=
      rowFactor (book g) (finiteLift y) (envAt g) (matrixAt g) r*value (chartPoint g y) r.2 :=
  every_residual y (every_coordinate g y) _ (fun k=>(every_matrix g y k).1) r h

end Physical130
