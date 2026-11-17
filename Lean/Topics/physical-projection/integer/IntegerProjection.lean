import IntegerProgram
import MarkedProjection
namespace Physical130
open ZeroInput.Sparse CircuitTransport PhysicalProjection ProjectionDescent

theorem exists_pointwise (g m : Bool) (a : Rat) :
    (∃y : Fin 130→Rat,finiteLift y 1=a ∧ (program g).eval m (finiteLift y)=0) ↔
    ∃y : Fin 130→Rat,finiteLift y 1=a ∧ chart g m y := by
  constructor <;> rintro ⟨y,hx,h⟩
  · exact ⟨y,hx,(pointwise g m y).mp h⟩
  · exact ⟨y,hx,(pointwise g m y).mpr h⟩

theorem ordinary_projection (g : Bool) (a : Rat) : RowsProject 226 (parentRows g) a ↔
    ∃ y : Fin 130→Rat, finiteLift y 1=a ∧ (program g).eval false (finiteLift y)=0 :=
  (PhysicalProjection.ordinary_projection g a).trans (exists_pointwise g false a).symm

theorem marked_projection (g : Bool) (a : Rat) :
    (∃ y : Fin 130→Rat, finiteLift y 1=a ∧ (program g).eval true (finiteLift y)=0) ↔ RowsProject 226 (parentRows g) a ∨ a=0 :=
  (exists_pointwise g true a).trans (PhysicalProjection.marked_projection g a)

theorem ordinary_polynomial (g : Bool) (a : Rat) :
    (∃x : Fin 226→Rat,finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion (parentRows g))=0) ↔
    ∃y : Fin 130→Rat,finiteLift y 1=a ∧ valueAt (program g).nodes (finiteLift y) (program g).ordinary=0 :=
  (PhysicalProjection.ordinary_polynomial g a).trans (exists_pointwise g false a).symm

theorem marked_polynomial (g : Bool) (a : Rat) :
    (∃y : Fin 130→Rat,finiteLift y 1=a ∧ valueAt (program g).nodes (finiteLift y) (program g).marked=0) ↔
    (∃x : Fin 226→Rat,finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion (parentRows g))=0) ∨ a=0 :=
  (exists_pointwise g true a).trans (PhysicalProjection.marked_polynomial g a)

theorem designated_mark (g : Bool) :
    finiteLift designated 1=0 ∧ valueAt (program g).nodes (finiteLift designated) (program g).marked=0 :=
  ⟨(PhysicalProjection.designated_zero g).1,(pointwise g true designated).mpr (PhysicalProjection.designated_zero g).2⟩

namespace Gate510
abbrev tape := program false
abbrev parent := parentRows false
theorem ordinary (a : Rat) :
    (∃x : Fin 226→Rat,finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion parent)=0) ↔
    ∃y : Fin 130→Rat,finiteLift y 1=a ∧ valueAt tape.nodes (finiteLift y) tape.ordinary=0 := ordinary_polynomial false a
theorem marked (a : Rat) :
    (∃y : Fin 130→Rat,finiteLift y 1=a ∧ valueAt tape.nodes (finiteLift y) tape.marked=0) ↔
    (∃x : Fin 226→Rat,finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion parent)=0) ∨ a=0 := marked_polynomial false a
theorem mark_at_zero : finiteLift designated 1=0 ∧ valueAt tape.nodes (finiteLift designated) tape.marked=0 := designated_mark false
end Gate510

namespace Gate67830
abbrev tape := program true
abbrev parent := parentRows true
theorem ordinary (a : Rat) :
    (∃x : Fin 226→Rat,finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion parent)=0) ↔
    ∃y : Fin 130→Rat,finiteLift y 1=a ∧ valueAt tape.nodes (finiteLift y) tape.ordinary=0 := ordinary_polynomial true a
theorem marked (a : Rat) :
    (∃y : Fin 130→Rat,finiteLift y 1=a ∧ valueAt tape.nodes (finiteLift y) tape.marked=0) ↔
    (∃x : Fin 226→Rat,finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion parent)=0) ∨ a=0 := marked_polynomial true a
theorem mark_at_zero : finiteLift designated 1=0 ∧ valueAt tape.nodes (finiteLift designated) tape.marked=0 := designated_mark true
end Gate67830
end Physical130
