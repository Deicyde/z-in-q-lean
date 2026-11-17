import Certificates
open ZeroInput.Sparse
namespace CircuitTransport

namespace Gate510
abbrev code := published false
abbrev rows := source false

theorem ordinary (a : Rat) :
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ↔
    (∃ y : Fin 153→Rat, finiteLift y 1=a ∧ valueAt code.nodes (finiteLift y) code.ordinary=0) :=
  ordinary_polynomial false a

theorem marked (a : Rat) :
    (∃ y : Fin 153→Rat, finiteLift y 1=a ∧ valueAt code.nodes (finiteLift y) code.marked=0) ↔
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ∨ a=0 :=
  marked_polynomial false a

theorem mark_at_zero : finiteLift designated 1=0 ∧ valueAt code.nodes (finiteLift designated) code.marked=0 := designated_zero false
end Gate510

namespace Gate67830
abbrev code := published true
abbrev rows := source true

theorem ordinary (a : Rat) :
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ↔
    (∃ y : Fin 153→Rat, finiteLift y 1=a ∧ valueAt code.nodes (finiteLift y) code.ordinary=0) :=
  ordinary_polynomial true a

theorem marked (a : Rat) :
    (∃ y : Fin 153→Rat, finiteLift y 1=a ∧ valueAt code.nodes (finiteLift y) code.marked=0) ↔
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ∨ a=0 :=
  marked_polynomial true a

theorem mark_at_zero : finiteLift designated 1=0 ∧ valueAt code.nodes (finiteLift designated) code.marked=0 := designated_zero true
end Gate67830
end CircuitTransport

#print axioms CircuitTransport.instruction
#print axioms CircuitTransport.reuse_value
#print axioms CircuitTransport.number_value
#print axioms CircuitTransport.combine_value
#print axioms CircuitTransport.plus_value
#print axioms CircuitTransport.times_value
#print axioms CircuitTransport.clear_term_value
#print axioms CircuitTransport.clear_row_value
#print axioms CircuitTransport.pivot_cell_value
#print axioms CircuitTransport.restore_value
#print axioms CircuitTransport.memo_eq
#print axioms CircuitTransport.outputs_zero
#print axioms CircuitTransport.emit_correct
#print axioms CircuitTransport.finish_value
#print axioms CircuitTransport.every_coordinate
#print axioms CircuitTransport.every_row
#print axioms CircuitTransport.pointwise
#print axioms CircuitTransport.designated_zero
#print axioms CircuitTransport.ordinary_projection
#print axioms CircuitTransport.marked_projection
#print axioms CircuitTransport.ordinary_polynomial
#print axioms CircuitTransport.marked_polynomial
#print axioms CircuitTransport.Gate510.ordinary
#print axioms CircuitTransport.Gate510.marked
#print axioms CircuitTransport.Gate510.mark_at_zero
#print axioms CircuitTransport.Gate67830.ordinary
#print axioms CircuitTransport.Gate67830.marked
#print axioms CircuitTransport.Gate67830.mark_at_zero
