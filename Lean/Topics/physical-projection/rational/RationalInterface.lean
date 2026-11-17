import MarkedProjection
namespace PhysicalProjection
open ZeroInput.Sparse ProjectionDescent

namespace Gate510
abbrev rows := parentRows false
theorem ordinary (a : Rat) :
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ↔
      ∃ y : Fin 130→Rat, finiteLift y 1=a ∧ chart false false y := ordinary_polynomial false a

theorem marked (a : Rat) :
    (∃ y : Fin 130→Rat, finiteLift y 1=a ∧ chart false true y) ↔
      (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ∨ a=0 := marked_polynomial false a
end Gate510

namespace Gate67830
abbrev rows := parentRows true
theorem ordinary (a : Rat) :
    (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ↔
      ∃ y : Fin 130→Rat, finiteLift y 1=a ∧ chart true false y := ordinary_polynomial true a

theorem marked (a : Rat) :
    (∃ y : Fin 130→Rat, finiteLift y 1=a ∧ chart true true y) ↔
      (∃ x : Fin 226→Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ∨ a=0 := marked_polynomial true a
end Gate67830

end PhysicalProjection
#print axioms PhysicalProjection.pair_det_ne
#print axioms PhysicalProjection.pade_f
#print axioms PhysicalProjection.pade_g
#print axioms PhysicalProjection.point_pade
#print axioms PhysicalProjection.point_pivots
#print axioms PhysicalProjection.detector_rows
#print axioms PhysicalProjection.split_rows
#print axioms PhysicalProjection.chart_agrees
#print axioms PhysicalProjection.private_extension
#print axioms PhysicalProjection.ordinary_projection
#print axioms PhysicalProjection.marked_projection
#print axioms PhysicalProjection.designated_coordinates
#print axioms PhysicalProjection.designated_zero
#print axioms PhysicalProjection.Gate510.ordinary
#print axioms PhysicalProjection.Gate510.marked
#print axioms PhysicalProjection.Gate67830.ordinary
#print axioms PhysicalProjection.Gate67830.marked
