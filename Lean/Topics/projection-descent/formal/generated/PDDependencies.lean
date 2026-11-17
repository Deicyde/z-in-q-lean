import PDProjection
open ZeroInput.Sparse
open ProjectionDescent
theorem literal510 (a : Rat) :
    (∃ x : Fin 249 → Rat, finiteLift x 1=a ∧ ∀ r∈Gate510.parent, value (finiteLift x) r.2=0) ↔
    (∃ x : Fin 226 → Rat, finiteLift x 1=a ∧ ∀ r∈Gate510.compact, value (finiteLift x) r.2=0) :=
  Gate510.residual_projection a
theorem polynomial510 (a : Rat) :
    (∃ x : Fin 249 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate510.parent)=0) ↔
    (∃ x : Fin 226 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate510.compact)=0) :=
  Gate510.polynomial_projection a
theorem literal67830 (a : Rat) :
    (∃ x : Fin 249 → Rat, finiteLift x 1=a ∧ ∀ r∈Gate67830.parent, value (finiteLift x) r.2=0) ↔
    (∃ x : Fin 226 → Rat, finiteLift x 1=a ∧ ∀ r∈Gate67830.compact, value (finiteLift x) r.2=0) :=
  Gate67830.residual_projection a
theorem polynomial67830 (a : Rat) :
    (∃ x : Fin 249 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate67830.parent)=0) ↔
    (∃ x : Fin 226 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate67830.compact)=0) :=
  Gate67830.polynomial_projection a
#print axioms ProjectionDescent.scale_value
#print axioms ProjectionDescent.primitive_value
#print axioms ProjectionDescent.substitute_value
#print axioms ProjectionDescent.pivot_project
#print axioms ProjectionDescent.pole_project
#print axioms ProjectionDescent.compact_project
#print axioms RowSquares.zero_iff_rows
#print axioms ThreeCoordinates.weak_iff_sextic
#print axioms ProjectionDescent.Shared.physical1
#print axioms ProjectionDescent.Shared.physical2
#print axioms ProjectionDescent.Shared.physical3
#print axioms ProjectionDescent.Shared.physical4
#print axioms ProjectionDescent.Shared.pivot1
#print axioms ProjectionDescent.Shared.pivot2
#print axioms ProjectionDescent.Shared.pivot3
#print axioms ProjectionDescent.Shared.pivot4
#print axioms ProjectionDescent.Shared.pivot5
#print axioms ProjectionDescent.Shared.pivot6
#print axioms ProjectionDescent.Shared.pivot7
#print axioms ProjectionDescent.Shared.pivot8
#print axioms ProjectionDescent.Shared.pivot9
#print axioms ProjectionDescent.Shared.pivot10
#print axioms ProjectionDescent.Shared.pivot11
#print axioms ProjectionDescent.Shared.pivot12
#print axioms ProjectionDescent.Shared.pivot13
#print axioms ProjectionDescent.Shared.pivot14
#print axioms ProjectionDescent.Shared.pivot15
#print axioms ProjectionDescent.Shared.literal_projection
#print axioms ProjectionDescent.Gate510.residual_projection
#print axioms ProjectionDescent.Gate510.polynomial_projection
#print axioms literal510
#print axioms polynomial510
#print axioms ProjectionDescent.Gate67830.residual_projection
#print axioms ProjectionDescent.Gate67830.polynomial_projection
#print axioms literal67830
#print axioms polynomial67830
