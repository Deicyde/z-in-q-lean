import PDGate510Data
import PDGate67830Data
import PDParentSupport
import PDBaseSupport
import PDCoordinateBounds
import PDPhysical1
import PDPhysical2
import PDPhysical3
import PDPhysical4
import PDPivot1
import PDPivot2
import PDPivot3
import PDPivot4
import PDPivot5
import PDPivot6
import PDPivot7
import PDPivot8
import PDPivot9
import PDPivot10
import PDPivot11
import PDPivot12
import PDPivot13
import PDPivot14
import PDPivot15
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 3000000
theorem literal_projection (g : Bool) (a : Rat) : RowsProject 249 (table parentIds (original g)) a ↔ RowsProject 226 (table stepI15 (fun i => renumber code (stepF15 g i))) a := by
  have support := supported15 g (supported14 g (supported13 g (supported12 g (supported11 g (supported10 g (supported9 g (supported8 g (supported7 g (supported6 g (supported5 g (supported4 g (supported3 g (supported2 g (supported1 g (base_support g)))))))))))))))
  exact ((parent_project _ _ 249 (by decide) (old_support g) a).symm).trans ((physical1 g a).trans ((physical2 g a).trans ((physical3 g a).trans ((physical4 g a).trans ((pivot1 g a).trans ((pivot2 g a).trans ((pivot3 g a).trans ((pivot4 g a).trans ((pivot5 g a).trans ((pivot6 g a).trans ((pivot7 g a).trans ((pivot8 g a).trans ((pivot9 g a).trans ((pivot10 g a).trans ((pivot11 g a).trans ((pivot12 g a).trans ((pivot13 g a).trans ((pivot14 g a).trans ((pivot15 g a).trans (compact_project _ _ live15 code back 226 (by decide) (by decide) (by decide) coordinate_bounds support a))))))))))))))))))))
end ProjectionDescent.Shared
namespace ProjectionDescent
theorem Gate510.residual_projection (a : Rat) : RowsProject 249 Gate510.parent a ↔ RowsProject 226 Gate510.compact a := Shared.literal_projection false a
theorem Gate67830.residual_projection (a : Rat) : RowsProject 249 Gate67830.parent a ↔ RowsProject 226 Gate67830.compact a := Shared.literal_projection true a
private theorem squares_iff (n : Nat) (rows : Rows) (a : Rat) :
    (∃ x : Fin n → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion rows)=0) ↔ RowsProject n rows a := by
  constructor <;> rintro ⟨x,hx,h⟩
  · exact ⟨x,hx,(RowSquares.zero_iff_rows _ _).mp h⟩
  · exact ⟨x,hx,(RowSquares.zero_iff_rows _ _).mpr h⟩
theorem Gate510.polynomial_projection : ∀ a : Rat,
    (∃ x : Fin 249 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate510.parent)=0) ↔
    (∃ x : Fin 226 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate510.compact)=0) :=
  fun a => (squares_iff 249 _ a).trans ((Gate510.residual_projection a).trans (squares_iff 226 _ a).symm)
theorem Gate67830.polynomial_projection : ∀ a : Rat,
    (∃ x : Fin 249 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate67830.parent)=0) ↔
    (∃ x : Fin 226 → Rat, finiteLift x 1=a ∧ value (finiteLift x) (RowSquares.expansion Gate67830.compact)=0) :=
  fun a => (squares_iff 249 _ a).trans ((Gate67830.residual_projection a).trans (squares_iff 226 _ a).symm)
end ProjectionDescent
#print axioms ProjectionDescent.Gate510.residual_projection
#print axioms ProjectionDescent.Gate67830.residual_projection
#print axioms ProjectionDescent.Gate510.polynomial_projection
#print axioms ProjectionDescent.Gate67830.polynomial_projection
