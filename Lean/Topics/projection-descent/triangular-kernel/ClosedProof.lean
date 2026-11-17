import TriRanks2
open ZeroInput.Sparse ProjectionDescent
namespace Triangular.Data
set_option maxRecDepth 16000
set_option maxHeartbeats 2500000

private theorem good (g : Bool) : valid (ps g)=true := good0 g
private theorem no_input (g : Bool) : 1∉slots (ps g) := by unfold ps; rw [slots0]; decide
private theorem scope (g : Bool) : ∀ i∈slots (ps g), inside i=true := by
  have c : (slots (ps g)).all inside=true := by unfold ps; rw [slots0]; decide
  exact List.all_eq_true.mp c
private theorem unmarked (g : Bool) (rs : Rows) (a : Rat) :
    RowsProject 226 (parent (ps g) rs) a ↔ ∃ y, finiteLift y 1=a ∧ ordinary (ps g) rs code y=0 :=
  ordinary_iff _ _ code back _ (good g) (no_input g) (by decide) (by decide) (scope g) (rangeTable g)

theorem ordinary_projection (g : Bool) (a : Rat) :
    RowsProject 226 (parent (ps g) (top::rest g)) a ↔
      ∃ y : Fin 153→Rat, finiteLift y 1=a ∧ ordinary (ps g) (top::rest g) code y=0 :=
  unmarked g _ a

private theorem row402AtZero (g : Bool) : RowsProject 226 (parent (ps g) [top]) 0 := by
  apply zero_parent _ _ w
  · intro i h; simp [w,h]
  · decide
  · exact zero0 g
  · decide

theorem marked_projection (g : Bool) (a : Rat) :
    (∃ y : Fin 153→Rat, finiteLift y 1=a ∧ marked (ps g) top (rest g) code y=0) ↔
      RowsProject 226 (parent (ps g) (top::rest g)) a ∨ a=0 :=
  marked_iff _ _ _ _ _ (ordinary_projection g a) ((unmarked g [top] 0).mp (row402AtZero g))

end Triangular.Data
#print axioms Triangular.Data.ordinary_projection
#print axioms Triangular.Data.marked_projection
