import PDSharedData
import PDPivot12
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot13 (g : Bool) (a : Rat) : project stepI12 (stepF12 g) a ↔ project stepI13 (stepF13 g) a := by
  apply pivot_project stepI12 (stepF12 g) 513 8 (8) numerator13 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache12_513 g]; exact pivot_cell p513A p513Z 8 (8) x
theorem supported13 (g : Bool) (prev : ∀ i∈stepI12, supported live12 (stepF12 g i)) : ∀ i∈stepI13, supported live13 (stepF13 g i) :=
  subst_family (i:=513) (by decide : (8:Int)≠0) (reads_supported (by decide : reads live13 numerator13=true)) prev
theorem cache13_401 (g : Bool) : stepF13 g 401=p401 := by
  change substitute 8 (8) numerator13 (stepF12 g 401)=p401
  rw [cache12_401 g]; exact substitute_absent 8 (8) numerator13 p401 (by decide)
end ProjectionDescent.Shared
