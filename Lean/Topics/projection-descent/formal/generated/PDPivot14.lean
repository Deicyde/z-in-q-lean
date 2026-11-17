import PDSharedData
import PDPivot13
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot14 (g : Bool) (a : Rat) : project stepI13 (stepF13 g) a ↔ project stepI14 (stepF14 g) a := by
  apply pivot_project stepI13 (stepF13 g) 401 176 (-4096) numerator14 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache13_401 g]; exact pivot_cell p401A p401Z 176 (-4096) x
theorem supported14 (g : Bool) (prev : ∀ i∈stepI13, supported live13 (stepF13 g i)) : ∀ i∈stepI14, supported live14 (stepF14 g i) :=
  subst_family (i:=401) (by decide : (-4096:Int)≠0) (reads_supported (by decide : reads live14 numerator14=true)) prev
end ProjectionDescent.Shared
