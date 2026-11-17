import PDSharedData
import PDPivot11
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot12 (g : Bool) (a : Rat) : project stepI11 (stepF11 g) a ↔ project stepI12 (stepF12 g) a := by
  apply pivot_project stepI11 (stepF11 g) 534 178 (-1) numerator12 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache11_534 g]; exact pivot_cell p534A p534Z 178 (-1) x
theorem supported12 (g : Bool) (prev : ∀ i∈stepI11, supported live11 (stepF11 g i)) : ∀ i∈stepI12, supported live12 (stepF12 g i) :=
  subst_family (i:=534) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live12 numerator12=true)) prev
theorem cache12_513 (g : Bool) : stepF12 g 513=p513 := by
  change substitute 178 (-1) numerator12 (stepF11 g 513)=p513
  rw [cache11_513 g]; exact substitute_absent 178 (-1) numerator12 p513 (by decide)
theorem cache12_401 (g : Bool) : stepF12 g 401=p401 := by
  change substitute 178 (-1) numerator12 (stepF11 g 401)=p401
  rw [cache11_401 g]; exact substitute_absent 178 (-1) numerator12 p401 (by decide)
theorem cache12_514 (g : Bool) : stepF12 g 514=p514 := by
  change substitute 178 (-1) numerator12 (stepF11 g 514)=p514
  rw [cache11_514 g]; exact substitute_absent 178 (-1) numerator12 p514 (by decide)
end ProjectionDescent.Shared
