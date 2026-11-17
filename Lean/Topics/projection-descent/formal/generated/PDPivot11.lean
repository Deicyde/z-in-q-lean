import PDSharedData
import PDPivot10
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot11 (g : Bool) (a : Rat) : project stepI10 (stepF10 g) a ↔ project stepI11 (stepF11 g) a := by
  apply pivot_project stepI10 (stepF10 g) 24 54 (-1) numerator11 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache10_24 g]; exact pivot_cell p24A p24Z 54 (-1) x
theorem supported11 (g : Bool) (prev : ∀ i∈stepI10, supported live10 (stepF10 g i)) : ∀ i∈stepI11, supported live11 (stepF11 g i) :=
  subst_family (i:=24) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live11 numerator11=true)) prev
theorem cache11_534 (g : Bool) : stepF11 g 534=p534 := by
  change substitute 54 (-1) numerator11 (stepF10 g 534)=p534
  rw [cache10_534 g]; exact substitute_absent 54 (-1) numerator11 p534 (by decide)
theorem cache11_513 (g : Bool) : stepF11 g 513=p513 := by
  change substitute 54 (-1) numerator11 (stepF10 g 513)=p513
  rw [cache10_513 g]; exact substitute_absent 54 (-1) numerator11 p513 (by decide)
theorem cache11_401 (g : Bool) : stepF11 g 401=p401 := by
  change substitute 54 (-1) numerator11 (stepF10 g 401)=p401
  rw [cache10_401 g]; exact substitute_absent 54 (-1) numerator11 p401 (by decide)
theorem cache11_514 (g : Bool) : stepF11 g 514=p514 := by
  change substitute 54 (-1) numerator11 (stepF10 g 514)=p514
  rw [cache10_514 g]; exact substitute_absent 54 (-1) numerator11 p514 (by decide)
end ProjectionDescent.Shared
