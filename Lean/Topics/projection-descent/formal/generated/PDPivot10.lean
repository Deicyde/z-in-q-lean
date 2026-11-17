import PDSharedData
import PDPivot9
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot10 (g : Bool) (a : Rat) : project stepI9 (stepF9 g) a ↔ project stepI10 (stepF10 g) a := by
  apply pivot_project stepI9 (stepF9 g) 520 147 (-1) numerator10 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache9_520 g]; exact pivot_cell p520A p520Z 147 (-1) x
theorem supported10 (g : Bool) (prev : ∀ i∈stepI9, supported live9 (stepF9 g i)) : ∀ i∈stepI10, supported live10 (stepF10 g i) :=
  subst_family (i:=520) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live10 numerator10=true)) prev
theorem cache10_24 (g : Bool) : stepF10 g 24=p24 := by
  change substitute 147 (-1) numerator10 (stepF9 g 24)=p24
  rw [cache9_24 g]; exact substitute_absent 147 (-1) numerator10 p24 (by decide)
theorem cache10_534 (g : Bool) : stepF10 g 534=p534 := by
  change substitute 147 (-1) numerator10 (stepF9 g 534)=p534
  rw [cache9_534 g]; exact substitute_absent 147 (-1) numerator10 p534 (by decide)
theorem cache10_513 (g : Bool) : stepF10 g 513=p513 := by
  change substitute 147 (-1) numerator10 (stepF9 g 513)=p513
  rw [cache9_513 g]; exact substitute_absent 147 (-1) numerator10 p513 (by decide)
theorem cache10_401 (g : Bool) : stepF10 g 401=p401 := by
  change substitute 147 (-1) numerator10 (stepF9 g 401)=p401
  rw [cache9_401 g]; exact substitute_absent 147 (-1) numerator10 p401 (by decide)
theorem cache10_514 (g : Bool) : stepF10 g 514=p514 := by
  change substitute 147 (-1) numerator10 (stepF9 g 514)=p514
  rw [cache9_514 g]; exact substitute_absent 147 (-1) numerator10 p514 (by decide)
end ProjectionDescent.Shared
