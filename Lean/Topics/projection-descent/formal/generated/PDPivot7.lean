import PDSharedData
import PDPivot6
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot7 (g : Bool) (a : Rat) : project stepI6 (stepF6 g) a ↔ project stepI7 (stepF7 g) a := by
  apply pivot_project stepI6 (stepF6 g) 25 55 (-1) numerator7 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache6_25 g]; exact pivot_cell p25A p25Z 55 (-1) x
theorem supported7 (g : Bool) (prev : ∀ i∈stepI6, supported live6 (stepF6 g i)) : ∀ i∈stepI7, supported live7 (stepF7 g i) :=
  subst_family (i:=25) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live7 numerator7=true)) prev
theorem cache7_593 (g : Bool) : stepF7 g 593=p593 := by
  change substitute 55 (-1) numerator7 (stepF6 g 593)=p593
  rw [cache6_593 g]; exact substitute_absent 55 (-1) numerator7 p593 (by decide)
theorem cache7_396 (g : Bool) : stepF7 g 396=p396 := by
  change substitute 55 (-1) numerator7 (stepF6 g 396)=p396
  rw [cache6_396 g]; exact substitute_absent 55 (-1) numerator7 p396 (by decide)
theorem cache7_520 (g : Bool) : stepF7 g 520=p520 := by
  change substitute 55 (-1) numerator7 (stepF6 g 520)=p520
  rw [cache6_520 g]; exact substitute_absent 55 (-1) numerator7 p520 (by decide)
theorem cache7_24 (g : Bool) : stepF7 g 24=p24 := by
  change substitute 55 (-1) numerator7 (stepF6 g 24)=p24
  rw [cache6_24 g]; exact substitute_absent 55 (-1) numerator7 p24 (by decide)
theorem cache7_534 (g : Bool) : stepF7 g 534=p534 := by
  change substitute 55 (-1) numerator7 (stepF6 g 534)=p534
  rw [cache6_534 g]; exact substitute_absent 55 (-1) numerator7 p534 (by decide)
theorem cache7_513 (g : Bool) : stepF7 g 513=p513 := by
  change substitute 55 (-1) numerator7 (stepF6 g 513)=p513
  rw [cache6_513 g]; exact substitute_absent 55 (-1) numerator7 p513 (by decide)
theorem cache7_401 (g : Bool) : stepF7 g 401=p401 := by
  change substitute 55 (-1) numerator7 (stepF6 g 401)=p401
  rw [cache6_401 g]; exact substitute_absent 55 (-1) numerator7 p401 (by decide)
theorem cache7_514 (g : Bool) : stepF7 g 514=p514 := by
  change substitute 55 (-1) numerator7 (stepF6 g 514)=p514
  rw [cache6_514 g]; exact substitute_absent 55 (-1) numerator7 p514 (by decide)
end ProjectionDescent.Shared
