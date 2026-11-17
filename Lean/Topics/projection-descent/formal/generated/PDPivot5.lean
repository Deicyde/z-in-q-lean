import PDSharedData
import PDPivot4
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot5 (g : Bool) (a : Rat) : project stepI4 (stepF4 g) a ↔ project stepI5 (stepF5 g) a := by
  apply pivot_project stepI4 (stepF4 g) 363 168 (-1) numerator5 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache4_363 g]; exact pivot_cell p363A p363Z 168 (-1) x
theorem supported5 (g : Bool) (prev : ∀ i∈stepI4, supported live4 (stepF4 g i)) : ∀ i∈stepI5, supported live5 (stepF5 g i) :=
  subst_family (i:=363) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live5 numerator5=true)) prev
theorem cache5_594 (g : Bool) : stepF5 g 594=p594 := by
  change substitute 168 (-1) numerator5 (stepF4 g 594)=p594
  rw [cache4_594 g]; exact substitute_absent 168 (-1) numerator5 p594 (by decide)
theorem cache5_25 (g : Bool) : stepF5 g 25=p25 := by
  change substitute 168 (-1) numerator5 (stepF4 g 25)=p25
  rw [cache4_25 g]; exact substitute_absent 168 (-1) numerator5 p25 (by decide)
theorem cache5_593 (g : Bool) : stepF5 g 593=p593 := by
  change substitute 168 (-1) numerator5 (stepF4 g 593)=p593
  rw [cache4_593 g]; exact substitute_absent 168 (-1) numerator5 p593 (by decide)
theorem cache5_396 (g : Bool) : stepF5 g 396=p396 := by
  change substitute 168 (-1) numerator5 (stepF4 g 396)=p396
  rw [cache4_396 g]; exact substitute_absent 168 (-1) numerator5 p396 (by decide)
theorem cache5_520 (g : Bool) : stepF5 g 520=p520 := by
  change substitute 168 (-1) numerator5 (stepF4 g 520)=p520
  rw [cache4_520 g]; exact substitute_absent 168 (-1) numerator5 p520 (by decide)
theorem cache5_24 (g : Bool) : stepF5 g 24=p24 := by
  change substitute 168 (-1) numerator5 (stepF4 g 24)=p24
  rw [cache4_24 g]; exact substitute_absent 168 (-1) numerator5 p24 (by decide)
theorem cache5_534 (g : Bool) : stepF5 g 534=p534 := by
  change substitute 168 (-1) numerator5 (stepF4 g 534)=p534
  rw [cache4_534 g]; exact substitute_absent 168 (-1) numerator5 p534 (by decide)
theorem cache5_513 (g : Bool) : stepF5 g 513=p513 := by
  change substitute 168 (-1) numerator5 (stepF4 g 513)=p513
  rw [cache4_513 g]; exact substitute_absent 168 (-1) numerator5 p513 (by decide)
theorem cache5_401 (g : Bool) : stepF5 g 401=p401 := by
  change substitute 168 (-1) numerator5 (stepF4 g 401)=p401
  rw [cache4_401 g]; exact substitute_absent 168 (-1) numerator5 p401 (by decide)
theorem cache5_514 (g : Bool) : stepF5 g 514=p514 := by
  change substitute 168 (-1) numerator5 (stepF4 g 514)=p514
  rw [cache4_514 g]; exact substitute_absent 168 (-1) numerator5 p514 (by decide)
end ProjectionDescent.Shared
