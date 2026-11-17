import PDSharedData
import PDPivot2
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot3 (g : Bool) (a : Rat) : project stepI2 (stepF2 g) a ↔ project stepI3 (stepF3 g) a := by
  apply pivot_project stepI2 (stepF2 g) 298 145 (-1) numerator3 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache2_298 g]; exact pivot_cell p298A p298Z 145 (-1) x
theorem supported3 (g : Bool) (prev : ∀ i∈stepI2, supported live2 (stepF2 g i)) : ∀ i∈stepI3, supported live3 (stepF3 g i) :=
  subst_family (i:=298) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live3 numerator3=true)) prev
theorem cache3_289 (g : Bool) : stepF3 g 289=p289 := by
  change substitute 145 (-1) numerator3 (stepF2 g 289)=p289
  rw [cache2_289 g]; exact substitute_absent 145 (-1) numerator3 p289 (by decide)
theorem cache3_363 (g : Bool) : stepF3 g 363=p363 := by
  change substitute 145 (-1) numerator3 (stepF2 g 363)=p363
  rw [cache2_363 g]; exact substitute_absent 145 (-1) numerator3 p363 (by decide)
theorem cache3_594 (g : Bool) : stepF3 g 594=p594 := by
  change substitute 145 (-1) numerator3 (stepF2 g 594)=p594
  rw [cache2_594 g]; exact substitute_absent 145 (-1) numerator3 p594 (by decide)
theorem cache3_25 (g : Bool) : stepF3 g 25=p25 := by
  change substitute 145 (-1) numerator3 (stepF2 g 25)=p25
  rw [cache2_25 g]; exact substitute_absent 145 (-1) numerator3 p25 (by decide)
theorem cache3_593 (g : Bool) : stepF3 g 593=p593 := by
  change substitute 145 (-1) numerator3 (stepF2 g 593)=p593
  rw [cache2_593 g]; exact substitute_absent 145 (-1) numerator3 p593 (by decide)
theorem cache3_396 (g : Bool) : stepF3 g 396=p396 := by
  change substitute 145 (-1) numerator3 (stepF2 g 396)=p396
  rw [cache2_396 g]; exact substitute_absent 145 (-1) numerator3 p396 (by decide)
theorem cache3_520 (g : Bool) : stepF3 g 520=p520 := by
  change substitute 145 (-1) numerator3 (stepF2 g 520)=p520
  rw [cache2_520 g]; exact substitute_absent 145 (-1) numerator3 p520 (by decide)
theorem cache3_24 (g : Bool) : stepF3 g 24=p24 := by
  change substitute 145 (-1) numerator3 (stepF2 g 24)=p24
  rw [cache2_24 g]; exact substitute_absent 145 (-1) numerator3 p24 (by decide)
theorem cache3_534 (g : Bool) : stepF3 g 534=p534 := by
  change substitute 145 (-1) numerator3 (stepF2 g 534)=p534
  rw [cache2_534 g]; exact substitute_absent 145 (-1) numerator3 p534 (by decide)
theorem cache3_513 (g : Bool) : stepF3 g 513=p513 := by
  change substitute 145 (-1) numerator3 (stepF2 g 513)=p513
  rw [cache2_513 g]; exact substitute_absent 145 (-1) numerator3 p513 (by decide)
theorem cache3_401 (g : Bool) : stepF3 g 401=p401 := by
  change substitute 145 (-1) numerator3 (stepF2 g 401)=p401
  rw [cache2_401 g]; exact substitute_absent 145 (-1) numerator3 p401 (by decide)
theorem cache3_514 (g : Bool) : stepF3 g 514=p514 := by
  change substitute 145 (-1) numerator3 (stepF2 g 514)=p514
  rw [cache2_514 g]; exact substitute_absent 145 (-1) numerator3 p514 (by decide)
end ProjectionDescent.Shared
