import PDSharedData
import PDPivot1
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot2 (g : Bool) (a : Rat) : project stepI1 (stepF1 g) a ↔ project stepI2 (stepF2 g) a := by
  apply pivot_project stepI1 (stepF1 g) 290 139 (-1) numerator2 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache1_290 g]; exact pivot_cell p290A p290Z 139 (-1) x
theorem supported2 (g : Bool) (prev : ∀ i∈stepI1, supported live1 (stepF1 g i)) : ∀ i∈stepI2, supported live2 (stepF2 g i) :=
  subst_family (i:=290) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live2 numerator2=true)) prev
theorem cache2_298 (g : Bool) : stepF2 g 298=p298 := by
  change substitute 139 (-1) numerator2 (stepF1 g 298)=p298
  rw [cache1_298 g]; exact substitute_absent 139 (-1) numerator2 p298 (by decide)
theorem cache2_289 (g : Bool) : stepF2 g 289=p289 := by
  change substitute 139 (-1) numerator2 (stepF1 g 289)=p289
  rw [cache1_289 g]; exact substitute_absent 139 (-1) numerator2 p289 (by decide)
theorem cache2_363 (g : Bool) : stepF2 g 363=p363 := by
  change substitute 139 (-1) numerator2 (stepF1 g 363)=p363
  rw [cache1_363 g]; exact substitute_absent 139 (-1) numerator2 p363 (by decide)
theorem cache2_594 (g : Bool) : stepF2 g 594=p594 := by
  change substitute 139 (-1) numerator2 (stepF1 g 594)=p594
  rw [cache1_594 g]; exact substitute_absent 139 (-1) numerator2 p594 (by decide)
theorem cache2_25 (g : Bool) : stepF2 g 25=p25 := by
  change substitute 139 (-1) numerator2 (stepF1 g 25)=p25
  rw [cache1_25 g]; exact substitute_absent 139 (-1) numerator2 p25 (by decide)
theorem cache2_593 (g : Bool) : stepF2 g 593=p593 := by
  change substitute 139 (-1) numerator2 (stepF1 g 593)=p593
  rw [cache1_593 g]; exact substitute_absent 139 (-1) numerator2 p593 (by decide)
theorem cache2_396 (g : Bool) : stepF2 g 396=p396 := by
  change substitute 139 (-1) numerator2 (stepF1 g 396)=p396
  rw [cache1_396 g]; exact substitute_absent 139 (-1) numerator2 p396 (by decide)
theorem cache2_520 (g : Bool) : stepF2 g 520=p520 := by
  change substitute 139 (-1) numerator2 (stepF1 g 520)=p520
  rw [cache1_520 g]; exact substitute_absent 139 (-1) numerator2 p520 (by decide)
theorem cache2_24 (g : Bool) : stepF2 g 24=p24 := by
  change substitute 139 (-1) numerator2 (stepF1 g 24)=p24
  rw [cache1_24 g]; exact substitute_absent 139 (-1) numerator2 p24 (by decide)
theorem cache2_534 (g : Bool) : stepF2 g 534=p534 := by
  change substitute 139 (-1) numerator2 (stepF1 g 534)=p534
  rw [cache1_534 g]; exact substitute_absent 139 (-1) numerator2 p534 (by decide)
theorem cache2_513 (g : Bool) : stepF2 g 513=p513 := by
  change substitute 139 (-1) numerator2 (stepF1 g 513)=p513
  rw [cache1_513 g]; exact substitute_absent 139 (-1) numerator2 p513 (by decide)
theorem cache2_401 (g : Bool) : stepF2 g 401=p401 := by
  change substitute 139 (-1) numerator2 (stepF1 g 401)=p401
  rw [cache1_401 g]; exact substitute_absent 139 (-1) numerator2 p401 (by decide)
theorem cache2_514 (g : Bool) : stepF2 g 514=p514 := by
  change substitute 139 (-1) numerator2 (stepF1 g 514)=p514
  rw [cache1_514 g]; exact substitute_absent 139 (-1) numerator2 p514 (by decide)
end ProjectionDescent.Shared
