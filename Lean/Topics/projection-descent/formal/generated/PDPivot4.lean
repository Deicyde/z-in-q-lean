import PDSharedData
import PDPivot3
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot4 (g : Bool) (a : Rat) : project stepI3 (stepF3 g) a ↔ project stepI4 (stepF4 g) a := by
  apply pivot_project stepI3 (stepF3 g) 289 138 (-1) numerator4 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache3_289 g]; exact pivot_cell p289A p289Z 138 (-1) x
theorem supported4 (g : Bool) (prev : ∀ i∈stepI3, supported live3 (stepF3 g i)) : ∀ i∈stepI4, supported live4 (stepF4 g i) :=
  subst_family (i:=289) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live4 numerator4=true)) prev
theorem cache4_363 (g : Bool) : stepF4 g 363=p363 := by
  change substitute 138 (-1) numerator4 (stepF3 g 363)=p363
  rw [cache3_363 g]; exact substitute_absent 138 (-1) numerator4 p363 (by decide)
theorem cache4_594 (g : Bool) : stepF4 g 594=p594 := by
  change substitute 138 (-1) numerator4 (stepF3 g 594)=p594
  rw [cache3_594 g]; exact substitute_absent 138 (-1) numerator4 p594 (by decide)
theorem cache4_25 (g : Bool) : stepF4 g 25=p25 := by
  change substitute 138 (-1) numerator4 (stepF3 g 25)=p25
  rw [cache3_25 g]; exact substitute_absent 138 (-1) numerator4 p25 (by decide)
theorem cache4_593 (g : Bool) : stepF4 g 593=p593 := by
  change substitute 138 (-1) numerator4 (stepF3 g 593)=p593
  rw [cache3_593 g]; exact substitute_absent 138 (-1) numerator4 p593 (by decide)
theorem cache4_396 (g : Bool) : stepF4 g 396=p396 := by
  change substitute 138 (-1) numerator4 (stepF3 g 396)=p396
  rw [cache3_396 g]; exact substitute_absent 138 (-1) numerator4 p396 (by decide)
theorem cache4_520 (g : Bool) : stepF4 g 520=p520 := by
  change substitute 138 (-1) numerator4 (stepF3 g 520)=p520
  rw [cache3_520 g]; exact substitute_absent 138 (-1) numerator4 p520 (by decide)
theorem cache4_24 (g : Bool) : stepF4 g 24=p24 := by
  change substitute 138 (-1) numerator4 (stepF3 g 24)=p24
  rw [cache3_24 g]; exact substitute_absent 138 (-1) numerator4 p24 (by decide)
theorem cache4_534 (g : Bool) : stepF4 g 534=p534 := by
  change substitute 138 (-1) numerator4 (stepF3 g 534)=p534
  rw [cache3_534 g]; exact substitute_absent 138 (-1) numerator4 p534 (by decide)
theorem cache4_513 (g : Bool) : stepF4 g 513=p513 := by
  change substitute 138 (-1) numerator4 (stepF3 g 513)=p513
  rw [cache3_513 g]; exact substitute_absent 138 (-1) numerator4 p513 (by decide)
theorem cache4_401 (g : Bool) : stepF4 g 401=p401 := by
  change substitute 138 (-1) numerator4 (stepF3 g 401)=p401
  rw [cache3_401 g]; exact substitute_absent 138 (-1) numerator4 p401 (by decide)
theorem cache4_514 (g : Bool) : stepF4 g 514=p514 := by
  change substitute 138 (-1) numerator4 (stepF3 g 514)=p514
  rw [cache3_514 g]; exact substitute_absent 138 (-1) numerator4 p514 (by decide)
end ProjectionDescent.Shared
