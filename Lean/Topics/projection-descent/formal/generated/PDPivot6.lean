import PDSharedData
import PDPivot5
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot6 (g : Bool) (a : Rat) : project stepI5 (stepF5 g) a ↔ project stepI6 (stepF6 g) a := by
  apply pivot_project stepI5 (stepF5 g) 594 213 (1) numerator6 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache5_594 g]; exact pivot_cell p594A p594Z 213 (1) x
theorem supported6 (g : Bool) (prev : ∀ i∈stepI5, supported live5 (stepF5 g i)) : ∀ i∈stepI6, supported live6 (stepF6 g i) :=
  subst_family (i:=594) (by decide : (1:Int)≠0) (reads_supported (by decide : reads live6 numerator6=true)) prev
theorem cache6_25 (g : Bool) : stepF6 g 25=p25 := by
  change substitute 213 (1) numerator6 (stepF5 g 25)=p25
  rw [cache5_25 g]; exact substitute_absent 213 (1) numerator6 p25 (by decide)
theorem cache6_593 (g : Bool) : stepF6 g 593=p593 := by
  change substitute 213 (1) numerator6 (stepF5 g 593)=p593
  rw [cache5_593 g]; exact substitute_absent 213 (1) numerator6 p593 (by decide)
theorem cache6_396 (g : Bool) : stepF6 g 396=p396 := by
  change substitute 213 (1) numerator6 (stepF5 g 396)=p396
  rw [cache5_396 g]; exact substitute_absent 213 (1) numerator6 p396 (by decide)
theorem cache6_520 (g : Bool) : stepF6 g 520=p520 := by
  change substitute 213 (1) numerator6 (stepF5 g 520)=p520
  rw [cache5_520 g]; exact substitute_absent 213 (1) numerator6 p520 (by decide)
theorem cache6_24 (g : Bool) : stepF6 g 24=p24 := by
  change substitute 213 (1) numerator6 (stepF5 g 24)=p24
  rw [cache5_24 g]; exact substitute_absent 213 (1) numerator6 p24 (by decide)
theorem cache6_534 (g : Bool) : stepF6 g 534=p534 := by
  change substitute 213 (1) numerator6 (stepF5 g 534)=p534
  rw [cache5_534 g]; exact substitute_absent 213 (1) numerator6 p534 (by decide)
theorem cache6_513 (g : Bool) : stepF6 g 513=p513 := by
  change substitute 213 (1) numerator6 (stepF5 g 513)=p513
  rw [cache5_513 g]; exact substitute_absent 213 (1) numerator6 p513 (by decide)
theorem cache6_401 (g : Bool) : stepF6 g 401=p401 := by
  change substitute 213 (1) numerator6 (stepF5 g 401)=p401
  rw [cache5_401 g]; exact substitute_absent 213 (1) numerator6 p401 (by decide)
theorem cache6_514 (g : Bool) : stepF6 g 514=p514 := by
  change substitute 213 (1) numerator6 (stepF5 g 514)=p514
  rw [cache5_514 g]; exact substitute_absent 213 (1) numerator6 p514 (by decide)
end ProjectionDescent.Shared
