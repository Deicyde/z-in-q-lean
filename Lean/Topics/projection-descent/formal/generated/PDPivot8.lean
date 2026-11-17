import PDSharedData
import PDPivot7
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot8 (g : Bool) (a : Rat) : project stepI7 (stepF7 g) a ↔ project stepI8 (stepF8 g) a := by
  apply pivot_project stepI7 (stepF7 g) 593 212 (1) numerator8 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache7_593 g]; exact pivot_cell p593A p593Z 212 (1) x
theorem supported8 (g : Bool) (prev : ∀ i∈stepI7, supported live7 (stepF7 g i)) : ∀ i∈stepI8, supported live8 (stepF8 g i) :=
  subst_family (i:=593) (by decide : (1:Int)≠0) (reads_supported (by decide : reads live8 numerator8=true)) prev
theorem cache8_396 (g : Bool) : stepF8 g 396=p396 := by
  change substitute 212 (1) numerator8 (stepF7 g 396)=p396
  rw [cache7_396 g]; exact substitute_absent 212 (1) numerator8 p396 (by decide)
theorem cache8_520 (g : Bool) : stepF8 g 520=p520 := by
  change substitute 212 (1) numerator8 (stepF7 g 520)=p520
  rw [cache7_520 g]; exact substitute_absent 212 (1) numerator8 p520 (by decide)
theorem cache8_24 (g : Bool) : stepF8 g 24=p24 := by
  change substitute 212 (1) numerator8 (stepF7 g 24)=p24
  rw [cache7_24 g]; exact substitute_absent 212 (1) numerator8 p24 (by decide)
theorem cache8_534 (g : Bool) : stepF8 g 534=p534 := by
  change substitute 212 (1) numerator8 (stepF7 g 534)=p534
  rw [cache7_534 g]; exact substitute_absent 212 (1) numerator8 p534 (by decide)
theorem cache8_513 (g : Bool) : stepF8 g 513=p513 := by
  change substitute 212 (1) numerator8 (stepF7 g 513)=p513
  rw [cache7_513 g]; exact substitute_absent 212 (1) numerator8 p513 (by decide)
theorem cache8_401 (g : Bool) : stepF8 g 401=p401 := by
  change substitute 212 (1) numerator8 (stepF7 g 401)=p401
  rw [cache7_401 g]; exact substitute_absent 212 (1) numerator8 p401 (by decide)
theorem cache8_514 (g : Bool) : stepF8 g 514=p514 := by
  change substitute 212 (1) numerator8 (stepF7 g 514)=p514
  rw [cache7_514 g]; exact substitute_absent 212 (1) numerator8 p514 (by decide)
end ProjectionDescent.Shared
