import PDSharedData
import PDPivot8
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem pivot9 (g : Bool) (a : Rat) : project stepI8 (stepF8 g) a ↔ project stepI9 (stepF9 g) a := by
  apply pivot_project stepI8 (stepF8 g) 396 174 (-1) numerator9 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache8_396 g]; exact pivot_cell p396A p396Z 174 (-1) x
theorem supported9 (g : Bool) (prev : ∀ i∈stepI8, supported live8 (stepF8 g i)) : ∀ i∈stepI9, supported live9 (stepF9 g i) :=
  subst_family (i:=396) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live9 numerator9=true)) prev
theorem cache9_520 (g : Bool) : stepF9 g 520=p520 := by
  change substitute 174 (-1) numerator9 (stepF8 g 520)=p520
  rw [cache8_520 g]; exact substitute_absent 174 (-1) numerator9 p520 (by decide)
theorem cache9_24 (g : Bool) : stepF9 g 24=p24 := by
  change substitute 174 (-1) numerator9 (stepF8 g 24)=p24
  rw [cache8_24 g]; exact substitute_absent 174 (-1) numerator9 p24 (by decide)
theorem cache9_534 (g : Bool) : stepF9 g 534=p534 := by
  change substitute 174 (-1) numerator9 (stepF8 g 534)=p534
  rw [cache8_534 g]; exact substitute_absent 174 (-1) numerator9 p534 (by decide)
theorem cache9_513 (g : Bool) : stepF9 g 513=p513 := by
  change substitute 174 (-1) numerator9 (stepF8 g 513)=p513
  rw [cache8_513 g]; exact substitute_absent 174 (-1) numerator9 p513 (by decide)
theorem cache9_401 (g : Bool) : stepF9 g 401=p401 := by
  change substitute 174 (-1) numerator9 (stepF8 g 401)=p401
  rw [cache8_401 g]; exact substitute_absent 174 (-1) numerator9 p401 (by decide)
theorem cache9_514 (g : Bool) : stepF9 g 514=p514 := by
  change substitute 174 (-1) numerator9 (stepF8 g 514)=p514
  rw [cache8_514 g]; exact substitute_absent 174 (-1) numerator9 p514 (by decide)
end ProjectionDescent.Shared
