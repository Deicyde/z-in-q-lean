import PDSharedData
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
theorem cache0_346 (g : Bool) : poleF4 g 346=p346 := rfl
theorem cache0_290 (g : Bool) : poleF4 g 290=p290 := rfl
theorem cache0_298 (g : Bool) : poleF4 g 298=p298 := rfl
theorem cache0_289 (g : Bool) : poleF4 g 289=p289 := rfl
theorem cache0_363 (g : Bool) : poleF4 g 363=p363 := rfl
theorem cache0_594 (g : Bool) : poleF4 g 594=p594 := rfl
theorem cache0_25 (g : Bool) : poleF4 g 25=p25 := rfl
theorem cache0_593 (g : Bool) : poleF4 g 593=p593 := rfl
theorem cache0_396 (g : Bool) : poleF4 g 396=p396 := rfl
theorem cache0_520 (g : Bool) : poleF4 g 520=p520 := rfl
theorem cache0_24 (g : Bool) : poleF4 g 24=p24 := rfl
theorem cache0_534 (g : Bool) : poleF4 g 534=p534 := rfl
theorem cache0_513 (g : Bool) : poleF4 g 513=p513 := rfl
theorem cache0_401 (g : Bool) : poleF4 g 401=p401 := rfl
theorem cache0_514 (g : Bool) : poleF4 g 514=p514 := rfl
theorem pivot1 (g : Bool) (a : Rat) : project poleI4 (poleF4 g) a ↔ project stepI1 (stepF1 g) a := by
  apply pivot_project poleI4 (poleF4 g) 346 159 (-1) numerator1 (by decide) (by decide) (by decide) (by decide)
  intro x; rw [cache0_346 g]; exact pivot_cell p346A p346Z 159 (-1) x
theorem supported1 (g : Bool) (prev : ∀ i∈poleI4, supported poleLive (poleF4 g i)) : ∀ i∈stepI1, supported live1 (stepF1 g i) :=
  subst_family (i:=346) (by decide : (-1:Int)≠0) (reads_supported (by decide : reads live1 numerator1=true)) prev
theorem cache1_290 (g : Bool) : stepF1 g 290=p290 := by
  change substitute 159 (-1) numerator1 (poleF4 g 290)=p290
  rw [cache0_290 g]; exact substitute_absent 159 (-1) numerator1 p290 (by decide)
theorem cache1_298 (g : Bool) : stepF1 g 298=p298 := by
  change substitute 159 (-1) numerator1 (poleF4 g 298)=p298
  rw [cache0_298 g]; exact substitute_absent 159 (-1) numerator1 p298 (by decide)
theorem cache1_289 (g : Bool) : stepF1 g 289=p289 := by
  change substitute 159 (-1) numerator1 (poleF4 g 289)=p289
  rw [cache0_289 g]; exact substitute_absent 159 (-1) numerator1 p289 (by decide)
theorem cache1_363 (g : Bool) : stepF1 g 363=p363 := by
  change substitute 159 (-1) numerator1 (poleF4 g 363)=p363
  rw [cache0_363 g]; exact substitute_absent 159 (-1) numerator1 p363 (by decide)
theorem cache1_594 (g : Bool) : stepF1 g 594=p594 := by
  change substitute 159 (-1) numerator1 (poleF4 g 594)=p594
  rw [cache0_594 g]; exact substitute_absent 159 (-1) numerator1 p594 (by decide)
theorem cache1_25 (g : Bool) : stepF1 g 25=p25 := by
  change substitute 159 (-1) numerator1 (poleF4 g 25)=p25
  rw [cache0_25 g]; exact substitute_absent 159 (-1) numerator1 p25 (by decide)
theorem cache1_593 (g : Bool) : stepF1 g 593=p593 := by
  change substitute 159 (-1) numerator1 (poleF4 g 593)=p593
  rw [cache0_593 g]; exact substitute_absent 159 (-1) numerator1 p593 (by decide)
theorem cache1_396 (g : Bool) : stepF1 g 396=p396 := by
  change substitute 159 (-1) numerator1 (poleF4 g 396)=p396
  rw [cache0_396 g]; exact substitute_absent 159 (-1) numerator1 p396 (by decide)
theorem cache1_520 (g : Bool) : stepF1 g 520=p520 := by
  change substitute 159 (-1) numerator1 (poleF4 g 520)=p520
  rw [cache0_520 g]; exact substitute_absent 159 (-1) numerator1 p520 (by decide)
theorem cache1_24 (g : Bool) : stepF1 g 24=p24 := by
  change substitute 159 (-1) numerator1 (poleF4 g 24)=p24
  rw [cache0_24 g]; exact substitute_absent 159 (-1) numerator1 p24 (by decide)
theorem cache1_534 (g : Bool) : stepF1 g 534=p534 := by
  change substitute 159 (-1) numerator1 (poleF4 g 534)=p534
  rw [cache0_534 g]; exact substitute_absent 159 (-1) numerator1 p534 (by decide)
theorem cache1_513 (g : Bool) : stepF1 g 513=p513 := by
  change substitute 159 (-1) numerator1 (poleF4 g 513)=p513
  rw [cache0_513 g]; exact substitute_absent 159 (-1) numerator1 p513 (by decide)
theorem cache1_401 (g : Bool) : stepF1 g 401=p401 := by
  change substitute 159 (-1) numerator1 (poleF4 g 401)=p401
  rw [cache0_401 g]; exact substitute_absent 159 (-1) numerator1 p401 (by decide)
theorem cache1_514 (g : Bool) : stepF1 g 514=p514 := by
  change substitute 159 (-1) numerator1 (poleF4 g 514)=p514
  rw [cache0_514 g]; exact substitute_absent 159 (-1) numerator1 p514 (by decide)
end ProjectionDescent.Shared
