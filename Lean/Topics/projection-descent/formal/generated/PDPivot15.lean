import PDSharedData
import PDPivot14
import ProjectionSupport
open ZeroInput.Sparse
namespace ProjectionDescent.Shared
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

private theorem subst_zero (j : Nat) (c : Int) (hc : c≠0) (n p : Polynomial) (x : Assignment) :
    value x (substitute j c n p)=0 ↔ value (put x j (value x n/(c:Rat))) p=0 := by
  obtain ⟨k,nz,ev⟩ := substitute_value j c hc n p
  rw [ev]; exact ⟨fun h => (Rat.mul_eq_zero.mp h).resolve_left nz,fun h => by rw [h,Rat.mul_zero]⟩

private theorem late_arithmetic (x : Assignment) :
    value (put x 8 (value x numerator13/8)) p514=0 ↔ value x p514late=0 := by
  let v : Rat := value x numerator13/8
  have cleared : v*8=value x numerator13 := Rat.div_mul_cancel (by decide)
  have exactRow : 8*value (put x 8 v) p514=2*value x p514late := by
    simp only [numerator13,scale_value,value_append,p513A,p513Z,value,termValue,monomialValue] at cleared
    simp [p514,p514A,p514Z,p514late,p514lateA,p514lateZ,value,termValue,monomialValue,put,Rat.add_zero,Rat.mul_one]
    grobner
  change value (put x 8 v) p514=0 ↔ _
  constructor <;> intro h <;> grind

private theorem late_agrees (g : Bool) (x : Assignment) : value x (stepF14 g 514)=0 ↔
    ((-164:Int):Rat)*x 9=value x numerator15 := by
  let v := value x numerator14/(-4096:Rat)
  let y := put x 176 v
  let w := value x numerator13/8
  have same : value y numerator13=value x numerator13 := unchanged x 176 v numerator13 (by decide)
  have commute : put y 8 (value y numerator13/8) = put (put x 8 w) 176 v := by
    rw [same]; funext i
    by_cases h : i=8
    · subst i; simp [put,w]
    · by_cases h' : i=176 <;> simp [put,y,h,h',w]
  calc value x (stepF14 g 514)=0 ↔ value y (stepF13 g 514)=0 := subst_zero 176 (-4096) (by decide) _ _ x
       _ ↔ value (put y 8 (value y numerator13/8)) (stepF12 g 514)=0 := subst_zero 8 8 (by decide) _ _ y
       _ ↔ value (put x 8 w) p514=0 := by
         rw [cache12_514 g,commute,unchanged (put x 8 w) 176 v p514 (by decide)]
       _ ↔ value x p514late=0 := late_arithmetic x
       _ ↔ _ := pivot_cell p514lateA p514lateZ 9 (-164) x

theorem pivot15 (g : Bool) (a : Rat) : project stepI14 (stepF14 g) a ↔ project stepI15 (stepF15 g) a := by
  apply pivot_project stepI14 (stepF14 g) 514 9 (-164) numerator15 (by decide) (by decide) (by decide) (by decide)
  intro x; exact late_agrees g x
theorem supported15 (g : Bool) (prev : ∀ i∈stepI14, supported live14 (stepF14 g i)) : ∀ i∈stepI15, supported live15 (stepF15 g i) :=
  subst_family (i:=514) (by decide : (-164:Int)≠0) (reads_supported (by decide : reads live15 numerator15=true)) prev
end ProjectionDescent.Shared
