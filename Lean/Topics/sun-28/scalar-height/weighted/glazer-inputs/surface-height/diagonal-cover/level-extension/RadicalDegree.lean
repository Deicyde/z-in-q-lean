import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Data.Rat.Sqrt
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic

namespace ZInQBlueprint.LevelExtension
noncomputable section

/-- Each new class lies outside the span of the preceding squareclasses.
The recursive test doubles the candidates after adjoining each radical. -/
def Avoids {K : Type*} [Field K] : List K → K → Prop
  | [], b => ¬ IsSquare b
  | d::ds,b => Avoids ds b ∧ Avoids ds (b*d)

def IndependentRadicals {K : Type*} [Field K] : List K → Prop
  | [] => True
  | d::ds => Avoids ds d ∧ IndependentRadicals ds

instance {K : Type*} [Field K] [DecidablePred (IsSquare : K → Prop)] (l : List K) (b : K) :
    Decidable (Avoids l b) := by induction l generalizing b with
  | nil => exact inferInstanceAs (Decidable (¬IsSquare b))
  | cons a l ih => exact @instDecidableAnd _ _ (ih b) (ih (b*a))

instance {K : Type*} [Field K] [DecidablePred (IsSquare : K → Prop)] (l : List K) :
    Decidable (IndependentRadicals l) := by induction l with
  | nil => exact isTrue trivial
  | cons a l ih => exact @instDecidableAnd _ _ inferInstance ih

theorem square_over_quadratic {K : Type*} [Field K] [CharZero K] {a b : K}
    (sq : IsSquare (algebraMap K (QuadraticAlgebra K a 0) b)) : IsSquare b ∨ IsSquare (b*a) := by
  obtain ⟨z,h⟩:=sq
  have re := congrArg QuadraticAlgebra.re h
  have im := congrArg QuadraticAlgebra.im h
  simp only [QuadraticAlgebra.algebraMap_re,QuadraticAlgebra.re_mul] at re
  simp only [QuadraticAlgebra.algebraMap_im,QuadraticAlgebra.im_mul,zero_mul,add_zero] at im
  have prod : z.re*z.im=0 := by linear_combination -im/2
  rcases mul_eq_zero.mp prod with hr|hi
  · right
    refine ⟨a*z.im,?_⟩
    rw [re,hr]
    ring
  · left
    exact ⟨z.re,by simpa [hi] using re⟩

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.square_over_quadratic
