import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Tactic

namespace Sun28.ConicNegative
noncomputable section

abbrev K := QuadraticAlgebra ℚ 3073 0
def alpha : K := ⟨2353/240,49/240⟩
def delta : K := ⟨-235/2,-5/2⟩
def component (s : ℚ) : Prop := ∃ z : K, QuadraticAlgebra.C s - alpha = delta*z^2

def H (t v : ℚ) : ℚ :=
  25*(v^2+6*t^2)^2-3528*(v^2-6*t^2)*(2*t*v)+2303*(v^2-6*t^2)^2

theorem component_four : component 4 := by
  refine ⟨⟨-91/720,1/144⟩,?_⟩
  change (⟨4,0⟩:K)-alpha=delta*⟨-91/720,1/144⟩^2
  apply QuadraticAlgebra.ext
  · change (4:ℚ)-2353/240 = _
    norm_num [alpha,delta,pow_two]
  · change (0:ℚ)-49/240 = _
    norm_num [alpha,delta,pow_two]

/-- Comparing the rational and irrational coefficients of the actual squareclass gives
a rational conic and the marked function on it. -/
theorem component_circle {s : ℚ} (hs : component s) :
    ∃ X Y : ℚ, X^2+6*Y^2=1 ∧ 120*s=25-3528*X*Y+2303*X^2 := by
  obtain ⟨⟨u,v⟩,e⟩:=hs
  have e1:=congrArg QuadraticAlgebra.re e
  have e2:=congrArg QuadraticAlgebra.im e
  simp [alpha,delta,pow_two] at e1 e2
  refine ⟨720*v/7,10*(u+47*v)/7,?_,?_⟩
  · linear_combination (240/49:ℚ)*e2
  · linear_combination 120*e1 - 5640*e2

/-- The sign of the square root interchanges the antipodal points. The north chart covers
every rational abscissa, including the image of its missing point. -/
theorem component_chart {s:ℚ} (h:component s) :
    ∃ t : ℚ, 120*s*(1+6*t^2)^2=H t 1 := by
  obtain ⟨x,y,c,v⟩:=component_circle h
  by_cases south : 1+x=0
  · have x1:x=-1:=by linarith
    rw [x1] at c v
    have z:y=0:=by nlinarith [sq_nonneg y]
    refine ⟨0,?_⟩
    subst y
    norm_num [H] at v ⊢
    linarith
  · let t:=y/(1+x)
    have tx:x*(1+6*t^2)=1-6*t^2 := by
      dsimp [t]
      field_simp [south]
      linear_combination (x+1)*c
    have ty:y*(1+6*t^2)=2*t := by
      dsimp [t]
      field_simp [south]
      linear_combination y*c
    refine ⟨t,?_⟩
    simp only [H,one_pow,mul_one]
    linear_combination (1+6*t^2)^2*v + (2303*(x*(1+6*t^2)+(1-6*t^2))-3528*y*(1+6*t^2))*tx -3528*(1-6*t^2)*ty

end
end Sun28.ConicNegative
#print axioms Sun28.ConicNegative.component_circle
#print axioms Sun28.ConicNegative.component_chart
#print axioms Sun28.ConicNegative.component_four
