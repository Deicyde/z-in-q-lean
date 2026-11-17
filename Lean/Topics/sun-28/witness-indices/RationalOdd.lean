import RationalWitness

/-! Sun's three successive rational square-root stages for an odd index. -/
namespace Sun28.WitnessIndices
open ZInQ WeierstrassCurve.Affine Sun28.Ordinates
noncomputable section

/-- One rational algebraic choice in one of the four signed charts. -/
def SquareStage (a y : K0) : Prop :=
  ∃ (b : Branch) (t : ℚ), b.condition a.re a.im t ∧ y=b.point a.im t

theorem squareStage_iff (a y : K0) : SquareStage a y ↔ y^2=a := (four_charts a.re a.im y).symm

/-- The odd-index chart as a sequence of rational choices, including the guard
for the unique quotient j=y/h. -/
def RationalOddChart (Q : CPoint) : Prop :=
  ∃ (x y : K0) (onCurve : curveC.toAffine.Nonsingular x y),
    Q = .some x y onCurve ∧ ∃ h u v : K0, h≠0 ∧ SquareStage x h ∧
      SquareStage (2*(x+y/h)) u ∧ SquareStage ((u*h+x+y/h)/epsilon) v

theorem rational_chart_iff (Q : CPoint) : RationalOddChart Q ↔ OddChart Q := by
  constructor
  · rintro ⟨x,y,e,eq,h,u,v,hn,hs,us,vs⟩
    have right := (eq_div_iff epsilon_ne_zero).1 ((squareStage_iff _ _).1 vs)
    refine ⟨x,y,e,eq,h,y/h,u,v,hn,(squareStage_iff _ _).1 hs,?_,(squareStage_iff _ _).1 us,?_⟩
    · field_simp [hn]
    · linear_combination -right
  · rintro ⟨x,y,e,eq,h,j,u,v,hn,hs,hy,us,vs⟩
    have hj : y/h=j := by rw [hy]; field_simp
    refine ⟨x,y,e,eq,h,u,v,hn,(squareStage_iff _ _).2 hs,?_,?_⟩
    · rw [hj]; exact (squareStage_iff _ _).2 us
    · rw [hj]; apply (squareStage_iff _ _).2 ((eq_div_iff epsilon_ne_zero).2 ?_)
      linear_combination -vs

theorem rational_odd_iff (k : ℤ) : RationalOddChart (k • P) ↔ Odd k :=
  (rational_chart_iff _).trans (odd_chart_iff k)

/-- All nine affine ordinates and all odd-index square roots use the rational branches
of Sun's encoding. The group operations have their values in the actual public carrier. -/
theorem extract_indices (A : Fin 9 → AffineInput) (c : ℤ) {D K S : ℝ}
    (hD : 0≤D) (hS : 0≤S) (q : (nineAffine A).doubles.Q≠0)
    (h : (nineAffine A).doubles.H≠0) (base : translatedBase (nineAffine A).doubles c≠0)
    (N : RationalOddChart (nineAffine A).doubles.N) (T : RationalOddChart (nineAffine A).doubles.T)
    (Z : RationalOddChart (nineAffine A).doubles.Z) :
    ∃! a : Labels, Consequences (nineAffine A).doubles (Sun28.multiplier D K S) c a :=
  indices_of_rational_charts A c hD hS
    ⟨q,h,base,(rational_chart_iff _).1 N,(rational_chart_iff _).1 T,(rational_chart_iff _).1 Z⟩

#print axioms squareStage_iff
#print axioms rational_chart_iff
#print axioms rational_odd_iff
#print axioms extract_indices
end
end Sun28.WitnessIndices
