import HeightReduction

namespace Sun28.ConicArithmetic
open Height ZInQ ZInQ.Mult Sun28.ScalarHeight Sun28.Ordinary Sun28.ConicCovers
open Sun28.ScalarRankZero Sun28.ScalarDepth Sun28.Forward Sun28.WitnessHeight
open Sun28.FixedPreparation Sun28.ScalarLucas Sun28.WitnessIndices Sun28.IndexHeights Sun28.FactorHeights
open Sun28.OcticResidues
noncomputable section
attribute [local irreducible] Sun28.Ordinary.glazerConstant24 Sun28.FixedPreparation.fixedMultiplier Sun28.ScalarDepth.floor Sun28.ScalarDepth.allowance
set_option maxRecDepth 1000
set_option maxHeartbeats 100000

/-- The two quadratic components left by the positive quintic's fake two-cover descent,
at a point having the three required rational root components. -/
def PositiveSelmerSelection : Prop :=
  ∀ s y:ℚ, 4<s → ratSquare s → ratSquare (7*(s-4)) → ratSquare (16*s-15) →
    y≠0 → y^2=quintic true s → imaginaryClass (-231) s ∨ imaginaryClass (-42) s

theorem positive_selected {s y:ℚ} (sel:PositiveSelmerSelection) (rng:4<s)
    (sq:ratSquare s) (quad:ratSquare (7*(s-4))) (third:ratSquare (16*s-15))
    (yn:y≠0) (curve:y^2=quintic true s) : imaginaryClass (-42) s := by
  obtain ⟨r,rs⟩:=sq
  obtain ⟨z,zs⟩:=quad
  exact (sel s y rng ⟨r,rs⟩ ⟨z,zs⟩ third yn curve).resolve_left (negative231_excluded rng rs zs)

/-- A selected positive quotient point with its literal marked beta and exceptional height. -/
def selectedPositivePoint (x:ℚ) : Prop :=
  ∃s y:ℚ, 4<s ∧ ratSquare s ∧ ratSquare (7*(s-4)) ∧ ratSquare (16*s-15) ∧
    y≠0 ∧ y^2=quintic true s ∧ beta x*den true s 1=num true s 1 ∧
    heightCap<logHeight₁ s ∧ imaginaryClass (-42) s

def selectedLocus (x:ℚ) : Prop :=
  (¬∃i,concentrated x i) ∨
    (positiveParameter x ∧ allowance x<2*Real.log 1199+4*Real.log x.den+4 ∧ selectedPositivePoint x) ∨
    (negativeParameter x ∧ allowance x<2*Real.log 35+2*Real.log x.den+4 ∧ largePoint false x)

theorem selected_failure_locus (sel:PositiveSelmerSelection) {x:ℚ} (nz:x≠0) (p:parameterLocus x)
    (bad:allowance x<logHeight₁ (beta x)) : selectedLocus x := by
  rcases failure_locus nz p bad with notconc|⟨w,ineq,_point⟩|⟨w,ineq,point⟩
  · exact Or.inl notconc
  · obtain ⟨s,y,rng,sq,quad,third,yn,curve,mark⟩:=positive_point w
    have fin:den true s 1≠0:=by dsimp [den];linarith only [rng]
    exact Or.inr (Or.inl ⟨w,ineq,s,y,rng,sq,quad,third,yn,curve,mark,
      lt_of_not_ge (fun h=>bad.not_ge (point_fits mark fin h)),positive_selected sel rng sq quad third yn curve⟩)
  · exact Or.inr (Or.inr ⟨w,ineq,point⟩)

def SelectedExceptionalScalarBound : Prop :=
  ∀ (A:Fin 9→AffineInput) (x η:ℚ), ¬(∃k:ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → HardInput x → selectedLocus x →
    x∈exceptionalInputs (max x.num.natAbs x.den) → logHeight₁ (beta x)≤allowance x

theorem scalar_of_selected_exceptions (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (sel:PositiveSelmerSelection) (est:SelectedExceptionalScalarBound) : ScalarBound := by
  apply scalar_of_parameter_exceptions descent reduction
  intro A x η ni cert hard loc box
  by_contra! bad
  have nz:x≠0:=fun eq=>ni ⟨0,by simpa using eq⟩
  exact bad.not_ge (est A x η ni cert hard (selected_failure_locus sel nz loc bad) box)

end
end Sun28.ConicArithmetic
#print axioms Sun28.ConicArithmetic.positive_selected
#print axioms Sun28.ConicArithmetic.selected_failure_locus
#print axioms Sun28.ConicArithmetic.scalar_of_selected_exceptions
