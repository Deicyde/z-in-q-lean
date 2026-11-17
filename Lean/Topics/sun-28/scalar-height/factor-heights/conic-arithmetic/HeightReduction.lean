import QuinticHeightBound
import ClassProjection

namespace Sun28.ConicArithmetic
open Height ZInQ ZInQ.Mult Sun28.ScalarHeight Sun28.Ordinary Sun28.ConicCovers
open Sun28.ScalarRankZero Sun28.ScalarDepth Sun28.Forward Sun28.WitnessHeight
open Sun28.FixedPreparation Sun28.ScalarLucas Sun28.WitnessIndices Sun28.IndexHeights Sun28.FactorHeights
noncomputable section
attribute [local irreducible] Sun28.Ordinary.glazerConstant24 Sun28.FixedPreparation.fixedMultiplier Sun28.ScalarDepth.floor Sun28.ScalarDepth.allowance
set_option maxRecDepth 1000
set_option maxHeartbeats 100000

/-- A height already covered by the fixed multiplier alone. -/
def heightCap : ℝ := ((fixedMultiplier:ℝ)/24-Real.log 31213)/2

private theorem basic_cap (x:ℚ) : 2*heightCap+Real.log 31213 ≤ allowance x := by
  have dv:fixedMultiplier ∣ floor x:=by unfold floor; exact Nat.dvd_lcm_left .. 
  have nn:fixedMultiplier≤floor x:=Nat.le_of_dvd (floor_pos x) dv
  have F:(fixedMultiplier:ℝ)≤floor x := Nat.cast_le.mpr nn
  have floor12:12≤(floor x:ℝ):=Nat.ofNat_le_cast.mpr (fixed_reserve.1.trans nn)
  have log1:=log_one_of_floor floor12
  have floorpos:0≤(floor x:ℝ):=Nat.cast_nonneg _
  have floorfree : (floor x:ℝ)≤(floor x:ℝ)*Real.log (floor x:ℝ):=
    le_mul_of_one_le_right floorpos log1
  unfold allowance heightCap
  linarith only [F,floorfree]

theorem point_fits {x s:ℚ} {pos:Bool} (mark:beta x*den pos s 1=num pos s 1)
    (fin:den pos s 1≠0) (small:logHeight₁ s≤heightCap) : logHeight₁ (beta x)≤allowance x :=
  by
    have m:=marked_height pos _ s mark fin
    have cap:=basic_cap x
    linarith only [m,small,cap]

/-- A further restriction on the exceptional rows. The range and the original marked
rational coordinate are retained, together with the strict lower bound on the quotient height. -/
def largePoint (pos:Bool) (x:ℚ) : Prop :=
  ∃s y:ℚ, (if pos then 4 else 0)<s ∧ ratSquare s ∧ y≠0 ∧ y^2=quintic pos s ∧
    beta x*den pos s 1=num pos s 1 ∧ heightCap<logHeight₁ s ∧
    (pos=true → ¬ Sun28.OcticResidues.imaginaryClass (-231) s)

def largeLocus (x:ℚ) : Prop :=
  (¬∃i,concentrated x i) ∨
    (positiveParameter x ∧ allowance x<2*Real.log 1199+4*Real.log x.den+4 ∧ largePoint true x) ∨
    (negativeParameter x ∧ allowance x<2*Real.log 35+2*Real.log x.den+4 ∧ largePoint false x)

theorem failure_locus {x:ℚ} (nz:x≠0) (p:parameterLocus x)
    (bad:allowance x<logHeight₁ (beta x)) : largeLocus x := by
  rcases p with nc|⟨w,ineq⟩|⟨w,ineq⟩
  · exact Or.inl nc
  · obtain ⟨s,y,rng,sq,quad,_third,yn,curve,mark⟩:=positive_point w
    have finite:den true s 1≠0:=by dsimp [den];linarith only [rng]
    refine Or.inr (Or.inl ⟨w,ineq,s,y,rng,sq,yn,curve,mark,
      lt_of_not_ge (fun small=>bad.not_ge (point_fits mark finite small)),?_⟩)
    obtain ⟨r,rs⟩:=sq
    obtain ⟨z,az⟩:=quad
    exact fun _=>Sun28.OcticResidues.negative231_excluded rng rs az
  · obtain ⟨s,y,rng,sq,yn,curve,mark⟩:=negative_point w nz
    have finite:den false s 1≠0:=by dsimp [den];positivity
    exact Or.inr (Or.inr ⟨w,ineq,s,y,rng,sq,yn,curve,mark,
      lt_of_not_ge (fun small=>bad.not_ge (point_fits mark finite small)),(fun e=>False.elim (Bool.noConfusion e))⟩)

def QuotientExceptionalScalarBound : Prop :=
  ∀ (A:Fin 9→AffineInput) (x η:ℚ), ¬(∃k:ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → HardInput x → largeLocus x →
    x∈exceptionalInputs (max x.num.natAbs x.den) → logHeight₁ (beta x)≤allowance x

theorem scalar_of_quotient_exceptions (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (est:QuotientExceptionalScalarBound) : ScalarBound := by
  apply scalar_of_parameter_exceptions descent reduction
  intro A x η ni cert hard loc box
  by_contra! bad
  have nz:x≠0:=fun eq=>ni ⟨0,by simpa using eq⟩
  exact bad.not_ge (est A x η ni cert hard (failure_locus nz loc bad) box)

end
end Sun28.ConicArithmetic
#print axioms Sun28.ConicArithmetic.point_fits
#print axioms Sun28.ConicArithmetic.failure_locus
#print axioms Sun28.ConicArithmetic.scalar_of_quotient_exceptions
