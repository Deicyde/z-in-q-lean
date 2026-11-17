import PointGroups
import ExceptionalProjection

namespace Sun28.ScalarRankZero
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open Sun28.FactorHeights
open ZInQ ZInQ.Mult Height Sun28.Ordinary Sun28.Forward Sun28.FixedPreparation
open Sun28.WitnessHeight Sun28.ScalarLucas Sun28.ScalarHeight Sun28.WitnessIndices
open Sun28.IndexHeights Sun28.ScalarDepth
noncomputable section

private def roots (j:Fin 2) (i:Fin 3) : ℚ := ![0,-(m j:ℚ),-(n j:ℚ)] i

private theorem roots_good (j:Fin 2) (i:Fin 3) :
    (curve (a j) (b j)).toAffine.Nonsingular (roots j i) 0 := by
  rw [WeierstrassCurve.Affine.nonsingular_iff',WeierstrassCurve.Affine.equation_iff]
  fin_cases j <;> fin_cases i <;> norm_num [roots,curve,a,b,m,n]

private def mark (j:Fin 2) (i:Fin 4) : Points j :=
  ![0,Point.some (roots j 0) 0 (roots_good j 0),Point.some (roots j 1) 0 (roots_good j 1),
      Point.some (roots j 2) 0 (roots_good j 2)] i

private theorem marks_injective (j:Fin 2) : Function.Injective (mark j) := by
  let loc : Points j→Option ℚ
    | .zero=>none
    | .some t _ _=>Option.some t
  have inj : Function.Injective (fun i=>loc (mark j i)) := by
    fin_cases j <;> decide
  exact fun _ _ h=>inj (congrArg loc h)

/-- On both curves the identity and the three rational points with ordinate zero exhaust the group. -/
theorem all_points (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (j:Fin 2) (P:Points j) : ∃i:Fin 4, mark j i=P := by
  obtain ⟨emb⟩:=embeds_in_four descent reduction j
  have sur:Function.Surjective (fun i=>emb (mark j i)) :=
    Finite.surjective_of_injective (emb.injective.comp (marks_injective j))
  obtain ⟨i,h⟩:=sur (emb P)
  exact ⟨i,emb.injective h⟩

theorem no_affine_nonzero (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (j:Fin 2) (X:ℚ) : ¬elliptic (m j:ℚ) (n j:ℚ) X := by
  rintro ⟨Y,yn,eq⟩
  have valid:(curve (a j) (b j)).toAffine.Nonsingular X Y := by
    rw [WeierstrassCurve.Affine.nonsingular_iff',WeierstrassCurve.Affine.equation_iff]
    constructor
    · simp [curve,a,b] at *
      linear_combination eq
    · right;simp [curve,yn]
  obtain ⟨i,mk⟩:=all_points descent reduction j (.some X Y valid)
  let ordinate : Points j→ℚ
    | .zero=>0
    | .some _ y _=>y
  have hz (k:Fin 4) : ordinate (mark j k)=0 := by fin_cases k <;> rfl
  exact yn ((congrArg ordinate mk).symm.trans (hz i))

theorem no_elliptic_alternatives (descent:TwoIsogenyRank) (reduction:OddGoodReduction) (x:ℚ) :
    (¬elliptic 4 6 (4*x^2)) ∧ (¬elliptic 64 439 (64*x^2)) :=
  ⟨no_affine_nonzero descent reduction 0 _,no_affine_nonzero descent reduction 1 _⟩

def reducedLocus (x:ℚ) : Prop :=
  (¬∃i,concentrated x i) ∨
    (conics x 2 1 1 ∧ allowance x < 2*Real.log 1199+4*Real.log x.den+4) ∨
    (conics x 14 (-35) 7 ∧ allowance x < 2*Real.log 35+2*Real.log x.den+4)

/-- The scalar obligation now has only the unconcentrated locus and two denominator-sensitive conic branches. -/
theorem remaining_iff (descent:TwoIsogenyRank) (reduction:OddGoodReduction) (x:ℚ) :
    remainingLocus x ↔ reducedLocus x := by
  obtain ⟨h,k⟩:=no_elliptic_alternatives descent reduction x
  simp [remainingLocus,reducedLocus,h,k]

def ReducedExceptionalScalarBound : Prop :=
  ∀ (A:Fin 9→AffineInput) (x η:ℚ), ¬(∃k:ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → HardInput x → reducedLocus x →
    x∈exceptionalInputs (max x.num.natAbs x.den) → logHeight₁ (beta x)≤allowance x

theorem exceptional_of_reduced (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (reduced:ReducedExceptionalScalarBound) : ExceptionalScalarBound := by
  intro A x η ni cert hard loc box
  exact reduced A x η ni cert hard ((remaining_iff descent reduction x).mp loc) box

theorem scalar_of_reduced_exceptions (descent:TwoIsogenyRank) (reduction:OddGoodReduction)
    (reduced:ReducedExceptionalScalarBound) : ScalarBound :=
  scalar_of_exceptions (exceptional_of_reduced descent reduction reduced)


end
end Sun28.ScalarRankZero
#print axioms Sun28.ScalarRankZero.all_points
#print axioms Sun28.ScalarRankZero.no_affine_nonzero
#print axioms Sun28.ScalarRankZero.no_elliptic_alternatives
#print axioms Sun28.ScalarRankZero.remaining_iff
#print axioms Sun28.ScalarRankZero.exceptional_of_reduced
#print axioms Sun28.ScalarRankZero.scalar_of_reduced_exceptions
