import DiscrepancyStage
import NumeratorStage
import RelativeScales

/-! Actual ordinary elliptic certificates, with separate tests before and after the Lucas equation. -/
namespace Sun28.IndexHeights
open ZInQ ZInQ.Mult Sun28.Ordinary Sun28.Forward Sun28.ScalarHeight Sun28.WitnessIndices
open Sun28.FixedPreparation Sun28.WitnessHeight Height
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 2500000

/-- The numerator test is needed only on the Lucas locus. The scalar bound enters elsewhere. -/
def StageTests (n : Fin 4→ℤ) (U : ℕ) : Prop :=
  (lucas (n 1) (n 2) (n 3)≠0 → LucasTest n U) ∧
  (lucas (n 1) (n 2) (n 3)=0 → NumeratorTest n U)

/-- For a fixed tuple all labels are characterized by the point identities. -/
def OrdinaryIndices (A : Fin 9→AffineInput) (η : ℚ) : Prop :=
  ∀ a : Labels, Represents (nineAffine A).doubles fixedMultiplier a →
    StageTests a.n (unionRadical oldCutoff (slope (nineAffine A).doubles η))

theorem certificate_products (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) {a : Labels}
    (e : Consequences (nineAffine A).doubles fixedMultiplier anchor a) :
    let U:=unionRadical oldCutoff (slope (nineAffine A).doubles η)
    (U:ℤ)^64∣lucas (a.n 1) (a.n 2) (a.n 3) ∧ U^16∣(beta x-a.n 0).num.natAbs := by
  let w := (nineAffine A).doubles
  let t:=slope w η
  have outside := commonCutoff_outside anchor_nonzero (gamma:ℚ) smallMultipliers smallMultipliers
  rw [fixed_cutoff] at outside
  have tests : ∀ i, let s:=pointScale w fixedMultiplier i
      testTrace sqrt2_sq conjugation anchor a.h a.n a.m (beta x) (s^2) (t i)≠0 ∧
      polePredicate smallMultipliers (poleArgument sqrt2_sq conjugation anchor a.h a.n a.m (beta x) (s^2) (t i)) :=
    fun i => (ordinaryAccepted_iff e ..).1 (accepted.ordinary i)
  have prod := three_marked_products sqrt2_sq conjugation conjugation_nontrivial anchor a.h a.n a.m
    (beta x) (pointScale w fixedMultiplier) t smallMultipliers oldCutoff e.h_nonzero e.base_nonzero outside
    (ShortFormal.ordinaryCharts oldCutoff K0) accepted.scale_guard tests
  exact union_discrepancies oldCutoff t _ _ prod

theorem ordinary_index_outputs (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) {a : Labels}
    (e : Consequences (nineAffine A).doubles fixedMultiplier anchor a)
    (tests : OrdinaryIndices A η) (wrong : beta x≠(a.n 0:ℚ)) :
    lucas (a.n 1) (a.n 2) (a.n 3)=0 ∧
    Real.log |(a.n 2:ℝ)| ≤ logConstant+3*logHeight₁ (beta x) := by
  obtain ⟨divΔ,divJ⟩:=certificate_products A x η accepted e
  obtain ⟨first,second⟩:=tests a e.represented
  have eqn : lucas (a.n 1) (a.n 2) (a.n 3)=0 := by
    by_contra nz
    exact nz (discrepancy_zero a.n a.q e.q_nonzero e.anchor divΔ (first nz))
  have live : a.n 2≠0 := by obtain ⟨k,h⟩:=e.odd 2;omega
  exact ⟨eqn,numerator_log a.n (beta x) wrong live divJ (second eqn)⟩

theorem of_index_size (n : Fin 4→ℤ) (U : ℕ)
    (size : (indexSize n)^2 ≤ ordinary*(U:ℝ)^24) : StageTests n U := by
  have t1 : 1≤ indexSize n := one_le_indexSize n
  have N : |(n 0:ℝ)|≤ indexSize n:=abs_first_le_indexSize _
  have T : |(n 2:ℝ)|≤ indexSize n:=by simp [indexSize]
  have old : tripleSize n≤ indexSize n:=by
    simp only [tripleSize,indexSize]
    exact max_le (le_max_left ..) ((le_max_right ..).trans (le_max_right ..))
  have D0 : 0≤ordinary:=by unfold ordinary glazerConstant24;positivity
  constructor
  · intro _
    refine Or.inl ((pow_le_pow_left₀ (show 0≤tripleSize n from zero_le_one.trans (le_max_left ..)) old 2).trans ?_)
    exact size.trans (by nlinarith only [D0])
  · intro _
    unfold NumeratorTest
    have cube:=pow_le_pow_left₀ (by positivity : 0≤1+|(n 0:ℝ)|)
      (show 1+|(n 0:ℝ)|≤2*indexSize n by linarith) 3
    have prod:=mul_le_mul cube T (abs_nonneg _) (by have b0:0≤ indexSize n:=zero_le_one.trans t1; positivity : (0:ℝ)≤(2*indexSize n)^3)
    have sq:=pow_le_pow_left₀ (sq_nonneg _) size 2
    have nonneg:=mul_nonneg (sq_nonneg ordinary) (show (0:ℝ)≤(U:ℝ)^48 by positivity)
    nlinarith only [prod,sq,nonneg]

/-- The tested geometric quantity depends on the elliptic points alone. -/
def IntrinsicBudget (A : Fin 9→AffineInput) (η : ℚ) : Prop :=
  hK0 (rootProduct (nineAffine A).doubles fixedMultiplier)+3*Real.log 7+Real.log 676/3 ≤
    ordinary*(unionRadical oldCutoff (slope (nineAffine A).doubles η):ℝ)^24

/-- The height of two ratios has no dependence on the common scalar η. -/
def RatioBudget (A : Fin 9→AffineInput) (η : ℚ) : Prop :=
  ratioHeight (slope (nineAffine A).doubles η)+10 ≤
    ordinary*(unionRadical oldCutoff (slope (nineAffine A).doubles η):ℝ)^24

theorem of_intrinsic (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) (h : IntrinsicBudget A η) : OrdinaryIndices A η := by
  intro a rep
  have o1 : 0≤ordinary:=by unfold ordinary glazerConstant24;positivity
  have g : 0≤glazerConstant24:=by unfold glazerConstant24;positivity
  obtain ⟨b,e,_⟩:=extract_indices A anchor (K:=logConstant) o1 g
    accepted.q_nonzero accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  have same:=rep.unique e.represented
  subst b
  apply of_index_size _ _ 
  have bound:=product_bound a.n e.odd
  rw [rootProduct_eq rep] at bound
  exact bound.trans h

theorem of_ratios (A : Fin 9→AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers) (h : RatioBudget A η) : OrdinaryIndices A η := by
  intro a rep
  have o1 : 0≤ordinary:=by unfold ordinary glazerConstant24;positivity
  have g : 0≤glazerConstant24:=by unfold glazerConstant24;positivity
  obtain ⟨b,e,_⟩:=extract_indices A anchor (K:=logConstant) o1 g
    accepted.q_nonzero accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  have same:=rep.unique e.represented
  subst b
  have nz : η≠0 := by
    rintro rfl
    have z := (accepted.scale_guard 0).1
    rw [mul_zero] at z
    exact z (by simp [marks])
  apply of_index_size _ _ 
  have bound:=ratio_bound a.n e.odd nz
  rw [rootProduct_eq rep] at bound
  exact bound.trans h

/-- Sun’s original maximum-slope bound implies the intrinsic ratio test on the unchanged polynomial. -/
theorem ratios_of_max (A : Fin 9→AffineInput) (η : ℚ) (j : Fin 3)
    (largest : ∀ i,logHeight₁ (slope (nineAffine A).doubles η i)≤logHeight₁ (slope (nineAffine A).doubles η j))
    (previous : unionHeight (slope (nineAffine A).doubles η) j) : RatioBudget A η := by
  let t:=slope (nineAffine A).doubles η
  let U:ℝ:=unionRadical oldCutoff t
  have one : 1≤U := by dsimp [U]; exact_mod_cast Nat.succ_le_of_lt (union_pos oldCutoff t)
  have cost:=ratio_le_max t largest
  change logHeight₁ (t j)≤fiveHeightConstant oldCutoff*U^24 at previous
  change ratioHeight t+10≤ordinary*U^24
  have op : ordinary=11+(3/2)*fiveHeightConstant oldCutoff := by
    rw [←fixed_coefficients.2]
    unfold ordinaryCoefficient ordinaryConstant
    ring
  rw [op]
  nlinarith only [cost,previous,one_le_pow₀ one (n:=24)]

end
end Sun28.IndexHeights
#print axioms Sun28.IndexHeights.certificate_products
#print axioms Sun28.IndexHeights.ordinary_index_outputs
#print axioms Sun28.IndexHeights.of_index_size
#print axioms Sun28.IndexHeights.of_intrinsic
#print axioms Sun28.IndexHeights.of_ratios
#print axioms Sun28.IndexHeights.ratios_of_max
