import ScalarBudget
import TwoCurves

namespace Sun28.ScalarLucas
open ZInQ Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices Sun28.FixedPreparation
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.FiveMarkUnits Height
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

/-- Only the arithmetic after the Lucas equation uses the scalar estimate. -/
theorem integral_of_allowance (A : Fin 9 → AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (j : Fin 3) (largest : ∀ i, logHeight₁ (slope (nineAffine A).doubles η i)≤
      logHeight₁ (slope (nineAffine A).doubles η j))
    (ordinaryHeight : unionHeight (slope (nineAffine A).doubles η) j)
    (scalarHeight : logHeight₁ (beta x) ≤ scalarAllowance x) : ∃ k : ℤ, x=(k:ℚ) := by
  let w := (nineAffine A).doubles
  let M := fixedMultiplier
  let C := rootProduct w M
  let t := slope w η
  have gl : 0≤glazerConstant24 := by unfold glazerConstant24; positivity
  have o1 : 1≤ordinary := by
    have f := le_max_left (1:ℝ) (glazerConstant24*(∏ p∈extraPrimes oldCutoff oldCutoff,(p:ℝ))^24+Real.log 3)
    change 1≤fiveHeightConstant oldCutoff at f
    rw [←fixed_coefficients.2]
    unfold ordinaryCoefficient ordinaryConstant
    linarith
  obtain ⟨a,e,_⟩ := extract_indices A anchor (K:=logConstant) (zero_le_one.trans o1) gl
    accepted.q_nonzero accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  change Consequences w M anchor a at e
  have en : η≠0 := by
    rintro rfl
    have z := (accepted.scale_guard 0).1
    rw [mul_zero] at z
    exact z (by simp [marks])
  have coords : coordinateProduct a.n=C := rootProduct_eq e.represented
  have scale : ∀ H : ℝ, 1≤H → (∀ i,logHeight₁ (t i)≤H) → (indexSize a.n)^2≤(3/2)*H+10 := by
    change ∀ H : ℝ, 1≤H → (∀ i,logHeight₁ ((scaleRoot C.re C.im i)^2*η)≤H) → _
    rw [←coords]
    exact three_scales a.n e.odd η en
  have outside := commonCutoff_outside anchor_nonzero (gamma:ℚ) smallMultipliers smallMultipliers
  rw [fixed_cutoff] at outside
  have tests : ∀ i, let s:=pointScale w M i
      testTrace sqrt2_sq conjugation anchor a.h a.n a.m (beta x) (s^2) (t i)≠0 ∧
      polePredicate smallMultipliers (poleArgument sqrt2_sq conjugation anchor a.h a.n a.m (beta x) (s^2) (t i)) :=
    fun i => (ordinaryAccepted_iff e ..).1 (accepted.ordinary i)
  have prod := three_marked_products sqrt2_sq conjugation conjugation_nontrivial anchor a.h a.n a.m
    (beta x) (pointScale w M) t smallMultipliers oldCutoff e.h_nonzero e.base_nonzero outside
    (ShortFormal.ordinaryCharts oldCutoff K0) accepted.scale_guard tests
  obtain ⟨ord,num⟩ := ordinary_of_union oldCutoff t a.n (beta x)
    (le_max_left _ _) (by norm_num : (0:ℝ)≤3/2) (by norm_num : (0:ℝ)≤10)
    scale j largest ordinaryHeight prod
  change lucas (a.n 1) (a.n 2) (a.n 3)≠0 → (indexSize a.n)^2≤ordinaryCoefficient oldCutoff*_ at ord
  change beta x ≠ (a.n 0:ℚ) → (indexSize a.n)^2≤ordinaryCoefficient oldCutoff*_ at num
  rw [fixed_coefficients.2] at ord num
  have enlar : exceptional (gamma:ℚ) smallMultipliers ⊆ oldCutoff := by
    rw [←fixed_cutoff]
    exact fun _ h => Finset.mem_union_left _ h
  have tree := tree_of_points e _ _ _ _ accepted.scalar
  have dv := scalar_product48_at_cutoff sqrt2_sq a.h (a.n 1) x gamma denominator smallMultipliers oldCutoff
    enlar e.h_nonzero (by exact_mod_cast gamma_positive.ne') (ShortFormal.ordinaryCharts oldCutoff K0) tree
  obtain ⟨mc,_,size,_⟩ := scalar_step_range fixed_multiplier_spec.2.1 a.n a.q e.q_nonzero e.anchor
  have mcR : (fixedMultiplier:ℝ)≤(scalarStep a.n:ℝ) := by exact_mod_cast mc
  have z := (actual_cutoff (hβ:=0) o1 gl a.n mcR size ord
    (mul_nonneg gl (Real.sqrt_nonneg _))).1
  have lower := scalar_lucas_growth a.n e.z_nonzero (fixed_reserve.1.trans mc) z
  have floorDv := stepFloor_dvd x e.anchor dv
  have stepPos : 0<scalarStep a.n := by exact Nat.lt_of_lt_of_le (by have := fixed_reserve.1; omega) mc
  have split := allowance_comparison x (Nat.le_of_dvd stepPos floorDv)
  have equal : beta x=(a.n 0:ℚ) := by
    by_contra ne
    have logB := ordinary_log_height (beta x) (a.n 0) (one_le_indexSize a.n)
      (abs_first_le_indexSize a.n) o1 ne (num ne)
    change Real.log (indexSize a.n)≤logConstant+3*logHeight₁ (beta x) at logB
    linarith only [logB,scalarHeight,split,lower]
  exact Sun28.integral_input x (a.n 0) equal

/-- Both inequalities are requested only at accepted nonintegral tuples. -/
structure AllowanceHeight : Prop where
  scalar : ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → logHeight₁ (beta x) ≤ scalarAllowance x
  ordinary : ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ, x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers →
    let t := slope (nineAffine A).doubles η
    ∃ j, (∀ i,logHeight₁ (t i)≤logHeight₁ (t j)) ∧ unionHeight t j

theorem integral_of_allowance_height (height : AllowanceHeight) (x : ℚ)
    (zero : ∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) : ∃ k : ℤ, x=(k:ℚ) := by
  classical
  by_contra nonintegral
  obtain ⟨A,η,accepted⟩ := (Concrete.polynomial_iff_certificate _).1 zero
  obtain ⟨j,mx,h⟩ := height.ordinary A x η nonintegral accepted
  exact nonintegral (integral_of_allowance A x η accepted j mx h (height.scalar A x η nonintegral accepted))

theorem allowance_of_two_loci (prev : TwoLocusHeight) : AllowanceHeight := by
  constructor
  · intro A x η nonint accepted
    exact (prev.scalar A x η nonint accepted).trans (original_fits x)
  · intro A x η nonint accepted
    let t := slope (nineAffine A).doubles η
    have lift := fun i => ordinary_coordinates (t i) (accepted.scale_guard i).1
    choose z v nz nv zq curve sets using lift
    obtain ⟨j,mx,h⟩ := prev.ordinary A x η nonint accepted z v (fun i=>⟨nz i,nv i,zq i,curve i⟩)
    have same : ordinaryFieldUnion z v=contactUnion oldCutoff t := by
      unfold ordinaryFieldUnion contactUnion
      simp only [sets]
    rw [same] at h
    exact ⟨j,mx,h⟩

theorem allowance_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (height : AllowanceHeight)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalDescent.DescentResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  refine ⟨integral_of_allowance_height height x,?_⟩
  rintro ⟨k,rfl⟩
  exact fibre_of_integer realCurves quadric moments (GlobalDescent.sections_iff_descent.mpr points) k

end
end Sun28.ScalarLucas
#print axioms Sun28.ScalarLucas.integral_of_allowance
#print axioms Sun28.ScalarLucas.integral_of_allowance_height
#print axioms Sun28.ScalarLucas.allowance_of_two_loci
#print axioms Sun28.ScalarLucas.allowance_projection
