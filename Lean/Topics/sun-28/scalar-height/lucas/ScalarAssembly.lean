import ScalarCriteria
import CertificateIndices
import SupportedNumerator

namespace Sun28.ScalarLucas
open ZInQ Height Sun28.Forward Sun28.Ordinary Sun28.FixedPreparation Sun28.WitnessIndices
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.FiveMarkUnits Sun28.IndexHeights
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.MinimalConductors
noncomputable section
set_option maxRecDepth 12000
set_option maxHeartbeats 2000000

/-- The ordinary equations bound just the second Lucas coordinate; this suffices. -/
theorem integral_of_indices (A : Fin 9 → AffineInput) (x η : ℚ)
    (accepted : PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers)
    (tests : OrdinaryIndices A η) (height : logHeight₁ (beta x) ≤ scalarAllowance x) :
    ∃ k : ℤ, x=(k:ℚ) := by
  have g : 0≤glazerConstant24 := by unfold glazerConstant24; positivity
  have o : 0≤ordinary := by unfold ordinary glazerConstant24; positivity
  obtain ⟨a,e,_⟩ := extract_indices A anchor (K:=logConstant) o g accepted.q_nonzero
    accepted.h_nonzero accepted.base_nonzero accepted.odd_N accepted.odd_T accepted.odd_Z
  apply Sun28.integral_input x (a.n 0)
  by_contra wrong
  obtain ⟨zero,upper⟩ := ordinary_index_outputs A x η accepted e tests wrong
  have outside : exceptional (gamma:ℚ) smallMultipliers ⊆ oldCutoff := by
    rw [←fixed_cutoff]
    exact fun _ h => Finset.mem_union_left _ h
  have tree := tree_of_points e _ _ _ _ accepted.scalar
  have dv := scalar_product48_at_cutoff sqrt2_sq a.h (a.n 1) x gamma denominator smallMultipliers oldCutoff
    outside e.h_nonzero (by exact_mod_cast gamma_positive.ne') (ShortFormal.ordinaryCharts oldCutoff K0) tree
  have mc := (scalar_step_range fixed_multiplier_spec.2.1 a.n a.q e.q_nonzero e.anchor).1
  have big := fixed_reserve.1.trans mc
  have pos : 0 < scalarStep a.n := by omega
  have lower := lucas_coordinate_growth a.n e.z_nonzero big zero
  have sep := allowance_comparison x (Nat.le_of_dvd pos (stepFloor_dvd x e.anchor dv))
  linarith only [lower,upper,sep,height]

/-- Only the scalar cases surviving all three numerical tests need a new height estimate. -/
def RemainingScalar : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers →
    (∀ u c : ℤ, ¬ ScalarPencil.NumeratorTest x u c) →
    scalarAllowance x < denominatorEstimate x →
    scalarAllowance x < vonKanelBound (best (beta x).num (beta x).den) →
    logHeight₁ (beta x) ≤ scalarAllowance x

theorem remainder_of_pencil (allPell : HeightBudget.PublishedAllPell)
    (classes : HeightExtension.PublishedClassRegulator) (disc : QuadraticCharacterDiscriminants)
    (rest : RemainingScalar) : ScalarRemainder := by
  intro A x η ni cert denBig unitBig
  classical
  by_cases h : ∃ u c : ℤ, ScalarPencil.NumeratorTest x u c
  · obtain ⟨u,c,t⟩ := h
    have nz : x≠0 := fun e => ni ⟨0,by simpa using e⟩
    exact (ScalarPencil.of_numerator_split allPell classes disc nz t).trans (original_fits x)
  · exact rest A x η ni cert (fun u c t => h ⟨u,c,t⟩) denBig unitBig

def RemainingOrdinary : Prop :=
  ∀ (A : Fin 9 → AffineInput) (x η : ℚ), ¬(∃ k : ℤ,x=(k:ℚ)) →
    PointCertificate (nineAffine A).doubles fixedMultiplier anchor x η gamma denominator
      smallMultipliers smallMultipliers → OrdinaryIndices A η

theorem index_projection (realCurves : RealComponents.PublishedProposition72)
    (quadric : ConeCount.PublishedQuadricCount) (units : PublishedCorollary72)
    (allPell : HeightBudget.PublishedAllPell) (classes : HeightExtension.PublishedClassRegulator)
    (disc : QuadraticCharacterDiscriminants) (scalar : RemainingScalar) (ordinaryTests : RemainingOrdinary)
    (moments : PrimeValues.FirstMomentInputs) (points : GlobalDescent.DescentResidual) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ z : ℤ, x=(z:ℚ) := by
  constructor
  · intro zero
    classical
    by_contra ni
    obtain ⟨A,η,cert⟩ := (Concrete.polynomial_iff_certificate _).1 zero
    have h := scalar_after_tests units (HeightBudget.integral_of_all allPell) (HeightExtension.ordinary_regulator classes) disc (remainder_of_pencil allPell classes disc scalar)
      A x η ni cert
    exact ni (integral_of_indices A x η cert (ordinaryTests A x η ni cert) h)
  · rintro ⟨k,rfl⟩
    exact fibre_of_integer realCurves quadric moments (GlobalDescent.sections_iff_descent.mpr points) k

end
end Sun28.ScalarLucas
#print axioms Sun28.ScalarLucas.integral_of_indices
#print axioms Sun28.ScalarLucas.remainder_of_pencil
#print axioms Sun28.ScalarLucas.index_projection
