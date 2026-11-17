import PeterssonGaussian
import JacobianDiscriminant

/-! Height comparisons on the actual rational Jacobian, with the analytic estimate discharged. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.PeriodGaussian
open ThetaPeriod ThetaQuotient JacobianHeight AbelianModel ZInQ Real
noncomputable section

private theorem finite_height (j : ℚ) :
    2*ratHeight j ≤ 3*log (j.num.natAbs:ℝ)+2*log (j.den:ℝ) := by
  by_cases hj : j = 0
  · subst j; norm_num [ratHeight]
  have pos : 0 < j.num.natAbs := Int.natAbs_pos.mpr (Rat.num_ne_zero.mpr hj)
  have hm := log_nonneg (show (1:ℝ) ≤ j.num.natAbs by exact_mod_cast pos)
  have hn := log_nonneg (show (1:ℝ) ≤ j.den by exact_mod_cast j.den_pos)
  rw [ratHeight, ← Int.cast_abs, ← Nat.cast_natAbs]
  rcases le_total (j.num.natAbs:ℝ) j.den with h|h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

private theorem log_petersson_le (Z : SiegelPeriod) (red : InStrengDomain Z) :
    log (peterssonFactor Z) ≤ log gaussianConstant := by
  have hn : 0 ≤ peterssonFactor Z := by
    unfold peterssonFactor
    exact mul_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => sq_nonneg _)))
      (pow_nonneg Z.imdet.le _)
  rcases hn.eq_or_lt with h|h
  · rw [← h, Real.log_zero]
    exact log_nonneg (by norm_num [gaussianConstant])
  · exact log_le_log h (petersson_gaussian Z red)

theorem height_of_actual_periods {K : Type} [Field K] [NumberField K]
    {hF : GroupScheme ℚ → ℝ} {u : ℚ} {hu : u ∉ contactSet} (P : JacobianPeriods K hF hu) :
    ratHeight (SixContact.J u) < 30*hF (SixJacobian.jacobian hu)+150 := by
  have arch : (∑ σ, log (peterssonFactor (P.period σ))) ≤ (Module.finrank ℚ K:ℝ)*log gaussianConstant := calc
    _ ≤ ∑ _σ : K →ₐ[ℚ] ℂ, log gaussianConstant := Finset.sum_le_sum fun σ _ => log_petersson_le _ (P.reduced σ)
    _ = _ := by simp [AlgHom.card ℚ K ℂ]
  have pos : 0 < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
  have fg := mul_le_mul_of_nonneg_left (finite_height (SixContact.J u)) pos.le
  have first : ratHeight (SixContact.J u) ≤ 30*(hF (SixJacobian.jacobian hu)+log π) + 3*log gaussianConstant := by
    apply (mul_le_mul_iff_right₀ pos).mp
    nlinarith only [fg, P.formula, arch]
  linarith only [first, log_allowance]

/-- For a curve defined over the rationals, all embeddings of a common extension have the
same complex curve. Symplectic invariance allows a single reduced period to be used when
specializing the geometric formula. -/
theorem height_of_one_period {j : ℚ} {h : ℝ} (Z : SiegelPeriod) (red : InStrengDomain Z)
    (formula : h+log π = (3*log (j.num.natAbs:ℝ)+2*log (j.den:ℝ))/60-log (peterssonFactor Z)/10) :
    ratHeight j < 30*h+150 := by
  linarith only [finite_height j,log_petersson_le Z red,formula,log_allowance]

/-- The analytic height formula can instead be applied only at the rational pole primes.
Here the finite input keeps the literal universal invariant of the signed sextic; the other
finite contributions need only be nonnegative. The complex period is chosen once. -/
theorem height_of_poles (K : Type) [Field K] [NumberField K]
    {u : ℚ} (hu : u ∉ contactSet) {h : ℝ} (Z : SiegelPeriod) (red : InStrengDomain Z)
    (S : Finset ℕ) (term : ℕ → ℝ) (contains : (SixContact.J u).den.primeFactors ⊆ S)
    (nonnegative : ∀ p ∈ S, 0 ≤ term p)
    (poles : ∀ p ∈ (SixContact.J u).den.primeFactors, paperPoleTerm K u p ≤ term p)
    (formula : (Module.finrank ℚ K:ℝ)*(h+log π) =
      (∑ p ∈ S, term p)/60 - (Module.finrank ℚ K:ℝ)*log (peterssonFactor Z)/10) :
    ratHeight (SixContact.J u) < 30*h + 150 := by
  have hu0 : u ≠ 0 := fun eq => hu (eq ▸ (by decide : (0:ℚ) ∈ contactSet))
  have at_poles (p : ℕ) (hp : p ∈ (SixContact.J u).den.primeFactors) := poles p hp
  simp only [paperPoleTerm,(paper_igusa_quotient hu).2] at at_poles
  have fin := SixContactHP.finite_log_lower K u hu0 term contains nonnegative at_poles rfl
  change (Module.finrank ℚ K:ℝ)*(2*ratHeight (SixContact.J u)) ≤ _ at fin
  have pos : 0 < (Module.finrank ℚ K:ℝ) := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
  have arch := mul_le_mul_of_nonneg_left (log_petersson_le Z red) pos.le
  have upper : ratHeight (SixContact.J u) ≤ 30*(h+log π)+3*log gaussianConstant := by
    apply (mul_le_mul_iff_right₀ pos).mp
    nlinarith only [fin,formula,arch]
  linarith only [upper,log_allowance]

theorem original_of_marking_and_periods (hF : GroupScheme ℚ → ℝ) (effective : EffectiveSurfaceHeight hF)
    (marking : ∀ (u : ℚ) (hu : u ∉ contactSet), Nonempty (MarkedAction u (SixJacobian.jacobian hu)))
    (reduction : ∀ (u : ℚ) (hu : u ∉ contactSet), GoodOutside (SixJacobian.jacobian hu)
      (HeightBudget.conductorPrimes Mult.S_mul u))
    (periods : ∀ (u : ℚ) (hu : u ∉ contactSet), ∃ (K : Type) (_ : Field K) (_ : NumberField K),
      Nonempty (JacobianPeriods K hF hu))
    (genus : OriginalRank.HigherOrderGenusCoefficient) (rank : OriginalRank.ModularSimpleZero) : FrozenTarget := by
  apply original_of_modular_height _ genus rank
  intro u hu
  obtain ⟨K,_,_,⟨P⟩⟩ := periods u hu
  have primes : ∀ p ∈ HeightBudget.conductorPrimes Mult.S_mul u, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_union.mp hp).elim (fun h => Mult.prime_of_mem_S_mul h) Nat.prime_of_mem_primeFactors
  have upper := effective _ _ primes (SixJacobian.isAbelian hu) (SixJacobian.jacobian_dimension_two hu)
    ((marking u hu).elim rationalRM_of_marked) (reduction u hu)
  change hF (SixJacobian.jacobian hu) ≤ HeightBudget.vonKaenelBudget u at upper
  linarith only [height_of_actual_periods P,upper]

end
end ZInQBlueprint.PeriodGaussian
#print axioms ZInQBlueprint.PeriodGaussian.height_of_actual_periods
#print axioms ZInQBlueprint.PeriodGaussian.height_of_poles
#print axioms ZInQBlueprint.PeriodGaussian.height_of_one_period
#print axioms ZInQBlueprint.PeriodGaussian.original_of_marking_and_periods
