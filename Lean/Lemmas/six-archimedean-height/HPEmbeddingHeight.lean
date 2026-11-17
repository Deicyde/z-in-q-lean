import HPPrimitiveProduct
import IgusaIdealOrders

/-! The height bound only consumes the denominator primes and an upper bound
on the archimedean average. The average is taken over every complex embedding. -/
open AlgebraicGeometry NumberField
namespace ZInQBlueprint.ArchimedeanHeight
open ThetaPeriod JacobianHeight PeriodGaussian AbelianModel NormalDescent ThetaClass ZInQ Real
noncomputable section
variable {K : Type} [Field K] [NumberField K]

theorem arch_log_upper (Z : SiegelPeriod) (red : InStrengDomain Z) :
    log (peterssonFactor Z) ≤ log gaussianConstant := by
  have hn : 0 ≤ peterssonFactor Z := by
    unfold peterssonFactor
    exact mul_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => sq_nonneg _)))
      (pow_nonneg Z.imdet.le _)
  rcases hn.eq_or_lt with h|h
  · rw [← h, log_zero]
    exact log_nonneg (by norm_num [gaussianConstant])
  · exact log_le_log h (petersson_gaussian _ red)

theorem embedding_sum_upper (Z : (K →ₐ[ℚ] ℂ) → SiegelPeriod) (red : ∀ σ, InStrengDomain (Z σ)) :
    (∑ σ, log (peterssonFactor (Z σ))) ≤ (Module.finrank ℚ K : ℝ)*log gaussianConstant := calc
  _ ≤ ∑ _σ : K →ₐ[ℚ] ℂ, log gaussianConstant :=
    Finset.sum_le_sum fun σ _ => arch_log_upper _ (red σ)
  _ = _ := by simp [AlgHom.card ℚ K ℂ]

/-- A one-sided inequality for the actual stable height, with no period argument. -/
def normFloor (I : Ideal (𝓞 K)) (h : ℝ) : Prop :=
  log (I.absNorm : ℝ)/60 - (Module.finrank ℚ K:ℝ)*log gaussianConstant/10 ≤
    (Module.finrank ℚ K:ℝ)*(h+log π)

theorem floor_of_embeddings (I : Ideal (𝓞 K)) (h : ℝ)
    (Z : (K →ₐ[ℚ] ℂ) → SiegelPeriod) (red : ∀ σ, InStrengDomain (Z σ))
    (formula : log (I.absNorm:ℝ)/60 - (∑ σ, log (peterssonFactor (Z σ)))/10 ≤
      (Module.finrank ℚ K:ℝ)*(h+log π)) : normFloor I h := by
  exact (sub_le_sub_left (div_le_div_of_nonneg_right (embedding_sum_upper Z red)
    (by norm_num : (0:ℝ) ≤ 10)) _).trans formula

/-- Only the orders at the prime ideals over the invariant denominator enter. -/
theorem height_of_ideal_floor {u : ℚ} (hu : u ∉ contactSet) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (divides : (Ideal.span {((SixContact.J u).den : 𝓞 K)})^2 ∣ I) {h : ℝ} (lower : normFloor I h) :
    ratHeight (SixContact.J u) < 30*h+150 := by
  have finite := denominator_norm_lower _ I hI divides
  have h0 : u ≠ 0 := fun eq => hu (eq ▸ (by decide : (0:ℚ) ∈ contactSet))
  have he : ratHeight (SixContact.J u) = log ((SixContact.J u).den:ℝ) := by
    have de : ((SixContact.J u).den:ℝ)=(PoleNorm.denominatorRoot u:ℝ)^6 := by
      exact_mod_cast PoleNorm.j_denominator u h0
    rw [de,log_pow]
    exact PoleNorm.j_height_exact u h0
  rw [← he] at finite
  have pos : 0 < (Module.finrank ℚ K:ℝ) := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
  unfold normFloor at lower
  have first : ratHeight (SixContact.J u) ≤ 30*(h+log π)+3*log gaussianConstant := by
    apply (mul_le_mul_iff_right₀ pos).mp
    linarith only [finite,lower]
  linarith only [first,log_allowance]

theorem height_of_norm_floor {u : ℚ} (hu : u ∉ contactSet) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (localFormula : GoodLocalIgusa u I) {h : ℝ} (lower : normFloor I h) :
    ratHeight (SixContact.J u) < 30*h+150 :=
  height_of_ideal_floor hu I hI (denominator_ideal_dvd _ (SixContact.J u).den_nz I hI
    (fun P hp => (orders_of_local_igusa hu I localFormula P hp).le)) lower

/-- Application of the printed archimedean sum to the same rational Jacobian and
the same discriminant ideal as the good-characteristic finite formula. -/
theorem rational_jacobian_height {u : ℚ} (hu : u ∉ contactSet) (hF : GroupScheme ℚ → ℝ)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (localFormula : GoodLocalIgusa u I)
    (Z : (K →ₐ[ℚ] ℂ) → SiegelPeriod) (red : ∀ σ, InStrengDomain (Z σ))
    (formula : (Module.finrank ℚ K:ℝ)*(hF (SixJacobian.jacobian hu)+log π) =
      log (I.absNorm:ℝ)/60 - (∑ σ, log (peterssonFactor (Z σ)))/10) :
    ratHeight (SixContact.J u) < 30*hF (SixJacobian.jacobian hu)+150 :=
  height_of_norm_floor hu I hI localFormula (floor_of_embeddings I _ Z red formula.ge)

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.embedding_sum_upper
#print axioms ZInQBlueprint.ArchimedeanHeight.floor_of_embeddings
#print axioms ZInQBlueprint.ArchimedeanHeight.height_of_ideal_floor
#print axioms ZInQBlueprint.ArchimedeanHeight.height_of_norm_floor
#print axioms ZInQBlueprint.ArchimedeanHeight.rational_jacobian_height
