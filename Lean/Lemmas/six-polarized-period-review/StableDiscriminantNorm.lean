import PeterssonGaussian
import DiscriminantHeight

/-! The absolute norm version of the one-period stable-discriminant comparison. -/
namespace ZInQBlueprint.PeriodGaussian
open ThetaPeriod JacobianHeight NumberField ZInQ Real
open UniqueFactorizationMonoid
noncomputable section

/-- It suffices to check the stable discriminant orders at the prime ideals of the
denominator. Unrelated finite primes and numerator primes impose no conditions. -/
theorem denominator_ideal_dvd {K : Type} [Field K] [NumberField K]
    (d : ℕ) (hd : d ≠ 0) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (localOrders : ∀ P ∈ normalizedFactors (Ideal.span {(d : 𝓞 K)}),
      2*(normalizedFactors (Ideal.span {(d : 𝓞 K)})).count P ≤ (normalizedFactors I).count P) :
    (Ideal.span {(d : 𝓞 K)})^2 ∣ I := by
  classical
  have hd' : Ideal.span {(d : 𝓞 K)} ≠ 0 := by
    change Ideal.span {(d : 𝓞 K)} ≠ ⊥
    simpa only [ne_eq,Ideal.span_singleton_eq_bot,Nat.cast_eq_zero] using hd
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hd') hI).mpr
  rw [normalizedFactors_pow,Multiset.le_iff_count]
  intro P
  by_cases hp : P ∈ normalizedFactors (Ideal.span {(d : 𝓞 K)})
  · simpa using localOrders P hp
  · simp [Multiset.count_eq_zero.mpr hp]

/-- The absolute ideal norm of a multiple of the square of (d) dominates d^(2[K:Q]). -/
theorem denominator_norm_lower {K : Type} [Field K] [NumberField K]
    (d : ℕ) (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) (divides : (Ideal.span {(d : 𝓞 K)})^2 ∣ I) :
    (Module.finrank ℚ K : ℝ)*(2*log (d:ℝ)) ≤ log (Ideal.absNorm I : ℝ) := by
  have dvd := map_dvd Ideal.absNorm divides
  rw [map_pow,Ideal.absNorm_span_natCast,RingOfIntegers.rank K] at dvd
  have hpos : 0 < I.absNorm := Nat.pos_of_ne_zero (mt (Ideal.absNorm_eq_zero_iff.mp) hI)
  have h := Nat.le_of_dvd hpos dvd
  by_cases hz : d = 0
  · subst d; simp; exact log_nonneg (by exact_mod_cast hpos)
  have dp : 0 < d := Nat.pos_of_ne_zero hz
  have hle : ((d:ℝ)^Module.finrank ℚ K)^2 ≤ (I.absNorm:ℝ) := by exact_mod_cast h
  have hlog := log_le_log (show 0 < ((d:ℝ)^Module.finrank ℚ K)^2 by positivity) hle
  rw [log_pow, log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  linarith only [hlog]

/-- For a rational slope the one-period HP norm formula only needs this ideal
divisibility. No finite exponents at numerator, dyadic, or triadic primes are supplied. -/
theorem height_of_stable_discriminant (K : Type) [Field K] [NumberField K]
    {u : ℚ} (hu : u ∉ contactSet) (h : ℝ) (Z : SiegelPeriod) (red : InStrengDomain Z)
    (I : Ideal (𝓞 K)) (hI : I ≠ ⊥)
    (divides : (Ideal.span {((SixContact.J u).den : 𝓞 K)})^2 ∣ I)
    (formula : (Module.finrank ℚ K:ℝ)*(h+log π) =
      log (I.absNorm:ℝ)/60 - (Module.finrank ℚ K:ℝ)*log (peterssonFactor Z)/10) :
    ratHeight (SixContact.J u) < 30*h + 150 := by
  have h0 : u ≠ 0 := fun eq => hu (eq ▸ (by decide : (0:ℚ) ∈ contactSet))
  have he : ratHeight (SixContact.J u) = log ((SixContact.J u).den:ℝ) := by
    have de : ((SixContact.J u).den:ℝ)=(PoleNorm.denominatorRoot u:ℝ)^6 := by
      exact_mod_cast PoleNorm.j_denominator u h0
    rw [de,log_pow]
    exact PoleNorm.j_height_exact u h0
  have fd := denominator_norm_lower _ I hI divides
  rw [← he] at fd
  have pos : 0 < (Module.finrank ℚ K:ℝ) := by exact_mod_cast Module.finrank_pos (R:=ℚ) (M:=K)
  have bound := petersson_gaussian Z red
  have nonneg : 0 ≤ peterssonFactor Z := by
    unfold peterssonFactor
    exact mul_nonneg (mul_nonneg (by positivity) (Finset.prod_nonneg (fun i _ => sq_nonneg _))) (pow_nonneg Z.imdet.le _)
  have arch : log (peterssonFactor Z) ≤ log gaussianConstant := by
    rcases nonneg.eq_or_lt with vp|vp
    · rw [← vp,log_zero]; exact log_nonneg (by norm_num [gaussianConstant])
    · exact log_le_log vp bound
  have arch' := mul_le_mul_of_nonneg_left arch pos.le
  have first : ratHeight (SixContact.J u) ≤ 30*(h+log π)+3*log gaussianConstant := by
    apply (mul_le_mul_iff_right₀ pos).mp
    nlinarith only [fd,formula,arch']
  linarith only [first,log_allowance]

end
end ZInQBlueprint.PeriodGaussian
#print axioms ZInQBlueprint.PeriodGaussian.denominator_ideal_dvd
#print axioms ZInQBlueprint.PeriodGaussian.denominator_norm_lower
#print axioms ZInQBlueprint.PeriodGaussian.height_of_stable_discriminant
