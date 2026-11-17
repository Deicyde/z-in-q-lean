import PolePeriodEndpoint

/-! The good-residue-characteristic local formula for the actual sextic gives
the denominator orders of the minimal discriminant ideal, including ramified places. -/
open AlgebraicGeometry NumberField IsDedekindDomain UniqueFactorizationMonoid
namespace ZInQBlueprint.ThetaClass
open JacobianHeight AbelianModel NormalDescent
noncomputable section
variable {K : Type} [Field K] [NumberField K]

private theorem denominator_coprime_twelve {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    (SixContact.J u).den.Coprime 12 := by
  have hu0 : u ≠ 0 := fun e => hu (e ▸ (by decide : (0 : ℚ) ∈ ZInQ.contactSet))
  by_contra h
  obtain ⟨p,hp,hd,h12⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  have large := SixContactHP.prime_den_large u hu0
    (Nat.mem_primeFactors.mpr ⟨hp,hd,(SixContact.J u).den_nz⟩)
  have h : p ∣ 2*(2*3) := h12
  rcases hp.dvd_mul.mp h with d|d
  · exact (Nat.le_of_dvd (by decide : 0 < 2) d).not_gt (by omega)
  · rcases hp.dvd_mul.mp d with d|d
    · exact (Nat.le_of_dvd (by decide : 0 < 2) d).not_gt (by omega)
    · exact (Nat.le_of_dvd (by decide : 0 < 3) d).not_gt large

/-- The rational invariant, written in lowest-term coordinates before taking an ideal valuation. -/
private theorem igusa_fraction (j : ℚ) : SixContactHP.igusaPole j =
    (j.num : ℚ)^3*(j.den : ℚ)^2 / (12*((j.num : ℚ)+(j.den : ℚ)))^5 := by
  have hd : (j.den : ℚ) ≠ 0 := by exact_mod_cast j.den_nz
  unfold SixContactHP.igusaPole
  conv_lhs => rw [← Rat.num_div_den j]
  rw [div_add_one hd]
  field_simp

/-- At every prime ideal dividing the denominator, the Igusa quotient has twice
the order of that denominator. The valuation on K is Mathlib's actual adic valuation. -/
theorem igusa_valuation_at_denominator (v : HeightOneSpectrum (𝓞 K)) {j : ℚ}
    (coprime : j.den.Coprime 12) (pole : (j.den : 𝓞 K) ∈ v.asIdeal) :
    v.valuation K ((SixContactHP.igusaPole j : ℚ) : K) = (v.intValuation (j.den : 𝓞 K))^2 := by
  have nd : IsCoprime (j.num : 𝓞 K) (j.den : 𝓞 K) := by
    simpa only [Int.cast_natCast] using (j.isCoprime_num_den.intCast (R:=𝓞 K))
  have unitNum := Ideal.IsPrime.notMem_of_isCoprime_of_mem nd.symm pole
  have unitTwelve : (12 : 𝓞 K) ∉ v.asIdeal :=
    Ideal.IsPrime.notMem_of_isCoprime_of_mem (by exact_mod_cast coprime.cast (R:=𝓞 K)) pole
  have unitSum : (j.num : 𝓞 K)+(j.den : 𝓞 K) ∉ v.asIdeal := by
    intro mem
    exact unitNum (by simpa using v.asIdeal.sub_mem mem pole)
  have numVal : v.valuation K (j.num : K) = 1 := by
    simpa using (v.valuation_eq_one_iff_notMem (K:=K)).mpr unitNum
  have sumVal : v.valuation K ((j.num : K)+(j.den : K)) = 1 := by
    simpa using (v.valuation_eq_one_iff_notMem (K:=K)).mpr unitSum
  have twelveVal : v.valuation K (12 : K) = 1 := by
    simpa only [map_ofNat] using (v.valuation_eq_one_iff_notMem (K:=K)).mpr unitTwelve
  have denVal : v.valuation K (j.den : K) = v.intValuation (j.den : 𝓞 K) := by
    simpa using v.valuation_of_algebraMap (K:=K) (j.den : 𝓞 K)
  rw [igusa_fraction]
  push_cast
  simp only [map_div₀,map_mul,map_pow,numVal,sumVal,twelveVal,denVal,one_pow,one_mul,div_one]

/-- Good-characteristic clause of the local stable-discriminant theorem, with the
invariants evaluated on the specified signed equation. Valuations are normalized
to take value one additively on a uniformizer. -/
def GoodLocalIgusa (u : ℚ) (I : Ideal (𝓞 K)) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 K), (12 : 𝓞 K) ∉ v.asIdeal →
      ((normalizedFactors I).count v.asIdeal : ℤ) =
       max 0 (-WithZero.log (v.valuation K
        (((igusaJ10 (BinaryCover.paper ℚ u false) / (igusaJ2 (BinaryCover.paper ℚ u false))^5 : ℚ) : K))))

/-- On the signed curve only the characteristic-prime-to-12 part of HP Theorem
4.5(ii) is used. Its input here is the literal Liu quotient on the rational equation. -/
theorem orders_of_local_igusa {u : ℚ} (hu : u ∉ ZInQ.contactSet) (I : Ideal (𝓞 K))
    (localFormula : GoodLocalIgusa u I) :
    ∀ P ∈ normalizedFactors (Ideal.span {((SixContact.J u).den : 𝓞 K)}),
      2*(normalizedFactors (Ideal.span {((SixContact.J u).den : 𝓞 K)})).count P =
        (normalizedFactors I).count P := by
  intro P hp
  let j := SixContact.J u
  have prime := prime_of_normalized_factor P hp
  let v : HeightOneSpectrum (𝓞 K) := ⟨P,Ideal.isPrime_of_prime prime,prime.ne_zero⟩
  let : v.asIdeal.IsPrime := v.isPrime
  have pole : (j.den : 𝓞 K) ∈ v.asIdeal := Ideal.dvd_span_singleton.mp (dvd_of_mem_normalizedFactors hp)
  have cop := denominator_coprime_twelve hu
  have unitTwelve : (12 : 𝓞 K) ∉ v.asIdeal :=
    Ideal.IsPrime.notMem_of_isCoprime_of_mem (by exact_mod_cast cop.cast (R:=𝓞 K)) pole
  have hpFormula := localFormula v unitTwelve
  rw [(paper_igusa_quotient hu).2] at hpFormula
  change ((normalizedFactors I).count v.asIdeal : ℤ) =
    max 0 (-WithZero.log (v.valuation K ((SixContactHP.igusaPole j : ℚ) : K))) at hpFormula
  have nz : (j.den : 𝓞 K) ≠ 0 := by exact_mod_cast j.den_nz
  have idealNz : Ideal.span {(j.den : 𝓞 K)} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr nz
  rw [igusa_valuation_at_denominator v cop pole,v.intValuation_eq_exp_neg_multiplicity nz,
    ← WithZero.exp_nsmul,WithZero.log_exp,two_nsmul] at hpFormula
  change 2*(normalizedFactors (Ideal.span {(j.den : 𝓞 K)})).count v.asIdeal =
    (normalizedFactors I).count v.asIdeal
  rw [v.count_normalizedFactors_eq_multiplicity idealNz]
  omega

/-- The global period identity and the classical good-characteristic Igusa
formula supply the required height data on this family. -/
structure IgusaPeriod (K : Type) [Field K] [NumberField K] (hF : GroupScheme ℚ → ℝ)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) where
  period : ThetaPeriod.SiegelPeriod
  reduced : InStrengDomain period
  discriminant : Ideal (𝓞 K)
  nonzero : discriminant ≠ ⊥
  localFormula : GoodLocalIgusa u discriminant
  heightFormula : (Module.finrank ℚ K:ℝ)*(hF (SixJacobian.jacobian hu)+Real.log Real.pi) =
    Real.log (discriminant.absNorm:ℝ)/60 -
      (Module.finrank ℚ K:ℝ)*Real.log (peterssonFactor period)/10

theorem pole_period_of_igusa {hF : GroupScheme ℚ → ℝ} {u : ℚ} {hu : u ∉ ZInQ.contactSet}
    (data : IgusaPeriod K hF hu) : Nonempty (PolePeriod K hF hu) :=
  ⟨⟨data.period,data.reduced,data.discriminant,data.nonzero,
    fun P hp => (orders_of_local_igusa hu _ data.localFormula P hp).le,data.heightFormula⟩⟩


end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.igusa_valuation_at_denominator
#print axioms ZInQBlueprint.ThetaClass.orders_of_local_igusa
#print axioms ZInQBlueprint.ThetaClass.GoodLocalIgusa
#print axioms ZInQBlueprint.ThetaClass.IgusaPeriod
#print axioms ZInQBlueprint.ThetaClass.pole_period_of_igusa
