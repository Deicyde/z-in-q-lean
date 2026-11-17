import AllFinitePlaces

/-! The local factor is exactly one away from the primes dividing six times the pole form. -/
open NumberField Polynomial IsDedekindDomain
namespace ZInQBlueprint.NonarchContact
open BranchHeight ContactInvariant BranchPlaces BranchDepth SexticThetaHeight
noncomputable section

/-- At a place over p, an ordinary integer coprime to p has absolute value one. -/
theorem norm_nat_unit {K : Type*} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    (w : FinitePlace K) (hw : w.maximalIdeal.asIdeal.LiesOver (rationalPrime p).asIdeal)
    (n : ℕ) (hn : ¬p ∣ n) : w (n:K)=1 := by
  let v := rationalPrime p
  let : w.maximalIdeal.asIdeal.LiesOver v.asIdeal := hw
  have hgen : Rat.HeightOneSpectrum.natGenerator v=p := by
    change (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ) v).val=p
    exact congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have hn' : (n : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have him := (Ideal.apply_mem_of_equiv_iff (f:=Rat.IsIntegralClosure.intEquiv (𝓞 ℚ))).mpr h
    rw [map_natCast] at him
    exact hn (hgen ▸ (Rat.HeightOneSpectrum.natGenerator_dvd_iff v).mpr him)
  have hm : (n : 𝓞 K) ∉ w.maximalIdeal.asIdeal := by
    simpa only [map_natCast] using (w.maximalIdeal.asIdeal.mem_of_liesOver v.asIdeal (n:𝓞 ℚ)).not.mp hn'
  rw [← FinitePlace.norm_embedding_eq w]
  simpa only [map_natCast] using (FinitePlace.norm_eq_one_iff_notMem K w.maximalIdeal (n:𝓞 K)).mpr hm

/-- Every contact depth, including every positive odd depth, is allowed if p does not divide 6G. -/
theorem supremum_away {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    {p : ℕ} [hp : Fact p.Prime] (hgood : ¬ p ∣ 6*poleNorm u) :
    letI := weight_numberField hu hδ hz
    ∀ w : FinitePlace (weightField r), w.maximalIdeal.asIdeal.LiesOver (rationalPrime p).asIdeal →
      (⨆ i : Fin 10, w (sumWeights r i))=1 := by
  let := weight_numberField hu hδ hz
  intro w hw
  apply supremum_of_unit hu hδ hr hz w
  apply norm_nat_unit w hw (denominator u)
  intro hd
  have hc : ¬ p ∣ 144*3^4*27^2 := by
    have hf : 144*3^4*27^2 ∣ (6:ℕ)^14 := by decide
    exact fun h => hgood (dvd_mul_of_dvd_left (hp.out.dvd_of_dvd_pow (h.trans hf)) _)
  rcases hp.out.dvd_or_dvd hd with h|h
  · exact hc h
  · exact hgood (dvd_mul_of_dvd_right (hp.out.dvd_of_dvd_pow h) _)

end
end ZInQBlueprint.NonarchContact
#print axioms ZInQBlueprint.NonarchContact.norm_nat_unit
#print axioms ZInQBlueprint.NonarchContact.supremum_away
