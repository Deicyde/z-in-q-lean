import SelectedOrdinaryPoints
import ZInQKernel.Multiplication.Completeness.SelectedReduction

/-! Identify the prime of the Euclidean model ℤ[√2] with the corresponding
prime of the Mathlib ring of integers, including its valuation normalization. -/
namespace Sun28.SelectedTrace
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Forward
open NumberField IsDedekindDomain WithZero
open scoped NumberField
noncomputable section

private def idealEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R≃+*S) : Ideal R ≃+* Ideal S :=
  RingEquiv.ofRingHom (Ideal.mapHom e.toRingHom) (Ideal.mapHom e.symm.toRingHom)
    (RingHom.ext fun I => by simp [Ideal.map_map]) (RingHom.ext fun I => by simp [Ideal.map_map])

private theorem map_intValuation {R S : Type*} [CommRing R] [IsDedekindDomain R]
    [CommRing S] [IsDedekindDomain S] (e : R≃+*S) (v : HeightOneSpectrum R) (x : R) :
    ((HeightOneSpectrum.equivOfRingEquiv e) v).intValuation (e x)=v.intValuation x := by
  by_cases z : x=0
  · simp [z]
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ ((map_ne_zero_iff e e.injective).mpr z),
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ z]
  have eIdeal : ((HeightOneSpectrum.equivOfRingEquiv e) v).asIdeal=(idealEquiv e) v.asIdeal :=
    (Ideal.map_comap_of_equiv e).symm
  have principal : Ideal.span {e x}=(idealEquiv e) (Ideal.span {x}) := by
    change _=Ideal.map e (Ideal.span {x}); rw [Ideal.map_span,Set.image_singleton]
  rw [eIdeal,principal,multiplicity_map_eq (idealEquiv e)]

def integerEquiv : Zs ≃+* 𝓞 K0 := (IsIntegralClosure.equiv ℤ Zs K0 (𝓞 K0)).toRingEquiv

theorem coe_integerEquiv (x : Zs) : algebraMap (𝓞 K0) K0 (integerEquiv x)=algebraMap Zs K0 x :=
  IsIntegralClosure.algebraMap_equiv ℤ Zs K0 (𝓞 K0) x

def selectedPlace (π : Zs) (hπ : Prime π) : HeightOneSpectrum (𝓞 K0) :=
  (HeightOneSpectrum.equivOfRingEquiv integerEquiv) (primeSpec π hπ)

/-- Both normalizations agree on the entire fraction field, with zero at infinite order. -/
theorem selectedPlace_order {π : Zs} (hπ : Prime π) :
    discreteOrder ((selectedPlace π hπ).valuation K0) = vP π hπ := by
  let v:=primeSpec π hπ
  let w:=selectedPlace π hπ
  have integr (a : Zs) : w.valuation K0 (algebraMap Zs K0 a)=v.valuation K0 (algebraMap Zs K0 a) :=
    calc
      _ = w.valuation K0 (algebraMap (𝓞 K0) K0 (integerEquiv a)) := congrArg (w.valuation K0) (coe_integerEquiv a).symm
      _ = w.intValuation (integerEquiv a) := w.valuation_of_algebraMap (K:=K0) (integerEquiv a)
      _ = v.intValuation a := map_intValuation integerEquiv v a
      _ = v.valuation K0 (algebraMap Zs K0 a) := (v.valuation_of_algebraMap (K:=K0) a).symm
  have eq : (selectedPlace π hπ).valuation K0=(primeSpec π hπ).valuation K0 := by
    apply Valuation.ext
    intro x
    obtain ⟨a,b,_,eq⟩ := IsFractionRing.div_surjective (A:=Zs) x
    rw [← eq, map_div₀, map_div₀, integr, integr]
  rw [eq,Sun28.ShortFormal.order_eq]
  rfl

theorem selectedPlace_conjugate_order {π : Zs} (hπ : Prime π) :
    (discreteOrder ((selectedPlace π hπ).valuation K0)).comap conjugation.toRingHom =
      vP (star π) (prime_star hπ) := by
  rw [selectedPlace_order]
  ext x
  exact (vP_star hπ x).symm

/-- A prime divisor of p in the Euclidean ring lies over p in Mathlib's
integral-closure model. -/
theorem selectedPlace_liesOver {p : ℕ} [pp : Fact p.Prime] {π : Zs} (hπ : Prime π) (divides : π∣(p:Zs)) :
    (selectedPlace π hπ).asIdeal.LiesOver
      ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,pp.out⟩).asIdeal := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,pp.out⟩
  let w:=selectedPlace π hπ
  have z : (p:𝓞 K0)∈w.asIdeal := by
    change integerEquiv.symm (p:𝓞 K0) ∈ (primeSpec π hπ).asIdeal
    rw [map_natCast,primeSpec_asIdeal,Ideal.mem_span_singleton]
    exact divides
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,pp.out⟩)
  let φ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)
  have span : v.asIdeal=Ideal.span {(p:𝓞 ℚ)} := by
    have e : v.asIdeal.map φ=(Ideal.span {(p:𝓞 ℚ)}).map φ := by
      rw [Ideal.map_span,Set.image_singleton,map_natCast]
      exact name ▸ (Rat.HeightOneSpectrum.span_natGenerator v).symm
    simpa [Ideal.comap_map_of_bijective _ φ.bijective] using congrArg (Ideal.comap φ) e
  constructor
  apply v.isMaximal.eq_of_le (w.asIdeal.comap_isPrime (algebraMap (𝓞 ℚ) (𝓞 K0))).ne_top
  rw [span,Ideal.span_le,Set.singleton_subset_iff]
  change algebraMap (𝓞 ℚ) (𝓞 K0) (p:𝓞 ℚ)∈w.asIdeal
  simpa using z

end
end Sun28.SelectedTrace
#print axioms Sun28.SelectedTrace.coe_integerEquiv
#print axioms Sun28.SelectedTrace.selectedPlace_order
#print axioms Sun28.SelectedTrace.selectedPlace_conjugate_order
#print axioms Sun28.SelectedTrace.selectedPlace_liesOver
