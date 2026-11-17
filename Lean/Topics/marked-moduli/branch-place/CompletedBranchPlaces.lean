import IntrinsicPlaceOrders
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! Computing the normalized coordinates at a prime ideal of the actual intrinsic number field. -/
open IsDedekindDomain NumberField Polynomial
open scoped NNReal
namespace ZInQBlueprint.BranchPlaces
open BranchDepth BranchHeight ContactInvariant ClusterRoots ClusterPicture ResidueExtension PrimitiveParameters
open DirectCharts SexticThetaHeight IsDiscreteValuationRing
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]

/-- The prime of the ring of integers of the rationals associated to p. -/
def rationalPrime := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩

/-- The rational completion maps continuously into the completion at each prime above it. -/
theorem map_to_completion {K : Type*} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) [w.asIdeal.LiesOver (rationalPrime p).asIdeal] :
    ∃ j : ℚ_[p] →+* w.adicCompletion K, Continuous j := by
  let v := rationalPrime p
  let f := algebraMap (WithVal (v.valuation ℚ)) (WithVal (w.valuation K))
  have hf := HeightOneSpectrum.uniformContinuous_algebraMap_liesOver ℚ K v w
  let e := Padic.adicCompletionEquiv (𝓞 ℚ) ⟨p,Fact.out⟩
  let m := UniformSpace.Completion.mapRingHom f hf.continuous
  let a := (HeightOneSpectrum.adicCompletion.equiv ℚ v).toRingHom.comp e.toAlgEquiv.toRingEquiv.toRingHom
  let b := (HeightOneSpectrum.adicCompletion.equiv K w).symm.toRingHom
  refine ⟨b.comp (m.comp a),?_⟩
  exact (HeightOneSpectrum.adicCompletion.uniformEquiv K w).symm.continuous.comp
    (UniformSpace.Completion.continuous_map.comp
      ((HeightOneSpectrum.adicCompletion.uniformEquiv ℚ v).continuous.comp e.continuous))

/-- If the p-adics map continuously to a nonarchimedean field then the p-adic integers
land in its valuation ring. -/
private theorem maps_integers {E : Type*} [NormedField E] [IsUltrametricDist E]
    (j : ℚ_[p] →+* E) (hc : Continuous j) (x : Zp) : ‖j (x:ℚ_[p])‖ ≤ 1 := by
  refine PadicInt.denseRange_natCast.induction_on (p:=fun a : Zp => ‖j (a:ℚ_[p])‖ ≤ 1) x ?_ ?_
  · exact isClosed_le (continuous_norm.comp (hc.comp PadicInt.isOpenEmbedding_coe.continuous)) continuous_const
  · intro n
    simpa only [PadicInt.coe_natCast,map_natCast] using IsUltrametricDist.norm_natCast_le_one E n

/-- In an algebraic closure of the completed field the quadratic chart maps to integral points. -/
private theorem local_chart_in_closure {E : Type*} [NontriviallyNormedField E] [CompleteSpace E]
    [IsUltrametricDist E] (j : ℚ_[p] →+* E) (hj : Continuous j) :
    ∃ φ : W →+* AlgebraicClosure E, Function.Injective φ ∧
      ∀ b : Wˣ, spectralNorm E (AlgebraicClosure E) (φ (b:W))=1 := by
  let Ω := AlgebraicClosure E
  let : NormedField Ω := spectralNorm.normedField E Ω
  let : IsUltrametricDist Ω := IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm
    (isNonarchimedean_spectralNorm (K:=E) (L:=Ω))
  let F := LocalField p
  let : FiniteDimensional ℚ_[p] F := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank ℚ_[p] (LocalField p)
    rw [fraction_degree]
    decide)
  let k := (algebraMap E Ω).comp j
  let : Algebra ℚ_[p] Ω := k.toAlgebra
  let ι : F →ₐ[ℚ_[p]] Ω := IsAlgClosed.lift
  let φ := ι.toRingHom.comp (algebraMap W F)
  refine ⟨φ,ι.injective.comp (IsFractionRing.injective W F),?_⟩
  let V := (NormedField.valuation (K:=Ω)).valuationSubring
  let f := (k.comp (algebraMap Zp ℚ_[p])).codRestrict V.toSubring (by
    intro x
    change spectralNorm E Ω (algebraMap E Ω (j (x:ℚ_[p]))) ≤ (1:ℝ)
    rw [spectralNorm_extends]
    exact maps_integers p j hj x)
  have hc : (algebraMap V Ω).comp f = φ.comp (algebraMap Zp W) := by
    ext1 x
    change algebraMap ℚ_[p] Ω (algebraMap Zp ℚ_[p] x) =
      ι (algebraMap W F (algebraMap Zp W x))
    rw [← IsScalarTower.algebraMap_apply Zp W F, IsScalarTower.algebraMap_apply Zp ℚ_[p] F, ι.commutes]
  have bounded (x : W) : ‖φ x‖ ≤ 1 := by
    have hx := (Algebra.IsIntegral.isIntegral (R:=Zp) x).map_of_comp_eq f φ hc
    change IsIntegral V (φ x) at hx
    obtain ⟨y,hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx
    exact hy ▸ y.2
  intro b
  change ‖φ (b:W)‖ = 1
  refine le_antisymm (bounded b) ?_
  have hi := bounded (↑b⁻¹:W)
  calc 1 = ‖φ (b:W)‖ * ‖φ (↑b⁻¹:W)‖ := by rw [←norm_mul,←map_mul,b.mul_inv,map_one,norm_one]
       _ ≤ ‖φ (b:W)‖ := mul_le_of_le_one_right (norm_nonneg _) hi


/-- The two computed order profiles at every prime of the actual intrinsic number field above p,
in the absolute value convention used by Mathlib's height. -/
theorem finite_place_profiles {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (hp : 17 ≤ p) :
    letI := weight_numberField hu hδ hz
    ∀ w : FinitePlace (weightField r), w.maximalIdeal.asIdeal.LiesOver (rationalPrime p).asIdeal →
      (∀ d : ℕ, 0 < d → addVal Zp (RationalClusters.F p u)=((2*d:ℕ):ℕ∞) →
        ∃ k : Fin 10, ∀ i : Fin 10, w (sumWeights r i) =
          (w (p:weightField r))^(if i=k then (8*d:ℤ) else 0)) ∧
      (∀ g : ℕ, 0 < g → addVal Zp (RationalClusters.G p u)=(g:ℕ∞) →
        ∃ k : Fin 10, ∀ i : Fin 10, w (sumWeights r i) =
          (w (p:weightField r))^(if i=k then (6*g:ℤ) else -(2*g))) := by
  let := weight_numberField hu hδ hz
  intro w hw
  let := hw
  let K := weightField r
  let E := w.maximalIdeal.adicCompletion K
  let Ω := AlgebraicClosure E
  let : NontriviallyNormedField E := Valued.toNontriviallyNormedField E (WithZero (Multiplicative ℤ))
  let : IsUltrametricDist E := inferInstanceAs (IsUltrametricDist (w.maximalIdeal.adicCompletion K))
  let : NormedField Ω := spectralNorm.normedField E Ω
  let σ := (algebraMap E Ω).comp (FinitePlace.embedding (K:=K) w.maximalIdeal)
  let : CharZero Ω := (RingHom.charZero_iff σ.injective).mp inferInstance
  obtain ⟨j,hj⟩ := map_to_completion p w.maximalIdeal
  obtain ⟨φ,hi,hφ⟩ := local_chart_in_closure p j hj
  have hn (x : K) : ‖σ x‖ = w x := by
    change spectralNorm E Ω (algebraMap E Ω (FinitePlace.embedding w.maximalIdeal x)) = w x
    rw [spectralNorm_extends,FinitePlace.norm_embedding_eq]
  have handle (x : K) (n : ℤ) {y : Ω} (hy : σ x=y)
      (h : ∃ b : Wˣ, y=φ (b:W)*φ (p:W)^n) : w x=(w (p:K))^n := by
    obtain ⟨b,hb⟩ := h
    rw [← hn,hy,hb,norm_mul,show ‖φ (b:W)‖=1 from hφ b,one_mul,norm_zpow,map_natCast]
    rw [← hn (p:K),map_natCast]
  constructor
  · intro d hd hF
    obtain ⟨t,v,a,hc,T,ht⟩ := even_normalized p φ hi u hp d hd hF
    obtain ⟨e,he⟩ := at_chart p hu hδ hr hz σ φ hi hc T
    obtain ⟨k,hk⟩ := ht e
    exact ⟨k,fun i => handle _ _ (he i) (hk i)⟩
  · intro g hg hG
    obtain ⟨t,a,hc,T,ht⟩ := pole_normalized p φ hi u hp g hg hG
    obtain ⟨e,he⟩ := at_chart p hu hδ hr hz σ φ hi hc T
    obtain ⟨k,hk⟩ := ht e
    exact ⟨k,fun i => handle _ _ (he i) (hk i)⟩


private theorem profile_sup (f : Fin 10 → ℝ) {b : ℝ} (hb₀ : 0<b) (hb₁ : b≤1)
    {m n : ℤ} (hmn : m ≤ n) (h : ∃ k : Fin 10, ∀ i, f i=b^(if i=k then n else m)) :
    (⨆ i, f i)=b^m := by
  obtain ⟨k,hk⟩ := h
  apply le_antisymm
  · apply ciSup_le
    intro i
    rw [hk]
    apply zpow_right_anti₀ hb₀ hb₁
    split <;> omega
  · obtain ⟨i,hi⟩ := exists_ne k
    exact le_ciSup_of_le (Finite.bddAbove_range _) i (le_of_eq (by simp [hk,hi]))

/-- The factor in the multiplicative height is one on the even-contact chart and
w(p)^(-2g) on the pole chart, in the finite-place normalization used by Mathlib. -/
theorem finite_place_suprema {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (hp : 17 ≤ p) :
    letI := weight_numberField hu hδ hz
    ∀ w : FinitePlace (weightField r), w.maximalIdeal.asIdeal.LiesOver (rationalPrime p).asIdeal →
      (∀ d : ℕ, 0 < d → addVal Zp (RationalClusters.F p u)=((2*d:ℕ):ℕ∞) →
        (⨆ i : Fin 10, w (sumWeights r i)) = 1) ∧
      (∀ g : ℕ, 0 < g → addVal Zp (RationalClusters.G p u)=(g:ℕ∞) →
        (⨆ i : Fin 10, w (sumWeights r i)) = (w (p:weightField r))^(-(2*g:ℤ))) := by
  let := weight_numberField hu hδ hz
  intro w hw
  obtain ⟨contact,pole⟩ := finite_place_profiles p hu hδ hr hz hp w hw
  have hb₀ : 0 < w (p:weightField r) := FinitePlace.pos_iff.mpr (Nat.cast_ne_zero.mpr (by omega))
  have hb₁ : w (p:weightField r) ≤ 1 := by
    rw [← FinitePlace.norm_embedding_eq w]
    simpa only [map_natCast] using FinitePlace.norm_le_one (weightField r) w.maximalIdeal (p:𝓞 (weightField r))
  constructor
  · intro d hd hF
    simpa only [zpow_zero] using profile_sup _ hb₀ hb₁ (show (0:ℤ) ≤ 8*d by positivity) (contact d hd hF)
  · intro g hg hG
    exact profile_sup _ hb₀ hb₁ (show -(2*g:ℤ) ≤ 6*g by omega) (pole g hg hG)

end
end ZInQBlueprint.BranchPlaces
#print axioms ZInQBlueprint.BranchPlaces.map_to_completion
#print axioms ZInQBlueprint.BranchPlaces.finite_place_profiles

#print axioms ZInQBlueprint.BranchPlaces.finite_place_suprema
