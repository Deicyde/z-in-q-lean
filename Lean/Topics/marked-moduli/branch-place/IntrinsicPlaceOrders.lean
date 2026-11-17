import LocalBranchPlaces
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Valuation.LocalSubring

/-! Exact magnitudes of the intrinsic branch coordinates at a specified p-adic embedding. -/
open Polynomial
open scoped NNReal
namespace ZInQBlueprint.BranchPlaces
open BranchDepth BranchHeight ContactInvariant ClusterRoots ClusterPicture ResidueExtension PrimitiveParameters
open DirectCharts SexticThetaHeight IsDiscreteValuationRing
noncomputable section

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]
local notation "Kp" => PadicAlgCl p

/-- The unramified quadratic chart has an embedding into the algebraic closure of the local
field under which every integral unit has absolute value one. -/
theorem integral_chart_embedding :
    ∃ φ : W →+* Kp, Function.Injective φ ∧ ∀ b : Wˣ, ‖φ (b:W)‖=1 := by
  let F := LocalField p
  let : FiniteDimensional ℚ_[p] F := Module.finite_of_finrank_pos (by
    change 0 < Module.finrank ℚ_[p] (LocalField p)
    rw [fraction_degree]
    decide)
  let ι : F →ₐ[ℚ_[p]] Kp := IsAlgClosed.lift
  let φ := ι.toRingHom.comp (algebraMap W F)
  refine ⟨φ,ι.injective.comp (IsFractionRing.injective W F),?_⟩
  let V := (Valued.v : Valuation Kp ℝ≥0).valuationSubring
  let f := ((algebraMap ℚ_[p] Kp).comp (algebraMap Zp ℚ_[p])).codRestrict V.toSubring (by
    intro x
    change ‖((x:ℚ_[p]):Kp)‖₊ ≤ 1
    change ‖((x:ℚ_[p]):Kp)‖ ≤ (1:ℝ)
    rw [PadicAlgCl.norm_extends]
    exact x.2)
  have hc : (algebraMap V Kp).comp f = φ.comp (algebraMap Zp W) := by
    ext1 x
    change algebraMap ℚ_[p] Kp (algebraMap Zp ℚ_[p] x) =
      ι (algebraMap W F (algebraMap Zp W x))
    rw [← IsScalarTower.algebraMap_apply Zp W F, IsScalarTower.algebraMap_apply Zp ℚ_[p] F, ι.commutes]
  have bounded (x : W) : ‖φ x‖ ≤ 1 := by
    have hx := (Algebra.IsIntegral.isIntegral (R:=Zp) x).map_of_comp_eq f φ hc
    change IsIntegral V (φ x) at hx
    obtain ⟨y,hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hx
    exact hy ▸ y.2
  intro b
  refine le_antisymm (bounded b) ?_
  have hi := bounded (↑b⁻¹:W)
  calc 1 = ‖φ (b:W)‖ * ‖φ (↑b⁻¹:W)‖ := by rw [←norm_mul,←map_mul,b.mul_inv,map_one,norm_one]
       _ ≤ ‖φ (b:W)‖ := mul_le_of_le_one_right (norm_nonneg _) hi

private theorem unit_factor_norm {φ : W →+* Kp} (hφ : ∀ b : Wˣ, ‖φ (b:W)‖=1)
    {y : Kp} {n : ℤ} (hy : ∃ b : Wˣ, y=φ (b:W) * φ (p:W)^n) :
    ‖y‖ = (1/(p:ℝ))^n := by
  obtain ⟨b,rfl⟩ := hy
  have hpn : ‖(p:Kp)‖=(1/(p:ℝ)) := by
    simp only [← PadicAlgCl.valuation_coe,PadicAlgCl.valuation_p,NNReal.coe_div,NNReal.coe_one,NNReal.coe_natCast]
  rw [norm_mul,hφ,one_mul,norm_zpow,map_natCast,hpn]

/-- For each prescribed embedding one coordinate has order 8d and the others have order zero. -/
theorem contact_at_embedding {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (σ : weightField r →+* PadicAlgCl p) (hp : 17 ≤ p) (d : ℕ) (hd : 0 < d)
    (hF : addVal Zp (RationalClusters.F p u)=((2*d:ℕ):ℕ∞)) :
    ∃ k : Fin 10, ∀ i : Fin 10, ‖(σ (sumWeights r i) : Kp)‖ =
      (1/(p:ℝ))^(if i=k then (8*d:ℤ) else 0) := by
  obtain ⟨φ,hi,hφ⟩ := integral_chart_embedding p
  obtain ⟨t,v,a,hc,T,ht⟩ := even_normalized p φ hi u hp d hd hF
  obtain ⟨e,he⟩ := at_chart p hu hδ hr hz σ φ hi hc T
  obtain ⟨k,hk⟩ := ht e
  exact ⟨k,fun i => unit_factor_norm p hφ ((he i).symm ▸ hk i)⟩

/-- For each prescribed embedding one coordinate has order 6g and the others have order −2g. -/
theorem pole_at_embedding {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ≠0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (σ : weightField r →+* PadicAlgCl p) (hp : 17 ≤ p) (g : ℕ) (hg : 0 < g)
    (hG : addVal Zp (RationalClusters.G p u)=(g:ℕ∞)) :
    ∃ k : Fin 10, ∀ i : Fin 10, ‖(σ (sumWeights r i) : Kp)‖ =
      (1/(p:ℝ))^(if i=k then (6*g:ℤ) else -(2*g)) := by
  obtain ⟨φ,hi,hφ⟩ := integral_chart_embedding p
  obtain ⟨t,a,hc,T,ht⟩ := pole_normalized p φ hi u hp g hg hG
  obtain ⟨e,he⟩ := at_chart p hu hδ hr hz σ φ hi hc T
  obtain ⟨k,hk⟩ := ht e
  exact ⟨k,fun i => unit_factor_norm p hφ ((he i).symm ▸ hk i)⟩

end
end ZInQBlueprint.BranchPlaces
#print axioms ZInQBlueprint.BranchPlaces.integral_chart_embedding
#print axioms ZInQBlueprint.BranchPlaces.contact_at_embedding
#print axioms ZInQBlueprint.BranchPlaces.pole_at_embedding
