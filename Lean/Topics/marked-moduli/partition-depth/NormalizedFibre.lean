import FibreSumOrders
import ProjectivePartitions

/-! Coordinates after dividing all ten weights by their sum. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial ClusterPicture ClusterRoots DirectCharts ResidueExtension PrimitiveParameters
open IsDiscreteValuationRing
noncomputable section

def normalized {K : Type*} [Field K] (w : Fin 10 → K) (i : Fin 10) := w i / ∑ j, w j

theorem normalized_scaling {K : Type*} [Field K] (w : Fin 10 → K) {s : K} (hs : s ≠ 0)
    (i : Fin 10) : normalized (fun j => s*w j) i = normalized w i := by
  simp only [normalized,← Finset.mul_sum,mul_div_mul_left _ _ hs]

theorem normalized_mobius {K : Type*} [Field K] (r : Fin 6 → K) (a b c d : K) (h : a*d-b*c≠0)
    (hu : ∀ j, c*r j+d≠0) (i : Fin 10) :
    normalized (weight (fun j => mobius a b c d (r j))) i = normalized (weight r) i := by
  let C := (∏ j, (c*r j+d))^4
  have hC : C≠0 := pow_ne_zero _ (Finset.prod_ne_zero_iff.mpr fun j _ => hu j)
  let s := (a*d-b*c)^12/C
  have hs : s≠0 := div_ne_zero (pow_ne_zero _ h) hC
  have hw (j) : weight (fun k => mobius a b c d (r k)) j = s*weight r j := by
    rw [show s*weight r j = ((a*d-b*c)^12*weight r j)/C by unfold s; ring]
    exact (eq_div_iff hC).mpr (clear_weight_mobius r a b c d hu j)
  rw [show weight (fun k => mobius a b c d (r k)) = fun j => s*weight r j from funext hw]
  exact normalized_scaling _ hs i

private theorem factor_of_order {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {π x : R} (hπ : Irreducible π) {n : ℕ} (hx : addVal R x=(n:ℕ∞)) :
    ∃ e : Rˣ, x=e*π^n := by
  have h : x≠0 := by rintro rfl; exact ENat.natCast_ne_top _ (hx.symm.trans addVal_zero)
  obtain ⟨m,e,hm⟩ := eq_unit_mul_pow_irreducible h hπ
  exact ⟨e,(ENat.natCast_inj.mp ((addVal_def _ e hπ m hm).symm.trans hx)) ▸ hm⟩

/-- A quotient with known numerator and denominator orders is a unit times the signed power. -/
theorem quotient_order {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] (φ : R →+* K) (hi : Function.Injective φ) {π x y : R} (hπ : Irreducible π)
    {m n : ℕ} (hx : addVal R x=(m:ℕ∞)) (hy : addVal R y=(n:ℕ∞)) :
    ∃ e : Rˣ, φ x / φ y = φ (e:R) * (φ π)^((m:ℤ)-(n:ℤ)) := by
  obtain ⟨a,ha⟩ := factor_of_order hπ hx
  obtain ⟨b,hb⟩ := factor_of_order hπ hy
  refine ⟨a*b⁻¹, ?_⟩
  have hπ' : φ π≠0 := (map_ne_zero_iff φ hi).mpr hπ.ne_zero
  have hb' : φ (b:R)≠0 := (b.isUnit.map φ).ne_zero
  rw [ha,hb,map_mul,map_mul,Units.val_mul,map_mul,map_pow,map_pow,zpow_sub₀ hπ',
    zpow_natCast,zpow_natCast]
  have hinv : φ (↑b⁻¹:R) = (φ (b:R))⁻¹ := by
    apply (mul_right_cancel₀ hb')
    rw [inv_mul_cancel₀ hb',← map_mul,Units.inv_mul,map_one]
  rw [hinv]
  ring

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]

/-- The tuple in any field containing the local splitting ring. -/
def normalizedFibre {K : Type*} [Field K] (φ : W →+* K) {t c : W}
    (T : SexticFibre (monicSextic t) c) (e : Fin 6 ≃ Index) :=
  normalized (fun i => φ (weight (fun j => point T (e j)) i))

private theorem fibre_profile {K : Type*} [Field K] (φ : W →+* K) (hi : Function.Injective φ)
    {t : W} {m n : ℕ} (T : SexticFibre (monicSextic t) ((p:W)^m)) (e : Fin 6 ≃ Index)
    (h : addVal W (∑ i, weight (fun j => point T (e j)) i)=(n:ℕ∞)) :
    ∃ k : Fin 10, ∀ i, ∃ b : Wˣ, normalizedFibre p φ T e i =
      φ (b:W) * φ (p:W)^((if i=k then (12*m:ℤ) else 4*m)-(n:ℤ)) := by
  obtain ⟨k,hk⟩ := fibre_orders (uniformizer p) m T e
  refine ⟨k,fun i => ?_⟩
  unfold normalizedFibre normalized
  rw [←map_sum]
  by_cases he : i=k
  · simpa [he] using quotient_order φ hi (uniformizer p) (by simpa [he] using hk i : addVal W _=((12*m:ℕ):ℕ∞)) h
  · simpa [he] using quotient_order φ hi (uniformizer p) (by simpa [he] using hk i : addVal W _=((4*m:ℕ):ℕ∞)) h

theorem even_normalized {K : Type*} [Field K] (φ : W →+* K) (hi : Function.Injective φ)
    (u : ℚ) (hp : 17 ≤ p) (m : ℕ) (hm : 0 < m)
    (hF : addVal Zp (RationalClusters.F p u)=((2*m:ℕ):ℕ∞)) :
    ∃ t : Zp, ∃ v a : Zpˣ, Coordinates p u t (v:Zp) (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p t)) ((p:W)^m), ∀ e : Fin 6 ≃ Index,
        ∃ k : Fin 10, ∀ i, ∃ b : Wˣ, normalizedFibre p φ T e i =
          φ (b:W) * φ (p:W)^(if i=k then (8*m:ℤ) else 0) := by
  obtain ⟨t,v,a,hc,ht⟩ := even_parameter p u hp m hm hF
  obtain ⟨T⟩ := PrimitiveRoots.even_valuation p (by omega) t m hm ht
  refine ⟨t,v,a,hc,T,fun e => ?_⟩
  obtain ⟨k,hk⟩ := fibre_profile p φ hi T e (even_sum_order p hp m hm ht T e)
  refine ⟨k,fun i => ?_⟩
  obtain ⟨b,hb⟩ := hk i
  refine ⟨b,hb.trans ?_⟩
  congr 2
  push_cast
  split <;> omega

theorem pole_normalized {K : Type*} [Field K] (φ : W →+* K) (hi : Function.Injective φ)
    (u : ℚ) (hp : 17 ≤ p) (g : ℕ) (hg : 0 < g)
    (hG : addVal Zp (RationalClusters.G p u)=(g:ℕ∞)) :
    ∃ t a : Zpˣ, Coordinates p u (t:Zp) 1 (a:Zp) ∧
      ∃ T : SexticFibre (monicSextic (fromPadics p (t:Zp))) ((p:W)^g), ∀ e : Fin 6 ≃ Index,
        ∃ k : Fin 10, ∀ i, ∃ b : Wˣ, normalizedFibre p φ T e i =
          φ (b:W) * φ (p:W)^(if i=k then (6*g:ℤ) else -(2*g)) := by
  obtain ⟨t,a,hc,he⟩ := PrimitiveParameters.pole_parameter p u hp g hg hG
  have ht : (t:Zp)*left p u=right p u := by
    cases hc with
    | first _ ha h => rw [←ha,mul_comm]; exact h
    | second hv _ _ => norm_num at hv
  obtain ⟨T⟩ := PrimitivePoleFibre.pole_parameter p (by omega) _ _ (t:Zp)
    (PadicParameters.rational_primitive u) g hg hG ht
  refine ⟨t,a,hc,T,fun e => ?_⟩
  obtain ⟨k,hk⟩ := fibre_profile p φ hi T e (pole_sum_order p hp g hG he T e)
  refine ⟨k,fun i => ?_⟩
  obtain ⟨b,hb⟩ := hk i
  refine ⟨b,hb.trans ?_⟩
  congr 2
  push_cast
  split <;> omega

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.normalized_scaling
#print axioms ZInQBlueprint.BranchDepth.normalized_mobius
#print axioms ZInQBlueprint.BranchDepth.quotient_order
#print axioms ZInQBlueprint.BranchDepth.even_normalized
#print axioms ZInQBlueprint.BranchDepth.pole_normalized
