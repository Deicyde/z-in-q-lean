import IntegralWeightSum
import LocalPartitionDepth

/-! The distinguished sum on a two-triple fibre of the monic sextic. -/
namespace ZInQBlueprint.BranchDepth
open Polynomial ClusterPicture ClusterRoots DirectCharts IsDiscreteValuationRing
open ResidueExtension PrimitiveParameters
noncomputable section

private theorem factors {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {t c : R} (T : SexticFibre (monicSextic t) c) (e : Fin 6 ≃ Index) :
    (∏ j, (X-C (point T (e j)))) = monicSextic t := by
  classical
  let f := monicSextic t
  let r : Fin 6 ↪ R := ⟨fun j => point T (e j), T.triples.injective.comp e.injective⟩
  let S := Finset.univ.map r
  have hc : S.card = 6 := by simp [S]
  have hdeg : f.natDegree = 6 := (monic_six t).2
  have hroots : f.roots = S.val := roots_eq_of_natDegree_le_card_of_ne_zero (fun x hx => by
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hx
    exact T.triples.root (e i).1 (e i).2) (hdeg.trans hc.symm).le T.nonzero
  have eq := prod_multiset_X_sub_C_of_monic_of_roots_card_eq (monic_six t).1
    (hroots ▸ hc.trans hdeg.symm)
  rw [hroots] at eq
  change (∏ j, (X-C (r j))) = f
  convert eq using 1
  change (∏ j, (X-C (r j))) = ∏ x ∈ S, (X-C x)
  rw [Finset.prod_map]

theorem fibre_weight_sum {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    {t c : R} (T : SexticFibre (monicSextic t) c) (e : Fin 6 ≃ Index) :
    ∑ i, weight (fun j => point T (e j)) i = -144*t^2*(t^2+27)^2 :=
  monic_weight_sum _ _ (factors T e)

variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "Zp" => ℤ_[p]

private theorem map_order {t : Zp} {n : ℕ} (ht : addVal Zp t=(n:ℕ∞)) :
    addVal W (fromPadics p t)=(n:ℕ∞) := by
  have hn : t ≠ 0 := by
    rintro rfl
    rw [addVal_zero] at ht
    exact ENat.natCast_ne_top _ ht.symm
  obtain ⟨m,u,h⟩ := eq_unit_mul_pow_irreducible hn PadicInt.irreducible_p
  have hm : m=n := ENat.natCast_inj.mp ((addVal_def _ u PadicInt.irreducible_p m h).symm.trans ht)
  rw [h,hm,map_mul,map_pow,map_natCast,AddValuation.map_mul,
    addVal_eq_zero_iff.mpr (u.isUnit.map _),(uniformizer p).addVal_pow,zero_add]

private theorem small_units (hp : 17 ≤ p) : IsUnit (144:W) ∧ IsUnit (27:W) := by
  have unit_cast (n : ℕ) (hn : 0<n) (hnp : n<p) : IsUnit (n:W) := by
    have hh := (unit_nat p n hn hnp).map (fromPadics p)
    rw [map_natCast] at hh
    exact hh
  have h₁ := unit_cast 12 (by decide) (by omega)
  have h₂ := unit_cast 3 (by decide) (by omega)
  constructor
  · convert h₁.pow 2 using 1
    norm_num
  · convert h₂.pow 3 using 1
    norm_num

theorem even_sum_order (hp : 17 ≤ p) {t : Zp} (m : ℕ) (hm : 0 < m)
    (ht : addVal Zp t=((2*m:ℕ):ℕ∞))
    (T : SexticFibre (monicSextic (fromPadics p t)) ((p:W)^m)) (e : Fin 6 ≃ Index) :
    addVal W (∑ i, weight (fun j => point T (e j)) i) = ((4*m:ℕ):ℕ∞) := by
  let t' := fromPadics p t
  have h := map_order p ht
  have hnu : ¬IsUnit t' := by
    intro hu
    have hn := (addVal_eq_zero_iff.mpr hu).symm.trans h
    exact (by omega : 0 ≠ 2*m) (by exact_mod_cast hn)
  have hz : IsLocalRing.residue W t'=0 := by
    by_contra hn
    exact hnu ((IsLocalRing.residue_ne_zero_iff_isUnit _).mp hn)
  obtain ⟨ha,hb⟩ := small_units p hp
  have hu : IsUnit (t'^2+27) := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp (by
    rw [map_add,map_pow,hz,zero_pow (by decide),zero_add]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hb)
  rw [fibre_weight_sum,AddValuation.map_mul,AddValuation.map_mul,AddValuation.map_neg,
    addVal_eq_zero_iff.mpr ha,AddValuation.map_pow,h,addVal_eq_zero_iff.mpr (hu.pow 2),zero_add,add_zero]
  rw [nsmul_eq_mul]
  exact_mod_cast (by omega : 2*(2*m) = 4*m)

theorem pole_sum_order (hp : 17 ≤ p) {u : ℚ} {t a : Zpˣ} (g : ℕ)
    (hG : addVal Zp (RationalClusters.G p u)=(g:ℕ∞))
    (he : (a:Zp)^2*((t:Zp)^2+27)=RationalClusters.G p u^3)
    (T : SexticFibre (monicSextic (fromPadics p (t:Zp))) ((p:W)^g)) (e : Fin 6 ≃ Index) :
    addVal W (∑ i, weight (fun j => point T (e j)) i) = ((6*g:ℕ):ℕ∞) := by
  have hv := congrArg (addVal Zp) he
  simp only [AddValuation.map_mul,addVal_eq_zero_iff.mpr (a.isUnit.pow 2),zero_add,
    AddValuation.map_pow,hG] at hv
  have hv' : addVal Zp ((t:Zp)^2+27)=((3*g:ℕ):ℕ∞) := by simpa using hv
  have hw := map_order p hv'
  rw [map_add,map_pow,map_ofNat] at hw
  obtain ⟨ha,_⟩ := small_units p hp
  rw [fibre_weight_sum,AddValuation.map_mul,AddValuation.map_mul,AddValuation.map_neg,
    addVal_eq_zero_iff.mpr ha,addVal_eq_zero_iff.mpr ((t.isUnit.map _).pow 2),
    AddValuation.map_pow,hw,zero_add,zero_add]
  rw [nsmul_eq_mul]
  exact_mod_cast (by omega : 2*(3*g) = 6*g)

end
end ZInQBlueprint.BranchDepth
#print axioms ZInQBlueprint.BranchDepth.fibre_weight_sum
#print axioms ZInQBlueprint.BranchDepth.even_sum_order
#print axioms ZInQBlueprint.BranchDepth.pole_sum_order
