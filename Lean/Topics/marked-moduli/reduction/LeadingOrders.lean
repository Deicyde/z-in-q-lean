import DirectCharts
import PrincipalClusters
import GlobalTwist
/-! The leading coefficient of the integral twist and its two principal valuations. -/
namespace ZInQBlueprint.LeadingOrders
open Polynomial IsDiscreteValuationRing
open ZInQBlueprint.IntegralSextic ZInQBlueprint.DirectCharts ZInQBlueprint.PrincipalClusters
open ZInQBlueprint.ResidualFactors ZInQBlueprint.ClusterRoots ZInQBlueprint.ClusterPicture
noncomputable section

theorem affine {R : Type*} [CommRing R] (a t x z : R) : form a (a*t) x z = a^2*form 1 t x z := by
  unfold form; ring

theorem reciprocal_chart {R : Type*} [CommRing R] {a b t : R} (ht : 27*a=b*t) (x z : R) :
    form a b (6*z) x=8*b^2*form 1 t x z := by rw [reciprocal,ht,affine]; ring

def chart {R : Type*} [CommRing R] (δ G v a t : R) : R[X] :=
  C (-6*δ*G*v*a^2)*monicSextic t

theorem leading {R : Type*} [CommRing R] [IsDomain R] (δ G v a t : R) :
    (chart δ G v a t).leadingCoeff = -6*δ*G*v*a^2 := by
  rw [chart,leadingCoeff_mul,leadingCoeff_C,(monic_six t).1.leadingCoeff,mul_one]

/-- The square identity guarantees at least one unit chart whenever G is a unit. -/
theorem chart_exists {R : Type*} [CommRing R] [IsLocalRing R] (A B : R) (hG : IsUnit (poleForm A B)) :
    IsUnit (m A B) ∨ IsUnit (n A B) := by
  by_contra! h
  have hm := mt (IsLocalRing.residue_ne_zero_iff_isUnit (m A B)).mp h.1
  have hn := mt (IsLocalRing.residue_ne_zero_iff_isUnit (n A B)).mp h.2
  push Not at hm hn
  have he := congrArg (IsLocalRing.residue R) (parameter_identities A B).2.1
  simp only [map_pow,map_mul,map_add,hm,hn,zero_pow (by decide : (2:ℕ)≠0),mul_zero,add_zero] at he
  exact pow_ne_zero 3 ((IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hG) he

variable (p : ℕ) [Fact p.Prime]
open ZInQBlueprint.ResidueExtension ZInQBlueprint.RationalClusters ZInQBlueprint.PadicParameters
open ZInQBlueprint.GlobalTwist
local notation "W" => IntegralField p

private theorem small_unit (n : ℕ) (hn : 0<n) (hp : n<p) : IsUnit (n:ℤ_[p]) := by
  have h : PadicInt.toZMod (n:ℤ_[p])≠0 := by
    rw [map_natCast,Ne,CharP.cast_eq_zero_iff (ZMod p) p]; exact Nat.not_dvd_of_pos_of_lt hn hp
  rw [Ne,← RingHom.mem_ker,PadicInt.ker_toZMod,IsLocalRing.mem_maximalIdeal] at h
  exact not_not.mp h
private theorem val_lead (hp : 7≤p) (u : ℚ) {v a : W} (hv : IsUnit v) (ha : IsUnit a) (t : W) :
    addVal W (chart (delta u:W) (fromPadics p (G p u)) v a t).leadingCoeff =
      addVal W (delta u:W) + addVal W (fromPadics p (G p u)) := by
  rw [leading]
  have h6 : IsUnit (6:W) := by simpa only [map_natCast, Nat.cast_ofNat, map_ofNat] using (small_unit p 6 (by decide) (by omega)).map (fromPadics p)
  simp only [AddValuation.map_mul,AddValuation.map_neg,addVal_eq_zero_iff.mpr h6,addVal_eq_zero_iff.mpr hv,
    addVal_eq_zero_iff.mpr (ha.pow 2),zero_add,add_zero]

theorem even_lead (u : ℚ) (hp : 17≤p) (k : ℕ) (hk : 0<k)
    (hf : addVal ℤ_[p] (F p u)=((2*k:ℕ):ℕ∞)) {v a : W}
    (hv : IsUnit v) (ha : IsUnit a) (t : W) :
    addVal W (chart (delta u:W) (fromPadics p (G p u)) v a t).leadingCoeff=(k%2:ℕ) := by
  have hG := (even_contact_data (by omega) _ _ (rational_primitive u) k hk hf).1
  rw [val_lead p (by omega) u hv ha,(even_contact p u hp k hf).witt_val,addVal_eq_zero_iff.mpr (hG.map _),add_zero]

theorem pole_lead (u : ℚ) (hp : 17≤p) (g : ℕ) (hg : 0<g)
    (hG : addVal ℤ_[p] (G p u)=(g:ℕ∞)) {v a : W}
    (hv : IsUnit v) (ha : IsUnit a) (t : W) :
    addVal W (chart (delta u:W) (fromPadics p (G p u)) v a t).leadingCoeff=(g:ℕ∞) := by
  obtain ⟨_,_,D,hD⟩ := pole_data (by omega) _ _ (rational_primitive u) g hg hG
  have h : fromPadics p (G p u)=(p:W)^g*(fromPadics p (D:ℤ_[p])) := by
    simpa only [map_mul,map_pow,map_natCast] using congrArg (fromPadics p) hD
  rw [val_lead p (by omega) u hv ha,(pole p u (by omega) g hg hG).witt_val,Nat.cast_zero,zero_add,h,
    AddValuation.map_mul,(uniformizer p).addVal_pow,addVal_eq_zero_iff.mpr (D.isUnit.map _),add_zero]

def principalOrder {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (f : S[X]) {mon : S[X]} {c : S} (T : SexticFibre mon c) (s : Cluster) (hs : principal s) : ℤ :=
  nu (addVal S f.leadingCoeff).toNat (fun i j => addVal S (point T i-point T j)) s hs

theorem even_principal (u : ℚ) (hp : 17≤p) (k : ℕ) (hk : 0<k)
    (hf : addVal ℤ_[p] (F p u)=((2*k:ℕ):ℕ∞)) {v a t : W} (hv : IsUnit v) (ha : IsUnit a)
    (T : SexticFibre (monicSextic t) ((p:W)^k)) (s : Cluster) (hs : principal s) :
    Even (principalOrder (chart (delta u:W) (fromPadics p (G p u)) v a t) T s hs) := by
  rw [principalOrder,fibre_nu (uniformizer p),even_lead p u hp k hk hf hv ha]
  simp only [ENat.toNat_natCast]
  rw [Int.even_iff]; omega

theorem pole_principal (u : ℚ) (hp : 17≤p) (g : ℕ) (hg : 0<g)
    (hG : addVal ℤ_[p] (G p u)=(g:ℕ∞)) {v a t : W} (hv : IsUnit v) (ha : IsUnit a)
    (T : SexticFibre (monicSextic t) ((p:W)^g)) (s : Cluster) (hs : principal s) :
    principalOrder (chart (delta u:W) (fromPadics p (G p u)) v a t) T s hs=4*g := by
  rw [principalOrder,fibre_nu (uniformizer p),pole_lead p u hp g hg hG hv ha]; simp; ring
end
end ZInQBlueprint.LeadingOrders
#print axioms ZInQBlueprint.LeadingOrders.affine
#print axioms ZInQBlueprint.LeadingOrders.reciprocal_chart
#print axioms ZInQBlueprint.LeadingOrders.leading
#print axioms ZInQBlueprint.LeadingOrders.chart_exists
#print axioms ZInQBlueprint.LeadingOrders.even_lead
#print axioms ZInQBlueprint.LeadingOrders.pole_lead
#print axioms ZInQBlueprint.LeadingOrders.even_principal
#print axioms ZInQBlueprint.LeadingOrders.pole_principal
