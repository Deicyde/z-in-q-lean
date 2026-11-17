import RationalReduction
import WittBasis
import Mathlib.FieldTheory.SplittingField.IsSplittingField

/-! The twisted chart over the base p-adic field and its splitting field. -/

open Polynomial IsDiscreteValuationRing
open ZInQBlueprint.ResidueExtension ZInQBlueprint.DirectCharts ZInQBlueprint.LeadingOrders
open ZInQBlueprint.RationalReduction ZInQBlueprint.RationalClusters ZInQBlueprint.ClusterRoots
open ZInQBlueprint.GlobalTwist

namespace ZInQBlueprint.GoodReductionCharts

noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "W" => IntegralField p
local notation "L" => LocalField p
local notation "Zp" => ℤ_[p]
local notation "Qp" => ℚ_[p]

/-- The base-field polynomial includes the twisting scalar and the unit of the
chosen chart. Its roots alone do not determine the quadratic twist. -/
def polynomial (u : ℚ) (v a : Zpˣ) (t : Zp) : Qp[X] :=
  (chart (delta u : Zp) (G p u) (v : Zp) (a : Zp) t).map (algebraMap Zp Qp)

private theorem map_chart {R S : Type*} [CommRing R] [CommRing S] (ι : R →+* S)
    (d b v a t : R) :
    (chart d b v a t).map ι = chart (ι d) (ι b) (ι v) (ι a) (ι t) := by
  simp [chart, monic_coeffs, map_ofNat]

theorem polynomial_map (u : ℚ) (v a : Zpˣ) (t : Zp) :
    (polynomial p u v a t).map (algebraMap Qp L) =
      (equation p u v a t).map (algebraMap W L) := by
  have H : (chart (delta u : Zp) (G p u) (v : Zp) (a : Zp) t).map (algebraMap Zp W) =
      equation p u v a t := by
    rw [map_chart, equation]
    simp only [map_natCast]
    rfl
  rw [polynomial, ← H, map_map, map_map, ← IsScalarTower.algebraMap_eq Zp Qp L,
    ← IsScalarTower.algebraMap_eq Zp W L]

/-- A polynomial split by the unramified quadratic field splits already over
the base field or has that quadratic field itself as a splitting field. -/
theorem splitting_field {f : Qp[X]} (hs : (f.map (algebraMap Qp L)).Splits) :
    f.Splits ∨ f.IsSplittingField Qp L := by
  have prime : Nat.Prime (Module.finrank Qp L) := by rw [fraction_degree]; decide
  have dichotomy := (IntermediateField.isSimpleOrder_of_finrank_prime Qp L prime).eq_bot_or_eq_top
    (IntermediateField.adjoin Qp (f.rootSet L))
  rcases dichotomy with h | h
  · left
    apply hs.of_splits_algebraMap
    intro x hx
    apply IntermediateField.mem_bot.mp
    rw [← h]
    exact IntermediateField.subset_adjoin Qp (f.rootSet L) hx
  · exact Or.inr (isSplittingField_iff_intermediateField.mpr ⟨hs,h⟩)

/-- Both integral-depth branches give a separable degree-six polynomial over Q_p.
The splitting field is the base field or the explicit unramified quadratic field. -/
theorem chart_splitting (u : ℚ) (v a : Zpˣ) (t : Zp) {m l : ℕ}
    (T : SexticFibre (monicSextic (fromPadics p t)) ((p : W)^m))
    (hc : conditions (equation p u v a t) T l) :
    (polynomial p u v a t).natDegree = 6 ∧ (polynomial p u v a t).Separable ∧
    ((polynomial p u v a t).Splits ∨ (polynomial p u v a t).IsSplittingField Qp L) := by
  let f := monicSextic (fromPadics p t)
  let b : W := -6*(delta u : W)*fromPadics p (G p u)*fromPadics p (v:Zp)*(fromPadics p (a:Zp))^2
  have lead : (equation p u v a t).leadingCoeff = b := leading ..
  have hb : b ≠ 0 := by
    intro h
    have hh := hc.1
    rw [lead, h, addVal_zero] at hh
    exact ENat.natCast_ne_top l hh.symm
  let ι := algebraMap W L
  have hι : Function.Injective ι := IsFractionRing.injective W L
  have hιb := (map_ne_zero_iff ι hι).mpr hb
  have hm : (polynomial p u v a t).map (algebraMap Qp L) = C (ι b) * f.map ι := by
    rw [polynomial_map]
    change (C b * f).map ι = _
    rw [Polynomial.map_mul, map_C]
  obtain ⟨hd, hn, hs⟩ := HenselTriples.splitsSix T.triples T.nonzero T.degree
  have sf : (C (ι b) * f.map ι).Splits := (Splits.C _).mul (hs.map ι)
  have sf' : ((polynomial p u v a t).map (algebraMap Qp L)).Splits := hm ▸ sf
  refine ⟨?_, (separable_map (algebraMap Qp L)).mp ?_, splitting_field p sf'⟩
  · rw [← natDegree_map (p := polynomial p u v a t) (algebraMap Qp L), hm,
      natDegree_C_mul hιb, natDegree_map_eq_of_injective hι]
    exact hd
  · rw [hm]
    apply (nodup_roots_iff_of_splits (mul_ne_zero (C_ne_zero.mpr hιb)
      ((Polynomial.map_ne_zero_iff hι).mpr T.nonzero)) sf).mp
    rw [roots_C_mul _ hιb, hs.roots_map_of_injective hι]
    exact Multiset.Nodup.map hι hn

end
end ZInQBlueprint.GoodReductionCharts

#print axioms ZInQBlueprint.GoodReductionCharts.polynomial_map
#print axioms ZInQBlueprint.GoodReductionCharts.splitting_field
#print axioms ZInQBlueprint.GoodReductionCharts.chart_splitting
