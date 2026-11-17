import PrimitiveParameters
import OddContactObstruction
/-! Rational inputs of odd contact order, in every unramified discrete valuation ring. -/
universe v w
namespace ZInQBlueprint.OddRational
open IsDiscreteValuationRing ZInQBlueprint.IntegralSextic ZInQBlueprint.ResidualFactors
open ZInQBlueprint.PrimitiveParameters ZInQBlueprint.RationalClusters ZInQBlueprint.PadicParameters
noncomputable section
variable (p : ℕ) [Fact p.Prime]
local notation "Zp" => ℤ_[p]

/-- A map that sends p to a uniformizer preserves the normalized order of every nonzero base parameter. -/
theorem mapped_order {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    (ι : Zp →+* S) (hπ : Irreducible (p:S)) {x : Zp} {n : ℕ} (hx : addVal Zp x=(n:ℕ∞)) :
    addVal S (ι x)=(n:ℕ∞) := by
  have hn : x≠0 := by rintro rfl; simp at hx
  obtain ⟨m,v,hm⟩ := eq_unit_mul_pow_irreducible hn PadicInt.irreducible_p
  have e := ENat.natCast_inj.mp ((addVal_def x v PadicInt.irreducible_p m hm).symm.trans hx)
  rw [hm,map_mul,map_pow,map_natCast,AddValuation.map_mul,addVal_eq_zero_iff.mpr (v.isUnit.map _),
    hπ.addVal_pow,zero_add,e]
/-- No nonzero scalar twist of the sextic at odd rational contact splits in the fraction field
of a discrete valuation ring in which p remains a uniformizer. -/
theorem odd_chart (u : ℚ) (hp : 7≤p) (n : ℕ) (hodd : Odd n)
    (hf : addVal Zp (F p u)=(n:ℕ∞)) :
    ∃ t : Zp, ∃ v a : Zpˣ, Coordinates p u t (v:Zp) (a:Zp) ∧
      ∀ {S : Type v} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (ι : Zp →+* S),
        Irreducible (p:S) → ∀ (K : Type w) [Field K] [Algebra S K] [IsFractionRing S K] (l : K),
          l≠0 → ¬ (Polynomial.C l*(DirectCharts.monicSextic (ι t)).map (algebraMap S K)).Splits := by
  have hn : 0<n := by obtain ⟨j,hj⟩ := hodd; omega
  obtain ⟨t,v,a,hc,ht⟩ := positive_parameter p u hp n hn hf
  refine ⟨t,v,a,hc,?_⟩
  intro S _ _ _ ι hπ K _ _ _ l hl
  have h2r : IsUnit (2:Zp) := unit_nat p 2 (by decide) (by omega)
  have h3r : IsUnit (3:Zp) := unit_nat p 3 (by decide) (by omega)
  have h2 : IsUnit (2:S) := by simpa only [map_ofNat] using h2r.map ι
  have h3 : IsUnit (3:S) := by simpa only [map_ofNat] using h3r.map ι
  rw [Polynomial.splits_mul_iff_right (Polynomial.C_ne_zero.mpr hl) (Polynomial.Splits.C l)]
  exact OddContact.not_splits_fraction K h2 h3 hodd (mapped_order p ι hπ ht)

end
end ZInQBlueprint.OddRational
#print axioms ZInQBlueprint.OddRational.mapped_order
#print axioms ZInQBlueprint.OddRational.odd_chart
