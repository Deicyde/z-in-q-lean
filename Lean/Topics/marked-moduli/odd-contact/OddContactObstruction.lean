import OddContact
import OddContactProduct

/-! The obstruction on the odd contact branch of the genus-two sextic. -/
namespace ZInQBlueprint.OddContact
open Polynomial IsDiscreteValuationRing DirectCharts

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The monic contact sextic cannot split in a DVR in residue characteristic
different from two and three when the parameter has finite odd order. -/
theorem not_splits (h₂ : IsUnit (2:R)) (h₃ : IsUnit (3:R)) {t : R} {n : ℕ}
    (hodd : Odd n) (ht : addVal R t = (n:ℕ∞)) : ¬ (monicSextic t).Splits :=
  OddContactProduct.not_splits hodd.pos ht h₂ (fun _ hx hres =>
    (root_valuation h₂ h₃ hodd ht hx hres).ge)

/-- The same obstruction holds over any fraction field of the DVR. -/
theorem not_splits_fraction (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (h₂ : IsUnit (2:R)) (h₃ : IsUnit (3:R)) {t : R} {n : ℕ}
    (hodd : Odd n) (ht : addVal R t = (n:ℕ∞)) :
    ¬ ((monicSextic t).map (algebraMap R K)).Splits :=
  OddContactProduct.not_splits_fraction K hodd.pos ht h₂ (fun _ hx hres =>
    (root_valuation h₂ h₃ hodd ht hx hres).ge)

variable {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]

/-- A ring map scales finite orders by the order of the image of a uniformizer. -/
theorem mapped_order_mul (ι : R →+* S) {π t : R} {e n : ℕ}
    (hπ : Irreducible π) (he : addVal S (ι π) = (e:ℕ∞))
    (ht : addVal R t = (n:ℕ∞)) : addVal S (ι t) = ((n*e:ℕ):ℕ∞) := by
  have h0 : t ≠ 0 := by rintro rfl; simp at ht
  obtain ⟨m,u,hm⟩ := eq_unit_mul_pow_irreducible h0 hπ
  have hmn := ENat.natCast_inj.mp ((addVal_def t u hπ m hm).symm.trans ht)
  rw [hm,map_mul,map_pow,addVal_mul,addVal_eq_zero_iff.mpr (u.isUnit.map ι),zero_add,
    addVal_pow,he,hmn,nsmul_eq_mul,Nat.cast_mul]

/-- In any DVR extension where the sextic at odd contact splits over the fraction field,
the normalized ramification index must be even.  No completeness assumption is needed. -/
theorem even_ramification_of_splits (ι : R →+* S) (K : Type*) [Field K] [Algebra S K]
    [IsFractionRing S K] (h₂ : IsUnit (2:S)) (h₃ : IsUnit (3:S)) {π t : R} {e n : ℕ}
    (hπ : Irreducible π) (he : addVal S (ι π) = (e:ℕ∞)) (hodd : Odd n)
    (ht : addVal R t = (n:ℕ∞)) (hs : ((monicSextic (ι t)).map (algebraMap S K)).Splits) :
    Even e := by
  by_contra h
  exact not_splits_fraction K h₂ h₃ (hodd.mul (Nat.not_even_iff_odd.mp h))
    (mapped_order_mul ι hπ he ht) hs

end ZInQBlueprint.OddContact
#print axioms ZInQBlueprint.OddContact.not_splits
#print axioms ZInQBlueprint.OddContact.not_splits_fraction
#print axioms ZInQBlueprint.OddContact.mapped_order_mul
#print axioms ZInQBlueprint.OddContact.even_ramification_of_splits
