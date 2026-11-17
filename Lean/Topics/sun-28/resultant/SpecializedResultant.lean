import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! Specialization of the Sylvester resultant at fixed sizes and a monic first equation. -/
open Polynomial
namespace ZInQBlueprint.SunResultant
noncomputable section
variable {R L : Type*} [CommRing R] [Field L] [IsAlgClosed L]

/-- Keep the sizes of the original Sylvester matrix when applying φ. The product
runs over roots with multiplicity, including all specializations where g loses degree. -/
theorem specialize_resultant (φ : R →+* L) (f g : R[X]) (hf : f.Monic) :
    φ (f.resultant g) = ((f.map φ).roots.map (g.map φ).eval).prod := by
  rw [← resultant_map_map f g f.natDegree g.natDegree φ, ← hf.natDegree_map φ]
  rw [resultant_eq_prod_eval _ _ _ natDegree_map_le (IsAlgClosed.splits _)]
  simp [(hf.map φ).leadingCoeff]

/-- The elimination condition is exact at every parameter value, also when g
specializes to zero or f has repeated roots. A constant monic f contributes no roots. -/
theorem specialize_resultant_zero_iff (φ : R →+* L) (f g : R[X]) (hf : f.Monic) :
    φ (f.resultant g) = 0 ↔ ∃ z : L, (f.map φ).IsRoot z ∧ (g.map φ).IsRoot z := by
  rw [specialize_resultant φ f g hf,Multiset.prod_eq_zero_iff,Multiset.mem_map]
  simp only [mem_roots (hf.map φ).ne_zero,IsRoot.def]

end
end ZInQBlueprint.SunResultant
#print axioms ZInQBlueprint.SunResultant.specialize_resultant
#print axioms ZInQBlueprint.SunResultant.specialize_resultant_zero_iff
