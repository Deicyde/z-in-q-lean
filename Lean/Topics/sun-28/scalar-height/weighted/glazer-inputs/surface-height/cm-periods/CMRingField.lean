import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
namespace ZInQBlueprint.CMPeriods
/-- The embeddings of the residue field give distinct geometric lifts. The full
Atkin--Lehner group has sixteen elements and acts transitively on this fibre. -/
theorem residue_degree_le {L : IntermediateField ℚ ℂ} [FiniteDimensional ℚ L]
    {X : Type*} [Fintype X] (point : (L →ₐ[ℚ] ℂ) → X) (separates : Function.Injective point)
    (deck : Fin 16 → X) (covers : Function.Surjective deck) : Module.finrank ℚ L ≤ 16 := by
  rw [← AlgHom.card ℚ L ℂ]
  exact (Fintype.card_le_of_injective point separates).trans
    (by simpa only [Fintype.card_fin] using Fintype.card_le_of_surjective deck covers)
/-- Shimura reciprocity identifies the ring class field with the compositum of
the CM field and the residue field. Extension of scalars cannot increase degree. -/
theorem ring_class_degree_le (K L : IntermediateField ℚ ℂ) {h : ℕ}
    (quadratic : Module.finrank ℚ K = 2)
    (reciprocity : Module.finrank ℚ ↥(K ⊔ L) = 2*h)
    (rationalFibre : Module.finrank ℚ L ≤ 16) : h ≤ 16 := by
  have bound := IntermediateField.finrank_sup_le K L
  rw [quadratic,reciprocity] at bound
  omega
end ZInQBlueprint.CMPeriods
#print axioms ZInQBlueprint.CMPeriods.residue_degree_le
#print axioms ZInQBlueprint.CMPeriods.ring_class_degree_le
