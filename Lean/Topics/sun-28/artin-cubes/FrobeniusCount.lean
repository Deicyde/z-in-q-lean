import CountSelection
import CoefficientClass

namespace Sun28.CutoffCount
open Finset Filter Topology Sun28.FinitePattern Sun28.SinglePrime Sun28.ContactFactors Sun28.PrimeClasses ZInQ.Density
open scoped Classical
noncomputable section

/-- The unweighted integer-pair count using just the rational prime and the trace
of the fixed curve y²=x³−x over its residue field. -/
def traceCount (A : Fin 3 → ℚ) (d L N W : ℕ) : ℕ :=
  (((Ioc (N/2) N ×ˢ Icc 1 W).filter (fun z : ℕ × ℕ => d ∣ z.2)).filter
    fun z => ∀ i : ↥(shifts A),
      0≤form A z i ∧ (form A z i).toNat.Prime ∧
        coefficientClass L (form A z i).toNat (traceAt (form A z i).toNat)).card

theorem trace_count_eq (A : Fin 3 → ℚ) (d L N W : ℕ) :
    traceCount A d L N W = count A d L N W := by
  simp only [traceCount,count,common_both_iff]

/-- The remaining analytic statement on ordinary rational integer pairs. The constant α
is fixed before L, while the row j and the successful scales may depend on L. -/
def TraceInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), Sun28.ContactSieve.AdmissibleRoots X c q n →
    ∀ d : ℕ, 0<d → ∃ α : ℝ,0<α ∧ ∀ B : ℕ,∃ L ≥ B, ∀ J : ℕ,∃ j ≥ J,∃ᶠ t : ℕ in atTop,
      let A := Sun28.RealPoleBounds.fixedScale n
      let N := lengthAt t
      let W := rowWidth j N
      α/(L:ℝ)*((N:ℝ)*W)/(Real.log (N:ℝ))^(shifts A).card ≤ traceCount A d L N W

theorem of_trace (h : TraceInputs) : Inputs := by
  intro X c q n roots d dp B D
  let A := Sun28.RealPoleBounds.fixedScale n
  obtain ⟨α,ap,lower⟩ := h X c q n roots d dp
  have existsL (m : ℕ) : ∃ L ≥ max 0 m, rows A d L (α/(L:ℝ)) := by
    obtain ⟨L,l,good⟩ := lower (max 0 m)
    exact ⟨L,l,by simpa only [rows,←trace_count_eq,A] using good⟩
  obtain ⟨L,δ,high,pos,rate,hits⟩ := Sun28.PrimeMass.cofinal_rates ap existsL B D
  exact ⟨L,δ,(le_max_right 0 B).trans high,pos,rate,hits⟩

end
end Sun28.CutoffCount
#print axioms Sun28.CutoffCount.trace_count_eq
#print axioms Sun28.CutoffCount.of_trace
