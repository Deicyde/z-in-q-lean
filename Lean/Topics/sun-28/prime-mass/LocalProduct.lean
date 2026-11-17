import OrdinaryProduct
import HybridCriterion

namespace Sun28.PrimeMass
open Finset Sun28.PrimeLower Sun28.SinglePrime Sun28.ContactFactors
noncomputable section

/-- The ordinary and additional local factors retain a fixed proportion
independently of the final cutoff. -/
theorem local_product (A : Fin 3 → ℚ) [Nonempty ↥(shifts A)] (K L : ℕ) (large : 2810 ≤ K) :
    1/4 ≤ (∏ q ∈ (places K L).attach,
      let _ : Fact q.val.Prime := ⟨(mem_places.mp q.property).2.2⟩
      beta (fun i : ↥(shifts A) => (offset (dilation A) i : ZMod q.val))) *
        ∏ p ∈ places K L,(1-hybridLoss A p) := by
  have h := ordinary_product (fun i : ↥(shifts A) => offset (dilation A) i)
    (by simpa using Sun28.GaussianSelection.shifts_card_le A) K L (by omega)
  have g := hybrid_product A (places K L) (fun p hp => large.trans (mem_places.mp hp).1.le)
  exact (by norm_num : (1:ℝ)/4 = 1/2*(1/2)).le.trans (mul_le_mul h g (by norm_num) (by linarith))

end
end Sun28.PrimeMass
#print axioms Sun28.PrimeMass.local_product
