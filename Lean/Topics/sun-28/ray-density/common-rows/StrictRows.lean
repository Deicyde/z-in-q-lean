import ActualRecurrence

namespace Sun28.CommonRows
open Finset Sun28.PrimeTransfer Sun28.FinitePattern Sun28.PrimeValues Sun28.ContactFactors Sun28.SinglePrime
open scoped Classical
noncomputable section

/-- At every prescribed height and prime lower bound a finite rectangle recovers
positive mass that the former inert obstruction excluded, for the actual list of shifts. -/
theorem strict_rectangle (narrow:NarrowClassRecurrence) (A:Fin 3→ℚ)
    {K p:ℕ} (seven:7≤K) (lower:K<p) (prime:p.Prime) (inert:p%4=3)
    (d H Y:ℕ) (dp:0<d) :
    ∃u w:ℕ,0<w ∧ d∣w ∧ H*((dilation A)*w)^2<u ∧
      (∀i:↥(shifts A),∃r>Y,(r:ℤ)=form A (u,w) i ∧ oneClass p r) ∧
      0< moment A d K u w (fun z=>collisions A K p z=0 ∧ obstruction A p z) := by
  obtain ⟨u,w,wp,div,high,seq,live,old,clear⟩:=narrow_recovered narrow A seven lower prime inert d H Y dp
  let z:ℕ×ℕ:=(u,w)
  have up:0<u:=(Nat.zero_le _).trans_lt high
  have low:u/2<u:=Nat.div_lt_self up (by decide)
  have mem:z∈parameterBox d u w:=mem_filter.mpr
    ⟨mem_product.mpr ⟨mem_Ioc.mpr ⟨low,le_rfl⟩,mem_Icc.mpr ⟨wp,le_rfl⟩⟩,div⟩
  let f:ℕ×ℕ→ℝ:=fun a=>if collisions A K p a=0 ∧ obstruction A p a then patternWeight A K K a else 0
  have nn (a:ℕ×ℕ) (_:a∈parameterBox d u w):0≤f a:=by unfold f;split <;> first | exact base_nonneg _ _ _ | exact le_rfl
  have pos:0<f z:=by
    dsimp only [f];rw [ite_eq_left ⟨clear,old⟩]
    exact lt_of_le_of_ne (base_nonneg _ _ _) (Ne.symm live)
  refine ⟨u,w,wp,div,high,seq,(pos.trans_le (Finset.single_le_sum nn mem)).trans_eq ?_⟩
  unfold moment
  apply Finset.sum_congr rfl
  intro a _
  by_cases h:collisions A K p a=0 ∧ obstruction A p a <;> simp [f,h]

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.strict_rectangle
