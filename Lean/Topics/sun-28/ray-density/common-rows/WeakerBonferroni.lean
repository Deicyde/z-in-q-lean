import SharedSelection

namespace Sun28.CommonRows
open Finset Filter Sun28.PrimeValues Sun28.PrimeModel Sun28.FinitePattern Sun28.PrimeClasses
open Sun28.PrimeLower Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection
open Sun28.SinglePrime Sun28.MediumSieve Sun28.MixedSieve Sun28.PrimeMass
open private record_of_pattern from NumericalPattern
open scoped Classical
noncomputable section

/-- On the same finite box, local signed exclusion never costs more than the
previous inert residue cutoff or split sum over ordered pairs. -/
theorem one_le_old {A : Fin 3→ℚ} {d K N W p:ℕ} [Fact p.Prime]
    (pos:0<d) (large:exceptionalBound A d<p) :
    onePlaceMass A d K N W p ≤ upperMoment A d K p N W := by
  apply le_trans _ (single_le_upper A d K p N W)
  apply sum_le_sum
  intro z hz
  by_cases live:patternWeight A K K z=0
  · simp [live]
  by_cases hit:signedHit A p z
  · obtain ⟨inside,hd⟩:=mem_filter.mp hz
    have vp:= (mem_Icc.mp (mem_product.mp inside).2).1
    have hy (i:↥(shifts A)) : (-1:ℝ)<(form A z i:ℝ) := by
      have lhs:0≤(form A z i:ℝ):=by exact_mod_cast (form_of_live live i).1
      linarith
    obtain ⟨a,e,_⟩:=record_of_pattern hd vp
      (sub_one_lt (slope A z.1 z.2:ℝ)) hy live
    have reach : signedHit A p (pair a):=by simpa only [e] using hit
    have obs:obstruction A p z := by simpa only [e] using (accepted_hit a pos large reach)
    simp [hit,obs]
  · simp only [ite_eq_right hit]
    split
    next => exact base_nonneg _ _ _
    next => exact le_rfl

/-- Every former cofinal Bonferroni estimate satisfies the new criterion.
The choice of K already permitted taking a larger fixed exceptional bound. -/
theorem from_bonferroni (old:CofinalBonferroni) : PairCorrectedInputs := by
  intro X c q n h d hd B
  let A:=Sun28.RealPoleBounds.fixedScale n
  obtain ⟨K,bk,rows⟩:=old X c q n h d hd (max B (exceptionalBound A d))
  refine ⟨K,(le_max_left _ _).trans bk,fun m D=>?_⟩
  obtain ⟨L,δ,ml,δp,surplus,run⟩:=rows m D
  refine ⟨L,δ,ml,δp,surplus,fun J=>?_⟩
  obtain ⟨j,jJ,freq⟩:=run J
  refine ⟨j,jJ,freq.mono (fun t good=>Or.inl (good.trans ?_))⟩
  apply sub_le_sub_left
  apply sum_le_sum
  intro p hp
  obtain ⟨lo,_,prime⟩:=mem_places.mp hp
  let _ : Fact p.Prime:=⟨prime⟩
  exact one_le_old hd (lt_of_le_of_lt ((le_max_right _ _).trans bk) lo)

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.one_le_old
#print axioms Sun28.CommonRows.from_bonferroni
