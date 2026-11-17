import RowPool

namespace Sun28.HeightCubics
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp
open private away_minor from RowPool
noncomputable section

theorem exact_hidden (r:ThreeRows) {A B:ℤ} (off:∀ i,oldForm i A B≠0) :
    mixedPlaces (left r A B) (right r A B) (baseRow r A B) \ support A B =
      defective r.b A B ∪ residualMark A B r.center := by
  ext p
  constructor
  · intro h
    have ⟨mem,unseen⟩:=Finset.mem_sdiff.mp h
    exact (Finset.mem_union.mp (chart_primes r off mem)).resolve_left unseen
  · intro h
    have boost {i j k:Fin 5} (jk:j≠k) (hp:p∈formPrimes i A B) :
        p∈(det j k*oldForm i A B).natAbs.primeFactors:=by
      rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (det_ne jk)) (Int.natAbs_ne_zero.mpr (off _))]
      exact Finset.mem_union_right _ hp
    rcases Finset.mem_union.mp h with q|r0
    · obtain ⟨inc,pow⟩:=Finset.mem_filter.mp q
      obtain ⟨dv,out⟩:=Finset.mem_sdiff.mp inc
      have pr:=Nat.prime_of_mem_primeFactors dv
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨boost r.ia.symm dv,?_⟩)),out⟩
      change (det r.a r.center * oldForm r.b A B).natAbs.factorization p%3≠0
      rw [away_minor pr out r.ia.symm (off _)];exact pow
    · obtain ⟨dv,out⟩:=Finset.mem_sdiff.mp r0
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_union_right _ (boost r.ab dv)),out⟩

/-- Choose any ordered center and cubic row. The remaining square row is free. -/
theorem pair_budget {A B:ℤ} (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (i j:Fin 5) (ij:i≠j) (budget:hidden i A B*noncubic j A B≤heightRadical A B^10) : MixedCovered A B := by
  have pick:∀ i j:Fin 5,i≠j → ∃ k:Fin 5,i≠k ∧ k≠j:=by decide
  obtain ⟨k,ik,kj⟩:=pick i j ij
  let r:ThreeRows:=⟨i,k,j,ik,ij,kj⟩
  apply mixed_of_conductor r
  have h:=chart_cost r cop off
  change mixedChart r A B≤heightRadical A B*(noncubic j A B*hidden i A B) at h
  rw [mul_comm (noncubic _ _ _)] at h
  exact h.trans ((Nat.mul_le_mul_left _ budget).trans_eq (by ring))

theorem failure_forces_pairs {A B:ℤ} (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (fail:¬MixedCovered A B) (i j:Fin 5) (ij:i≠j) :
    heightRadical A B^10<hidden i A B*noncubic j A B :=
  lt_of_not_ge (fun lo=>fail (pair_budget cop off i j ij lo))

end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.exact_hidden
#print axioms Sun28.HeightCubics.pair_budget
#print axioms Sun28.HeightCubics.failure_forces_pairs
