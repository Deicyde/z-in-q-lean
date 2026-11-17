import ThreeFactors

namespace Sun28.FactorHeights
open Sun28.WitnessHeight Sun28.ScalarQuotients
noncomputable section

/-- Divisibility of the signed class lifts to an actual binary row. -/
theorem prime_in_row {p:ℕ} (pp:p.Prime) {x:ℚ} (pd:p∣(scalarClass x).natAbs):
    ∃i:Fin 4,(p:ℤ)∣value i x := by
  obtain ⟨sf,y,yn,h⟩:=octic_twist x
  obtain ⟨Y,eq⟩:=integral_point sf yn h
  have pi:(p:ℤ)∣scalarClass x:=Int.natAbs_dvd_natAbs.mp (by simpa using pd)
  have prod:(p:ℤ)∣∏i:Fin 4,value i x:=by
    change (p:ℤ)∣∏i:Fin 4,row i x.num x.den
    rw [literal_product,eq];exact dvd_mul_of_dvd_left pi _
  have ip:=Nat.prime_iff_prime_int.mp pp
  obtain ⟨i,_,div⟩:=(ip.dvd_finsetProd_iff _).mp prod
  exact ⟨i,div⟩

/-- A global scalar class with at most one prime outside 2,3,5,7 lies on the three-factor locus. -/
theorem one_prime_concentrated (x:ℚ) (p:ℕ)
    (support:∀q:ℕ,q.Prime → q∣(scalarClass x).natAbs → q∣210 ∨ q=p):
    ∃i:Fin 4,concentrated x i := by
  by_cases hit:p.Prime ∧ p∣(scalarClass x).natAbs
  · obtain ⟨i,hi⟩:=prime_in_row hit.1 hit.2
    exact ⟨i,fun q qp out div=>((support q qp div).resolve_left out) ▸ hi⟩
  · refine ⟨0,fun q qp out div=>?_⟩
    have h:=(support q qp div).resolve_left out
    subst p;exact (hit ⟨qp,div⟩).elim

/-- In particular the prime p may be arbitrarily large, and e may have either sign. -/
theorem prime_times_fixed (x:ℚ) {p:ℕ} (pp:p.Prime) {e:ℤ} (small:e.natAbs∣210)
    (eq:scalarClass x=e*p) : ∃i:Fin 4,concentrated x i := by
  apply one_prime_concentrated x p
  intro q hq div
  rw [eq,Int.natAbs_mul,Int.natAbs_natCast] at div
  exact (hq.dvd_mul.mp div).imp (fun d=>d.trans small) (fun d=>(Nat.prime_dvd_prime_iff_eq hq pp).mp d)

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.prime_in_row
#print axioms Sun28.FactorHeights.one_prime_concentrated
#print axioms Sun28.FactorHeights.prime_times_fixed
