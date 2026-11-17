import OddRadicalField
import OddTraceRank

/-! Concrete parts of the field condition in odd genus rows. -/
namespace ZInQBlueprint.TYZ.Specialization
noncomputable section
open IntermediateField

/-- The second bracket vanishes on every squarefree class-five index
whose prime factors are all 1 modulo 4. No CM row is needed on this whole
subfamily. -/
theorem secondBracket_zero_of_primes_one_mod_four {n : ℕ} (hs : Squarefree n)
    (h5 : n%8=5) (hpr : ∀ p, p.Prime → p ∣ n → p%4=1) :
    ZInQ.RouteK.Rank5b.T5bCl n = 0 := by
  rw [←printedCoefficient_mod_two h5 hs,TraceAction.printedCoefficient_split h5]
  have he : (n.divisors.filter (fun e => e%8=7)) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨he,h7⟩ := Finset.mem_filter.mp he
    have hdiv := (Nat.mem_divisors.mp he).1
    have prodOne (t : Finset ℕ) (ht : ∀ q∈t, q%4=1) : (∏ q∈t, q)%4=1 := by
      induction t using Finset.induction_on with
      | empty => decide
      | @insert q t hq ih =>
        rw [Finset.prod_insert hq,Nat.mul_mod,ht q (Finset.mem_insert_self ..),
          ih (fun k hk => ht k (Finset.mem_insert_of_mem hk))]
    have hmod : e%4=1 := by
      rw [←Nat.prod_primeFactors_of_squarefree (hs.squarefree_of_dvd hdiv)]
      apply prodOne
      exact fun q hq => hpr q (Nat.mem_primeFactors.mp hq).1 ((Nat.mem_primeFactors.mp hq).2.1.trans hdiv)
    omega
  simp [he]


/-- An odd second bracket forces two distinct prime factors both congruent
to three modulo four. Thus the local trace, field and character hypotheses
are needed only on this narrower family. -/
theorem two_three_mod_four_primes_of_odd_row {n : ℕ} (hs : Squarefree n)
    (h5 : n%8=5) (ho : ZInQ.RouteK.Rank5b.T5bCl n = 1) :
    ∃ p q : ℕ, p.Prime ∧ p ∣ n ∧ p%4=3 ∧ q.Prime ∧ q ∣ n ∧ q%4=3 ∧ p≠q := by
  classical
  have hn : n ≠ 0 := by omega
  have hnodd : Odd n := Nat.odd_iff.mpr (by omega)
  have ex : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p%4≠1 := by
    by_contra hall
    push Not at hall
    exact zero_ne_one ((secondBracket_zero_of_primes_one_mod_four hs h5 hall).symm.trans ho)
  obtain ⟨p,hp,hpd,hp1⟩ := ex
  have oddp := Nat.odd_iff.mp (hnodd.of_dvd_nat hpd)
  have hp3 : p%4=3 := by omega
  let s := n.primeFactors.erase p
  have prod : p * (∏ q ∈ s, q) = n := by
    exact (Finset.mul_prod_erase n.primeFactors (fun q : ℕ => q)
      (Nat.mem_primeFactors.mpr ⟨hp,hpd,hn⟩)).trans (Nat.prod_primeFactors_of_squarefree hs)
  have exq : ∃ q ∈ s, q%4≠1 := by
    by_contra hall
    push Not at hall
    have one (l : Finset ℕ) (hl : ∀ q ∈ l, q%4=1) : (∏ q∈l, q)%4=1 := by
      induction l using Finset.induction_on with
      | empty => decide
      | @insert x l hx ih =>
        rw [Finset.prod_insert hx,Nat.mul_mod,hl x (Finset.mem_insert_self ..),
          ih (fun q hq => hl q (Finset.mem_insert_of_mem hq))]
    have hi := congrArg (·%4) prod
    rw [Nat.mul_mod,hp3,one s hall] at hi
    omega
  obtain ⟨q,hq,hq1⟩ := exq
  obtain ⟨hne,hqn⟩ := Finset.mem_erase.mp hq
  obtain ⟨hqp,hqd,_⟩ := Nat.mem_primeFactors.mp hqn
  have oddq := Nat.odd_iff.mp (hnodd.of_dvd_nat hqd)
  exact ⟨p,q,hp,hpd,hp3,hqp,hqd,by omega,hne.symm⟩

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.secondBracket_zero_of_primes_one_mod_four
#print axioms ZInQBlueprint.TYZ.Specialization.two_three_mod_four_primes_of_odd_row
