import LowPool

namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres
noncomputable section

/-- Odd contacts outside the original cutoff partition into orders 1,5
modulo 6, and orders 3 modulo 6. -/
theorem odd_classes {A B:ℤ} (cop:Int.gcd A B=1) :
    oddProduct A B=classProduct oldCutoff .oddNoncube A B * classProduct oldCutoff .oddCube A B := by
  let row (i:Fin 5):=classSet oldCutoff .oddNoncube i A B∪classSet oldCutoff .oddCube i A B
  have char (i:Fin 5) (p:ℕ) : p∈row i ↔ p∈formPrimes i A B ∧ p∉oldCutoff ∧ order i A B p%2=1:=by
    simp only [row,classSet,Finset.mem_union,Finset.mem_filter,Finset.mem_sdiff]
    by_cases h:order i A B p%2=1 <;> by_cases e:order i A B p%3=0 <;> simp [kind,h,e]
  have union:oddSupport A B=Finset.univ.biUnion row:=by
    ext p
    rw [Finset.mem_biUnion]
    constructor
    · intro m
      obtain ⟨pr,out,i,positive,odd⟩:=mem_oldContactPrimes.mp m
      rw [padicValInt,←Nat.factorization_def _ pr] at positive odd
      have ord:(order i A B p)%2=1:=by obtain ⟨k,h⟩:=odd;unfold order;omega
      have pm:p∈(oldForm i A B).natAbs.primeFactors:=by rw [←Nat.support_factorization];exact Finsupp.mem_support_iff.mpr positive.ne'
      exact ⟨i,Finset.mem_univ _,(char i p).mpr ⟨pm,out,ord⟩⟩
    · rintro ⟨i,_,m⟩
      obtain ⟨pm,out,ord⟩:=(char i p).mp m
      have pr:=Nat.prime_of_mem_primeFactors pm
      exact mem_oldContactPrimes.mpr ⟨pr,out,i,by
        rw [padicValInt,←Nat.factorization_def _ pr];unfold order at ord;omega,by
        rw [padicValInt,←Nat.factorization_def _ pr];unfold order at ord;exact Nat.odd_iff.mpr ord⟩
  unfold oddProduct classProduct
  rw [union,←Finset.prod_mul_distrib]
  calc
    primeProduct (Finset.univ.biUnion row)=∏ i:Fin 5,primeProduct (row i):=by
      apply Finset.prod_biUnion
      intro i _ j _ ij
      apply Finset.disjoint_left.mpr
      intro p m n
      have a:=(char _ _).mp m
      have b:=(char _ _).mp n
      exact ij (unique_form cop a.2.1 a.1 b.1)
    _ =_:=by
      apply Finset.prod_congr rfl
      intro i _
      apply Finset.prod_union
      apply Finset.disjoint_left.mpr
      intro p h h'
      have a:=(Finset.mem_filter.mp h).2
      have b:=(Finset.mem_filter.mp h').2
      exact (by decide:Kind.oddNoncube≠Kind.oddCube) (a.symm.trans b)

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.odd_classes
