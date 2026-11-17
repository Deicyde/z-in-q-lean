import SexticChart

/-! Recovering the original prime support from the two signed sextic coefficients. -/
namespace Sun28.FiveDescent
open Sun28.Ordinary Sun28.FiveMarkTriples Sun28.FiveMarkUnits ZInQ.RouteK

def parameterPrimes (d e : ℤ) : Finset ℕ := d.natAbs.primeFactors ∪ e.natAbs.primeFactors
def twistPrimes (d e : ℤ) := parameterPrimes d e \ oldCutoff

private theorem kernel_primes {u : ℤ} (nz : u≠0) :
    (sqfInt u).natAbs.primeFactors=
      u.natAbs.primeFactors.filter (fun p=>Odd (padicValInt p u)) := by
  have h : (sqfInt u).natAbs=sqfNat u.natAbs := by
    rw [sqfInt,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero nz,Int.natAbs_natCast,one_mul]
  rw [h,sqfNat,Nat.primeFactors_prod (fun p hp=>Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)]
  ext p
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hp
  rw [padicValInt,←Nat.factorization_def _ (Nat.prime_of_mem_primeFactors hp)]

private theorem kernel_member {u : ℤ} (nu : u≠0) {p : ℕ} (prime : p.Prime) :
    p∈(sqfInt u).natAbs.primeFactors ↔ Odd (padicValInt p u) := by
  rw [kernel_primes nu,Finset.mem_filter,and_iff_right_iff_imp]
  intro odd
  have pos : 1≤padicValInt p u := by obtain ⟨k,h⟩:=odd;omega
  exact Nat.mem_primeFactors.mpr ⟨prime,dvd_of_one_le_padicValNat pos,Int.natAbs_ne_zero.mpr nu⟩

private def firstRows : Finset (Fin 5) := {1,2}
private def secondRows : Finset (Fin 5) := {0,1,3,4}

private theorem products (A B : ℤ) :
    F1 A B=∏ i∈firstRows,oldForm i A B ∧
    F2 A B=∏ i∈secondRows,oldForm i A B := by
  norm_num [F1,F2,firstRows,secondRows,oldForm]
  ring

private theorem product_order {p : ℕ} (pr : p.Prime) (f : Fin 5→ℤ)
    (U : Finset (Fin 5)) (off : ∀ j,f j≠0) :
    padicValInt p (∏ j∈U,f j)=∑ j∈U,padicValInt p (f j) := by
  let : Fact p.Prime := ⟨pr⟩
  induction U using Finset.induction_on with
  | empty => simp [padicValInt]
  | @insert a U fresh ih =>
    rw [Finset.prod_insert fresh,Finset.sum_insert fresh,padicValInt,Int.natAbs_mul,
      padicValNat.mul (Int.natAbs_ne_zero.mpr (off _))
        (Int.natAbs_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun j _=>off j)))]
    exact congrArg (fun z=>padicValInt p (f a)+z) ih

private theorem zero_order {p : ℕ} {A B : ℤ} {j : Fin 5} (pr : p.Prime)
    (off : ∀ i,oldForm i A B≠0) (absent : p∉formPrimes j A B) :
    padicValInt p (oldForm j A B)=0 :=
  padicValNat.eq_zero_of_not_dvd (fun h=>absent
    (Nat.mem_primeFactors.mpr ⟨pr,h,Int.natAbs_ne_zero.mpr (off j)⟩))

theorem product_odd_iff {p : ℕ} {A B : ℤ} (pr : p.Prime) (out : p∉oldCutoff)
    (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (U : Finset (Fin 5)) :
    Odd (padicValInt p (∏ j∈U,oldForm j A B)) ↔ ∃ i∈U,Odd (padicValInt p (oldForm i A B)) := by
  rw [product_order pr _ _ off]
  by_cases hit : ∃ i∈U,p∈formPrimes i A B
  · obtain ⟨i,mem,hi⟩:=hit
    have other (j : Fin 5) (ne : j≠i) : padicValInt p (oldForm j A B)=0 :=
      zero_order pr off (fun hj=>ne (unique_form cop out hj hi))
    rw [Finset.sum_eq_single_of_mem i mem (fun j _ ne=>other j ne)]
    constructor
    · exact fun r=>⟨i,mem,r⟩
    · rintro ⟨j,_,h⟩
      by_cases e : j=i
      · simpa only [e] using h
      · rw [other j e] at h; exact False.elim ((by decide : ¬Odd (0:ℕ)) h)
  · push Not at hit
    have z (i : Fin 5) (hi : i∈U) := zero_order pr off (hit i hi)
    rw [Finset.sum_eq_zero z]
    constructor
    · intro h; exact False.elim ((by decide : ¬Odd (0:ℕ)) h)
    · rintro ⟨i,hi,odd⟩;rwa [z i hi] at odd

/-- Each prime outside the exact cutoff divides at most one literal row, and every row
occurs in one of the two products. The shared A row is counted once by union. -/
theorem support_exact {A B : ℤ} (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) :
    oldContactPrimes oldCutoff A B=twistPrimes (D A B) (E A B) := by
  obtain ⟨_,_,nf,ng⟩:=rows off
  ext p
  rw [mem_oldContactPrimes]
  simp only [twistPrimes,parameterPrimes,Finset.mem_sdiff,Finset.mem_union]
  by_cases pr : p.Prime
  · by_cases out : p∉oldCutoff
    · simp only [pr,out,not_false_eq_true,true_and,and_true]
      rw [D,E,kernel_member nf pr,kernel_member ng pr,(products A B).1,(products A B).2,
        product_odd_iff pr out cop off,product_odd_iff pr out cop off]
      constructor
      · rintro ⟨i,_,od⟩
        have covers : ∀ j : Fin 5, j∈firstRows ∨ j∈secondRows := by decide
        exact (covers i).elim (fun h=>Or.inl ⟨i,h,od⟩) (fun h=>Or.inr ⟨i,h,od⟩)
      · rintro (⟨i,_,od⟩|⟨i,_,od⟩) <;>
          exact ⟨i,by obtain ⟨k,h⟩:=od;omega,od⟩
    · simp [out]
  · simp only [pr,false_and,false_iff,not_and]
    exact fun h=>h.elim (fun hd=>False.elim (pr (Nat.prime_of_mem_primeFactors hd)))
      (fun he=>False.elim (pr (Nat.prime_of_mem_primeFactors he)))

/-- Full twist support has only one fixed cutoff cost, even at the shared A row. -/
theorem fixed_cost (d e : ℤ) :
    primeProduct (parameterPrimes d e)≤cutoffProduct*primeProduct (twistPrimes d e) := by
  let T:=parameterPrimes d e
  have sub : T⊆oldCutoff ∪ (T \ oldCutoff) := by
    intro p hp;by_cases h:p∈oldCutoff
    · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hp,h⟩)
  have disj : Disjoint oldCutoff (T \ oldCutoff) := Finset.disjoint_left.mpr fun _ h q=>(Finset.mem_sdiff.mp q).2 h
  have pos (p : ℕ) (mem : p∈oldCutoff ∪ (T \ oldCutoff)) : 1≤p := by
    rcases Finset.mem_union.mp mem with h|h
    · exact (Finset.mem_filter.mp h).2.one_lt.le
    · rcases Finset.mem_union.mp (Finset.mem_sdiff.mp h).1 with q|q <;> exact (Nat.prime_of_mem_primeFactors q).one_lt.le
  have bound:=Finset.prod_le_prod_of_subset_of_one_le (f:=id) sub (fun p hp _=>pos p hp)
  simpa only [T,primeProduct,cutoffProduct,twistPrimes,Finset.prod_union disj,id_eq] using bound

end Sun28.FiveDescent
#print axioms Sun28.FiveDescent.product_odd_iff
#print axioms Sun28.FiveDescent.support_exact
#print axioms Sun28.FiveDescent.fixed_cost
