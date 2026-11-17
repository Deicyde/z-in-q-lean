import MarkOverlap

/-! The product of the five squarefree parts on the primitive slope line. -/
namespace ZInQBlueprint.FiveCovers
open Finset Sun28.Ordinary Sun28.HeightFibres Sun28.FiveMarkUnits ZInQ.RouteK
noncomputable section

def support (A B : ℤ) := univ.biUnion fun i : Fin 5 => rowPrimes i A B
def weight (A B : ℤ) := ∏ i : Fin 5,(kernel i A B).natAbs

private theorem row_subset (i : Fin 5) (A B : ℤ) : rowPrimes i A B ⊆ support A B :=
  fun _ h=> mem_biUnion.mpr ⟨i,mem_univ _,h⟩

theorem product_by_prime {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    weight A B = ∏ p ∈ support A B,p^(hitRows A B p).card := by
  let S := support A B
  have rr (i : Fin 5) : (kernel i A B).natAbs = ∏ p ∈ S,if p∈rowPrimes i A B then p else 1 := by
    rw [radical_row i (off i),←prod_filter]
    have same : S.filter (fun p=>p∈rowPrimes i A B)=rowPrimes i A B := by
      ext p
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun h=>row_subset i A B h)
    rw [same];rfl
  unfold weight
  simp_rw [rr]
  rw [prod_comm]
  apply prod_congr rfl
  intro p _
  rw [←prod_filter]
  simp only [prod_const,hitRows]

private def atPrime (p : ℕ) :=
  (if p=2 then 2 else 1)*(if p=3 then 9 else 1)*(if p=5 then 25 else 1)*(if p=7 then 49 else 1 : ℕ)

private theorem max_power (p : ℕ) : p^multiplicity p=p*atPrime p := by
  by_cases p2 : p=2
  · subst p; decide
  by_cases p3 : p=3
  · subst p; decide
  by_cases p5 : p=5
  · subst p; decide
  by_cases p7 : p=7
  · subst p; decide
  simp [multiplicity,atPrime,p2,p3,p5,p7]

private theorem excess (S : Finset ℕ) : (∏ p ∈ S,atPrime p) ∣ 22050 := by
  simp only [atPrime,prod_mul_distrib,prod_ite_eq']
  by_cases h₂ : 2∈S <;> by_cases h₃ : 3∈S <;> by_cases h₅ : 5∈S <;> by_cases h₇ : 7∈S <;>
    simp [h₂,h₃,h₅,h₇]

/-- Sharp universal divisibility, including all four exceptional residue characteristics. -/
theorem joint_divides {A B : ℤ} (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) :
    weight A B ∣ 22050*primeProduct (support A B) := by
  let S:=support A B
  have upper : (∏ p ∈ S,p^(hitRows A B p).card) ∣ ∏ p ∈ S,p^multiplicity p := by
    apply prod_dvd_prod_of_dvd
    intro p hp
    obtain ⟨i,_,hi⟩ := mem_biUnion.mp hp
    exact pow_dvd_pow p (prime_multiplicity cop (Nat.prime_of_mem_primeFactors (mem_filter.mp hi).1))
  rw [product_by_prime off]
  apply upper.trans
  simp_rw [max_power]
  rw [prod_mul_distrib,mul_comm 22050]
  exact Nat.mul_dvd_mul_left _ (excess S)

/-- The common support uses the literal odd-contact radical outside Glazer's cutoff. -/
theorem support_outside (A B : ℤ) : support A B \ oldCutoff=oddSupport A B := by
  ext p
  constructor
  · intro hp
    obtain ⟨hs,cut⟩:=mem_sdiff.mp hp
    obtain ⟨i,_,hi⟩:=mem_biUnion.mp hs
    obtain ⟨mem,par⟩:=mem_filter.mp hi
    have pr:=Nat.prime_of_mem_primeFactors mem
    have odd : Odd (padicValInt p (oldForm i A B)) := by
      simpa only [padicValInt,←Nat.factorization_def _ pr] using par
    have pos : 0<padicValInt p (oldForm i A B) := by obtain ⟨q,e⟩:=odd;omega
    exact mem_oldContactPrimes.mpr ⟨pr,cut,i,pos,odd⟩
  · intro hp
    obtain ⟨pr,cut,i,pos,odd⟩:=mem_oldContactPrimes.mp hp
    have ord : 0<(oldForm i A B).natAbs.factorization p := by
      simpa only [padicValInt,←Nat.factorization_def _ pr] using pos
    have mem : p∈(oldForm i A B).natAbs.primeFactors := by
      rw [←Nat.support_factorization,Finsupp.mem_support_iff];omega
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨i,mem_univ _,mem_filter.mpr ⟨mem,by
      simpa only [padicValInt,←Nat.factorization_def _ pr] using odd⟩⟩,cut⟩

theorem weight_bound {A B : ℤ} (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) :
    weight A B ≤ 22050*heightRadical A B := by
  have sub : support A B ⊆ oldCutoff ∪ oddSupport A B := by
    intro p h
    by_cases hc : p∈oldCutoff
    · exact mem_union_left _ hc
    · exact mem_union_right _ (support_outside A B ▸ mem_sdiff.mpr ⟨h,hc⟩)
  have dis : Disjoint oldCutoff (oddSupport A B) :=
    disjoint_left.mpr fun _ hc ho=>(mem_oldContactPrimes.mp ho).2.1 hc
  have div := Finset.prod_dvd_prod_of_subset _ _ (fun p : ℕ=>p) sub
  rw [prod_union dis] at div
  have pos := Nat.mul_pos pos_cutoff (pos_odd A B)
  exact Nat.le_of_dvd (Nat.mul_pos (by decide) pos)
    ((joint_divides cop off).trans (Nat.mul_dvd_mul_left 22050 div))

end
end ZInQBlueprint.FiveCovers
#print axioms ZInQBlueprint.FiveCovers.product_by_prime
#print axioms ZInQBlueprint.FiveCovers.joint_divides
#print axioms ZInQBlueprint.FiveCovers.support_outside
#print axioms ZInQBlueprint.FiveCovers.weight_bound
