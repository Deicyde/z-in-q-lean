import TenTriples

/-! Keep the contribution of odd-contact primes in each conductor before pooling. -/
namespace Sun28.FiveMarkTriples
open Sun28.Ordinary Sun28.FiveMarkUnits

def freeMark (A B : ℤ) (i : Fin 5) := formPrimes i A B \ oldCutoff

def actualConductor (t : Fin 10) (A B : ℤ) :=
  primeProduct (oldCutoff ∪ triplePrimes (first t) (second t) (third t) A B)

private theorem free_product {A B : ℤ} (primitive : Int.gcd A B=1) (U : Finset (Fin 5)) :
    primeProduct (U.biUnion (freeMark A B)) = ∏ i∈U,primeProduct (freeMark A B i) := by
  apply Finset.prod_biUnion
  intro i _ j _ distinct
  apply Finset.disjoint_left.mpr
  intro p h h'
  obtain ⟨fi,away⟩:=Finset.mem_sdiff.mp h
  exact distinct (unique_form primitive away fi (Finset.mem_sdiff.mp h').1)

private theorem free_triple (t : Fin 10) (A B : ℤ) :
    (tripleIndex t).biUnion (freeMark A B)=
    triplePrimes (first t) (second t) (third t) A B \ oldCutoff := by
  simp only [tripleIndex,triplePrimes,freeMark,Finset.biUnion_insert,Finset.singleton_biUnion,
    Finset.union_sdiff_distrib,Finset.union_assoc]

private theorem at_triple (t : Fin 10) {A B : ℤ} (primitive : Int.gcd A B=1) :
    actualConductor t A B=cutoffProduct*(∏ i∈tripleIndex t,primeProduct (freeMark A B i)) := by
  rw [← free_product primitive,free_triple]
  let C:=oldCutoff
  let T:=triplePrimes (first t) (second t) (third t) A B
  have dis : Disjoint C (T\C) := Finset.disjoint_left.mpr (fun _ h hr => (Finset.mem_sdiff.mp hr).2 h)
  change (∏ p∈C∪T,p)=(∏ p∈C,p)*(∏ p∈T\C,p)
  rw [← Finset.prod_union dis,Finset.union_sdiff_self_eq_union]

private theorem all_free (A B : ℤ) :
    Finset.univ.biUnion (freeMark A B)=oddSupport A B ∪ totalResidualSupport A B := by
  ext p
  constructor
  · intro h
    obtain ⟨i,_,f⟩:=Finset.mem_biUnion.mp h
    obtain ⟨fi,away⟩:=Finset.mem_sdiff.mp f
    by_cases odd : p∈oddSupport A B
    · exact Finset.mem_union_left _ odd
    · have outside : p∉oldCutoff∪oddSupport A B := fun h => (Finset.mem_union.mp h).elim away odd
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨fi,outside⟩⟩)
  · intro h
    rcases Finset.mem_union.mp h with odd|even
    · obtain ⟨atForm,away⟩:=Finset.mem_sdiff.mp odd
      obtain ⟨i,_,f⟩:=Finset.mem_biUnion.mp atForm
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp f).1,away⟩⟩
    · obtain ⟨i,_,f⟩:=Finset.mem_biUnion.mp even
      obtain ⟨fi,away⟩:=Finset.mem_sdiff.mp f
      exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_sdiff.mpr ⟨fi,fun h=>away (Finset.mem_union_left _ h)⟩⟩

private theorem at_all {A B : ℤ} (primitive : Int.gcd A B=1) :
    (∏ i:Fin 5,primeProduct (freeMark A B i))=oddProduct A B*totalResidual A B := by
  rw [← free_product primitive,all_free]
  have dis : Disjoint (oddSupport A B) (totalResidualSupport A B) := by
    apply Finset.disjoint_left.mpr
    intro p h r
    obtain ⟨i,_,f⟩:=Finset.mem_biUnion.mp r
    exact (Finset.mem_sdiff.mp f).2 (Finset.mem_union_right _ h)
  exact Finset.prod_union dis

theorem incidence_count (f : Fin 5→ℕ) :
    (∏ t : Fin 10, ∏ i∈tripleIndex t,f i)=(∏ i : Fin 5,f i)^6 := by
  calc
    _ = ∏ t : Fin 10, ∏ i : Fin 5, if i∈tripleIndex t then f i else 1 := by
      apply Finset.prod_congr rfl
      intro t _
      rw [← Finset.prod_filter]
      simp
    _ = ∏ i : Fin 5, ∏ t : Fin 10, if i∈tripleIndex t then f i else 1 := Finset.prod_comm
    _ = ∏ i : Fin 5, (f i)^6 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Finset.prod_filter,Finset.prod_const,six_occurrences]
    _ = _ := Finset.prod_pow _ _ _


theorem conductor_pool {A B : ℤ} (primitive : Int.gcd A B=1) :
    (∏ t : Fin 10,actualConductor t A B)=cutoffProduct^10*(oddProduct A B*totalResidual A B)^6 := by
  simp_rw [at_triple _ primitive]
  rw [Finset.prod_mul_distrib,incidence_count,at_all primitive]
  simp

theorem bad_conductors_force_total {A B : ℤ} (primitive : Int.gcd A B=1)
    (failure : ∀ t : Fin 10,(cutoffProduct*oddProduct A B)^23<actualConductor t A B) :
    cutoffProduct^220*oddProduct A B^224<totalResidual A B^6 := by
  let C:=cutoffProduct
  let O:=oddProduct A B
  let E:=totalResidual A B
  have xp : 0<C*O := Nat.mul_pos pos_cutoff (pos_odd A B)
  have cut (C O : ℕ) : (C*O)^230=(C^10*O^6)*(C^220*O^224) := by ring
  have join (C O E : ℕ) : C^10*(O*E)^6=(C^10*O^6)*E^6 := by ring
  have inequality : (C*O)^230<C^10*(O*E)^6 := calc
    _ = ∏ _t : Fin 10,(C*O)^23 := by simp [←pow_mul]
    _ < ∏ t : Fin 10,actualConductor t A B :=
      Finset.prod_lt_prod_of_nonempty₀ (fun _ _=>pow_pos xp _) (fun t _=>failure t) Finset.univ_nonempty
    _ = _ := conductor_pool primitive
  rw [cut,join] at inequality
  exact lt_of_mul_lt_mul_left' inequality

def LargeConductorHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ t : Fin 10,(cutoffProduct*oddProduct A B)^23<actualConductor t A B) →
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

theorem originalFiveHeight_iff_large_conductors (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ LargeConductorHeight := by
  constructor
  · exact fun all A B primitive off _ => all A B primitive off
  · intro remain A B primitive off
    by_cases failure : ∀ t : Fin 10,(cutoffProduct*oddProduct A B)^23<actualConductor t A B
    · exact remain A B primitive off failure
    push Not at failure
    obtain ⟨t,small⟩:=failure
    exact five_height_of_triple_conductor published primitive off t small

theorem five_height_of_pooled_conductors (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (small : totalResidual A B^6≤cutoffProduct^220*oddProduct A B^224) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  have someChart : ¬ ∀ t : Fin 10,(cutoffProduct*oddProduct A B)^23<actualConductor t A B :=
    fun h => (not_lt_of_ge small) (bad_conductors_force_total primitive h)
  push Not at someChart
  obtain ⟨t,ht⟩:=someChart
  exact five_height_of_triple_conductor published primitive off t ht

def LargeEvenSupportHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    cutoffProduct^220*oddProduct A B^224<totalResidual A B^6 →
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

theorem originalFiveHeight_iff_large_even_support (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ LargeEvenSupportHeight := by
  constructor
  · exact fun all A B primitive off _ => all A B primitive off
  · intro remain A B primitive off
    rcases le_or_gt (totalResidual A B^6) (cutoffProduct^220*oddProduct A B^224) with h|h
    · exact five_height_of_pooled_conductors published primitive off h
    · exact remain A B primitive off h

end Sun28.FiveMarkTriples
#print axioms Sun28.FiveMarkTriples.conductor_pool
#print axioms Sun28.FiveMarkTriples.bad_conductors_force_total
#print axioms Sun28.FiveMarkTriples.originalFiveHeight_iff_large_conductors
#print axioms Sun28.FiveMarkTriples.five_height_of_pooled_conductors
#print axioms Sun28.FiveMarkTriples.originalFiveHeight_iff_large_even_support
