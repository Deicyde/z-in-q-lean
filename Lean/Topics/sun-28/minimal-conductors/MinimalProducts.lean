import MinimalSets

/-! Products of the ten smaller localization sets, with exact treatment of small primes. -/
set_option maxRecDepth 1300
namespace Sun28.MinimalConductors
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples
noncomputable section

def wideMark (A B : ℤ) (i : Fin 5) := formPrimes i A B \ core
def nearSet (A B : ℤ) := (Finset.univ.biUnion (wideMark A B)) ∩ oldCutoff
def nearProduct (A B : ℤ) := primeProduct (nearSet A B)
def leastConductor (t : Fin 10) (A B : ℤ) := primeProduct (leastSet t A B)

private theorem mark_product {A B : ℤ} (primitive : Int.gcd A B=1) (U : Finset (Fin 5)) :
    primeProduct (U.biUnion (wideMark A B)) = ∏ i∈U,primeProduct (wideMark A B i) := by
  apply Finset.prod_biUnion
  intro i _ j _ distinct
  apply Finset.disjoint_left.mpr
  intro p h h'
  obtain ⟨fi,away⟩:=Finset.mem_sdiff.mp h
  exact distinct (unique_mark primitive away fi (Finset.mem_sdiff.mp h').1)

private theorem mark_triple (t : Fin 10) (A B : ℤ) :
    (tripleIndex t).biUnion (wideMark A B)=
    triplePrimes (first t) (second t) (third t) A B \ core := by
  simp only [tripleIndex,triplePrimes,wideMark,Finset.biUnion_insert,Finset.singleton_biUnion,
    Finset.union_sdiff_distrib,Finset.union_assoc]

private theorem factor_chart (t : Fin 10) {A B : ℤ} (primitive : Int.gcd A B=1) :
    primeProduct (smallSet t A B)=210*(∏ i∈tripleIndex t,primeProduct (wideMark A B i)) := by
  rw [←core_product,← mark_product primitive,mark_triple]
  let C:=core
  let T:=triplePrimes (first t) (second t) (third t) A B
  have dis : Disjoint C (T\C) := Finset.disjoint_left.mpr (fun _ h hr => (Finset.mem_sdiff.mp hr).2 h)
  change (∏ p∈C∪T,p)=(∏ p∈C,p)*(∏ p∈T\C,p)
  rw [← Finset.prod_union dis,Finset.union_sdiff_self_eq_union]

private theorem outside_cutoff (A B : ℤ) :
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


private theorem partition (A B : ℤ) :
    Finset.univ.biUnion (wideMark A B)=nearSet A B ∪ (oddSupport A B ∪ totalResidualSupport A B) := by
  rw [←outside_cutoff]
  ext p
  simp only [wideMark,nearSet,freeMark,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_inter,
    Finset.mem_union,Finset.mem_sdiff]
  constructor
  · rintro ⟨i,mem,away⟩
    by_cases cut : p∈oldCutoff
    · exact Or.inl ⟨⟨i,mem,away⟩,cut⟩
    · exact Or.inr ⟨i,mem,cut⟩
  · intro z
    rcases z with ⟨h,_⟩ | ⟨i,h,away⟩
    · exact h
    · exact ⟨i,h,fun c=>away (core_subset c)⟩

theorem core_near_bound (A B : ℤ) : 210*nearProduct A B≤cutoffProduct := by
  have avoid : Disjoint core (nearSet A B) := by
    apply Finset.disjoint_left.mpr
    intro p h k
    obtain ⟨i,_,a⟩:=Finset.mem_biUnion.mp (Finset.mem_inter.mp k).1
    exact (Finset.mem_sdiff.mp a).2 h
  have sub : core ∪ nearSet A B ⊆ oldCutoff :=
    Finset.union_subset core_subset (fun _ k => (Finset.mem_inter.mp k).2)
  have e : primeProduct (core ∪ nearSet A B)=210*nearProduct A B := by
    rw [←core_product]; exact Finset.prod_union avoid
  rw [←e]
  exact support_mono sub fun _ h => (Finset.mem_filter.mp h).2

private theorem all_marks {A B : ℤ} (primitive : Int.gcd A B=1) :
    (∏ i:Fin 5,primeProduct (wideMark A B i))=nearProduct A B*(oddProduct A B*totalResidual A B) := by
  rw [←mark_product primitive,partition]
  have avoid : Disjoint (nearSet A B) (oddSupport A B ∪ totalResidualSupport A B) := by
    apply Finset.disjoint_left.mpr
    intro p h k
    have cut := (Finset.mem_inter.mp h).2
    rcases Finset.mem_union.mp k with odd|even
    · exact (Finset.mem_sdiff.mp odd).2 cut
    · obtain ⟨i,_,d⟩:=Finset.mem_biUnion.mp even
      exact (Finset.mem_sdiff.mp d).2 (Finset.mem_union_left _ cut)
  have dis : Disjoint (oddSupport A B) (totalResidualSupport A B) := by
    apply Finset.disjoint_left.mpr
    intro p h r
    obtain ⟨i,_,f⟩:=Finset.mem_biUnion.mp r
    exact (Finset.mem_sdiff.mp f).2 (Finset.mem_union_right _ h)
  change (∏ p∈nearSet A B ∪ (oddSupport A B ∪ totalResidualSupport A B),p)=_
  rw [Finset.prod_union avoid,Finset.prod_union dis]; rfl

theorem small_conductor_product {A B : ℤ} (primitive : Int.gcd A B=1) :
    (∏ t : Fin 10,primeProduct (smallSet t A B))=210^10*(nearProduct A B*(oddProduct A B*totalResidual A B))^6 := by
  simp_rw [factor_chart _ primitive]
  rw [Finset.prod_mul_distrib,incidence_count,all_marks primitive]
  simp

attribute [local irreducible] primeProduct cutoffProduct oddProduct totalResidual nearProduct smallSet leastSet

private theorem pooled_bound {c j s : ℕ} (h : 210*j≤c) :
    210^10*(j*s)^6 ≤ 210^4*c^6*s^6 := by
  calc
    _ = 210^4*(210*j)^6*s^6 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 6))

theorem least_product_bounds {A B : ℤ} (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) :
    (∏ t : Fin 10,leastConductor t A B)≤210^4*cutoffProduct^6*(oddProduct A B*totalResidual A B)^6 := by
  have m (t : Fin 10) : leastConductor t A B≤primeProduct (smallSet t A B) :=
    support_mono (least_subset t A B off) (fun _ h=>small_primes t A B h)
  have le : (∏ t : Fin 10,leastConductor t A B)≤∏ t : Fin 10,primeProduct (smallSet t A B) :=
    Finset.prod_le_prod (fun t _=>m t)
  rw [small_conductor_product primitive] at le
  exact le.trans (pooled_bound (c:=cutoffProduct) (j:=nearProduct A B) (s:=oddProduct A B*totalResidual A B)
    (core_near_bound A B))

end
end Sun28.MinimalConductors
#print axioms Sun28.MinimalConductors.core_near_bound
#print axioms Sun28.MinimalConductors.small_conductor_product
#print axioms Sun28.MinimalConductors.least_product_bounds
