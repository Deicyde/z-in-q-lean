import CrossRatioForms

/-! The ten triples and their incidence with the even-contact prime divisors. -/
namespace Sun28.FiveMarkTriples
open Sun28.Ordinary Sun28.FiveMarkUnits

def first : Fin 10 → Fin 5 := ![0,0,0,0,0,0,1,1,1,2]
def second : Fin 10 → Fin 5 := ![1,1,1,2,2,3,2,2,3,3]
def third : Fin 10 → Fin 5 := ![2,3,4,3,4,4,3,4,4,4]
def tripleIndex (t : Fin 10) : Finset (Fin 5) := {first t,second t,third t}

theorem increasing (t : Fin 10) : first t<second t ∧ second t<third t := by
  have h : ∀ t : Fin 10, first t<second t ∧ second t<third t := by decide
  exact h t

theorem catalogue : ∀ i j k : Fin 5, i<j → j<k →
    ∃! t : Fin 10, first t=i ∧ second t=j ∧ third t=k := by
  unfold ExistsUnique
  decide

theorem six_occurrences (i : Fin 5) :
    ((Finset.univ : Finset (Fin 10)).filter (fun t => i∈tripleIndex t)).card=6 := by
  have h : ∀ i : Fin 5, ((Finset.univ : Finset (Fin 10)).filter (fun t => i∈tripleIndex t)).card=6 := by decide
  exact h i

def residualMark (A B : ℤ) (i : Fin 5) : Finset ℕ :=
  formPrimes i A B \ (oldCutoff ∪ oddSupport A B)

def residualTriple (t : Fin 10) (A B : ℤ) : ℕ :=
  primeProduct ((tripleIndex t).biUnion (residualMark A B))

def totalResidualSupport (A B : ℤ) : Finset ℕ := Finset.univ.biUnion (residualMark A B)
def totalResidual (A B : ℤ) : ℕ := primeProduct (totalResidualSupport A B)

theorem residual_union (t : Fin 10) (A B : ℤ) :
    (tripleIndex t).biUnion (residualMark A B)=
      triplePrimes (first t) (second t) (third t) A B \ (oldCutoff ∪ oddSupport A B) := by
  simp only [tripleIndex,triplePrimes,residualMark,Finset.biUnion_insert,
    Finset.singleton_biUnion,Finset.union_sdiff_distrib,Finset.union_assoc]

theorem triple_conductor (t : Fin 10) (A B : ℤ) :
    primeProduct (oldCutoff ∪ triplePrimes (first t) (second t) (third t) A B) ≤
    cutoffProduct*oddProduct A B*residualTriple t A B := by
  let C:=oldCutoff
  let O:=oddSupport A B
  let T:=triplePrimes (first t) (second t) (third t) A B
  let R:=T \ (C∪O)
  have sub : C∪T⊆(C∪O)∪R := by
    intro p hp
    rcases Finset.mem_union.mp hp with h|h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    by_cases inCO : p∈C∪O
    · exact Finset.mem_union_left _ inCO
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h,inCO⟩)
  have dis : Disjoint C O := Finset.disjoint_left.mpr (fun _ hc ho => (mem_oldContactPrimes.mp ho).2.1 hc)
  have dr : Disjoint (C∪O) R := Finset.disjoint_left.mpr (fun _ hc hr => (Finset.mem_sdiff.mp hr).2 hc)
  have ones (p : ℕ) (h : p∈(C∪O)∪R) : 1≤p := by
    rcases Finset.mem_union.mp h with a|r
    · rcases Finset.mem_union.mp a with c|o
      · exact (Finset.mem_filter.mp c).2.one_lt.le
      · exact (mem_oldContactPrimes.mp o).1.one_lt.le
    · exact (support_prime (Finset.mem_sdiff.mp r).1).one_lt.le
  have h := Finset.prod_le_prod_of_subset_of_one_le (f:=id) sub (fun p hp _ => ones p hp)
  unfold residualTriple
  rw [residual_union]
  change (∏ p∈C∪T,p)≤(∏ p∈C,p)*(∏ p∈O,p)*(∏ p∈R,p)
  simpa only [Finset.prod_union dr,Finset.prod_union dis,id_eq] using h

theorem residual_even_unique {A B : ℤ} (primitive : Int.gcd A B=1)
    {p : ℕ} (member : p∈totalResidualSupport A B) :
    p.Prime ∧ 76176<p ∧ (∃! i : Fin 5,p∈formPrimes i A B) ∧
    ∀ i : Fin 5, Even (padicValInt p (oldForm i A B)) := by
  obtain ⟨i,_,hin⟩:=Finset.mem_biUnion.mp member
  obtain ⟨fac,outside⟩:=Finset.mem_sdiff.mp hin
  have prime := Nat.prime_of_mem_primeFactors fac
  have away : p∉oldCutoff := fun h => outside (Finset.mem_union_left _ h)
  have large : 76176<p := by
    by_contra! le
    exact away (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prime⟩)
  refine ⟨prime,large,⟨i,fac,fun j h => unique_form primitive away h fac⟩,?_⟩
  intro j
  rcases Nat.even_or_odd (padicValInt p (oldForm j A B)) with even|odd
  · exact even
  have pos : 0<padicValInt p (oldForm j A B) := by obtain ⟨k,hk⟩ := odd; omega
  exact (outside (Finset.mem_union_right _ (mem_oldContactPrimes.mpr ⟨prime,away,j,pos,odd⟩))).elim

private theorem mark_product {A B : ℤ} (primitive : Int.gcd A B=1) (U : Finset (Fin 5)) :
    primeProduct (U.biUnion (residualMark A B)) = ∏ i∈U,primeProduct (residualMark A B i) := by
  apply Finset.prod_biUnion
  intro i _ j _ distinct
  apply Finset.disjoint_left.mpr
  intro p h h'
  obtain ⟨fi,away⟩:=Finset.mem_sdiff.mp h
  exact distinct (unique_form primitive (fun c => away (Finset.mem_union_left _ c)) fi (Finset.mem_sdiff.mp h').1)

private theorem incidence_product (f : Fin 5→ℕ) :
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

theorem residual_pool {A B : ℤ} (primitive : Int.gcd A B=1) :
    (∏ t : Fin 10, residualTriple t A B)=totalResidual A B^6 := by
  simp only [residualTriple,totalResidual,totalResidualSupport,mark_product primitive]
  exact incidence_product _

theorem failures_force_total {A B : ℤ} (primitive : Int.gcd A B=1)
    (fail : ∀ t : Fin 10,(cutoffProduct*oddProduct A B)^22<residualTriple t A B) :
    (cutoffProduct*oddProduct A B)^220<totalResidual A B^6 := by
  let X:=cutoffProduct*oddProduct A B
  have xpos : 0<X := Nat.mul_pos pos_cutoff (pos_odd A B)
  calc
    X^220 = ∏ _t : Fin 10,X^22 := by simp [←pow_mul]
    _ < ∏ t : Fin 10,residualTriple t A B :=
      Finset.prod_lt_prod_of_nonempty₀ (fun _ _ => pow_pos xpos _) (fun t _ => fail t) Finset.univ_nonempty
    _ = _ := residual_pool primitive

end Sun28.FiveMarkTriples
#print axioms Sun28.FiveMarkTriples.catalogue
#print axioms Sun28.FiveMarkTriples.six_occurrences
#print axioms Sun28.FiveMarkTriples.triple_conductor
#print axioms Sun28.FiveMarkTriples.residual_even_unique
#print axioms Sun28.FiveMarkTriples.residual_pool
#print axioms Sun28.FiveMarkTriples.failures_force_total
