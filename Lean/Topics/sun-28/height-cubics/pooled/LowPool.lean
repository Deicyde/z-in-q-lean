import ValuationPool

set_option maxHeartbeats 320000
namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres
noncomputable section

private theorem weighted_filter (S:Finset ℕ) (f:ℕ→Kind) (pr:∀ p∈S,p.Prime) :
    (primeProduct (S.filter (fun p=>f p=.oddNoncube)))^5*
      (primeProduct (S.filter (fun p=>f p=.oddCube)))^3*
      (primeProduct (S.filter (fun p=>f p=.evenNoncube)))^3*
      primeProduct (S.filter (fun p=>f p=.evenCube))≤(primeProduct S)^5 := by
  simp only [primeProduct,Finset.prod_filter,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_le_prod
  intro p hp
  have positive:= (pr p hp).pos
  cases f p <;> simp
  all_goals first | exact Nat.pow_le_pow_right positive (by decide) | exact Nat.le_self_pow (by decide) _

private theorem intersect_class (S K F:Finset ℕ) (f:ℕ→Kind) (k:Kind) :
    ((F \ K).filter (fun p=>f p=k))∩S=(((F \ K)∩S).filter (fun p=>f p=k)) := by
  ext p
  simp only [Finset.mem_filter,Finset.mem_inter]
  tauto

private theorem low_row (i:Fin 5) (A B:ℤ) :
    (primeProduct ((classSet core .oddNoncube i A B)∩oldCutoff))^5*
      (primeProduct ((classSet core .oddCube i A B)∩oldCutoff))^3*
      (primeProduct ((classSet core .evenNoncube i A B)∩oldCutoff))^3*
      primeProduct ((classSet core .evenCube i A B)∩oldCutoff) ≤
      (primeProduct (baseSet i A B∩oldCutoff))^5 := by
  simp only [classSet,intersect_class]
  exact weighted_filter _ (fun p=>kind (order i A B p)) (fun p m=>base_prime
    (i:=i) (A:=A) (B:=B) (Finset.mem_inter.mp m).1)


private theorem generic_disjoint_product {U : Fin 5 → Finset ℕ}
    (d : ∀ i j, i≠j → Disjoint (U i) (U j)) (S:Finset ℕ) :
    primeProduct ((Finset.univ.biUnion U)∩S) = ∏i, primeProduct (U i∩S) := by
  let V (i:Fin 5) := U i ∩ S
  have un : (Finset.univ.biUnion U)∩S=Finset.univ.biUnion V:=by
    ext p
    simp only [V,Finset.mem_inter,Finset.mem_biUnion,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨i,hi⟩,hc⟩;exact ⟨i,hi,hc⟩
    · rintro ⟨i,hi,hc⟩;exact ⟨⟨i,hi⟩,hc⟩
  rw [un]
  apply Finset.prod_biUnion
  intro i _ j _ ij
  exact (d i j ij).mono (Finset.inter_subset_left) (Finset.inter_subset_left)

private theorem near_row_product {A B:ℤ} (cop:Int.gcd A B=1) :
    primeProduct (nearSet A B)=∏ i:Fin 5,primeProduct (baseSet i A B∩oldCutoff) := by
  apply generic_disjoint_product (U:=fun i=>baseSet i A B) (S:=oldCutoff)
  intro i j ij
  apply Finset.disjoint_left.mpr
  intro p hi hj
  have a:=Finset.mem_sdiff.mp hi
  have b:=Finset.mem_sdiff.mp hj
  exact ij (unique_mark cop a.2 a.1 b.1)


private theorem near_compare {A B:ℤ} (cop:Int.gcd A B=1) :
    lowWeight A B≤(nearProduct A B)^5 := by
  let S (i:Fin 5):=primeProduct (baseSet i A B∩oldCutoff)
  have first:lowWeight A B≤∏i:Fin 5,(S i)^5 := Finset.prod_le_prod (fun i _=>low_row i A B)
  have second:(∏i:Fin 5,(S i)^5)=(∏i:Fin 5,S i)^5:=Finset.prod_pow _ _ _
  have third:(∏i:Fin 5,S i)^5=(nearProduct A B)^5:=congrArg (fun n:ℕ=>n^5) (near_row_product cop).symm
  exact first.trans_eq (second.trans third)

private theorem collect_bound {L N C : ℕ} (h:L≤N^5) (v:210*N≤C) : 210^5*L≤C^5 := by
  calc
    210^5*L ≤ 210^5*N^5 := Nat.mul_le_mul_left _ h
    _ = (210*N)^5 := (mul_pow 210 N 5).symm
    _ ≤ C^5 := Nat.pow_le_pow_left v 5

theorem low_weight_bound {A B:ℤ} (cop:Int.gcd A B=1) :
    210^5*lowWeight A B≤cutoffProduct^5 :=
  collect_bound (L:=lowWeight A B) (N:=nearProduct A B) (C:=cutoffProduct)
    (near_compare cop) (core_near_bound A B)

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.low_weight_bound
