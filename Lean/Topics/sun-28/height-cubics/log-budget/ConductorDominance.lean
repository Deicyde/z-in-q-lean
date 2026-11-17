import PooledEndpoint

namespace Sun28.HeightCubics.Pooled.Logarithmic
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.HeightCubics.Refinement
open private core_eq from TameChart
noncomputable section
set_option maxRecDepth 2000

private theorem product_subset {S T:Finset ℕ} (sub:S⊆T) : primeProduct S∣primeProduct T :=
  Finset.prod_dvd_prod_of_subset S T (fun p=>p) sub

private theorem decompose (S T:Finset ℕ) :
    primeProduct S=primeProduct (S∩T)*primeProduct (S \ T) := by
  have split:(S∩T)∪(S \ T)=S:=by ext p;simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff];tauto
  have separate:Disjoint (S∩T) (S \ T):=Finset.disjoint_left.mpr
    (fun _ h m=>(Finset.mem_sdiff.mp m).2 (Finset.mem_inter.mp h).2)
  calc
    primeProduct S=primeProduct ((S∩T)∪(S \ T)):=congrArg _ split.symm
    _ = _:=Finset.prod_union separate

private theorem square_seen {A B:ℤ} (i:Fin 5) : squareSet i A B⊆support A B := by
  intro p h
  by_cases old:p∈oldCutoff
  · exact Finset.mem_union_left _ old
  obtain ⟨mem,odd⟩:=Finset.mem_filter.mp h
  have pr:=base_prime mem
  apply Finset.mem_union_right _ (mem_oldContactPrimes.mpr ⟨pr,old,i,?_,?_⟩)
  · rw [padicValInt,←Nat.factorization_def _ pr]
    unfold order at odd
    omega
  · rw [padicValInt,←Nat.factorization_def _ pr]
    exact Nat.odd_iff.mpr odd

private theorem measured {A B:ℤ} (cop:Int.gcd A B=1) (r:ThreeRows) :
    let S:=support A B
    let I:=baseSet r.center A B ∩ S
    let J:=squareSet r.a A B
    let K:=cubeSet r.b A B ∩ S
    35*primeProduct I*primeProduct J*primeProduct K ∣ heightRadical A B := by
  let S:=support A B
  let I:=baseSet r.center A B ∩ S
  let J:=squareSet r.a A B
  let K:=cubeSet r.b A B ∩ S
  let W:Finset ℕ:={5,7}
  have w:W⊆core:=by rw [core_eq]; decide
  have wi:Disjoint W I:=Finset.disjoint_left.mpr (fun _ a b=>(Finset.mem_sdiff.mp (Finset.mem_inter.mp b).1).2 (w a))
  have wj:Disjoint (W∪I) J:=by
    apply Finset.disjoint_left.mpr
    intro p x y
    have jy:=Finset.mem_sdiff.mp (Finset.mem_filter.mp y).1
    rcases Finset.mem_union.mp x with z|z
    · exact jy.2 (w z)
    · exact r.ia (unique_mark cop jy.2 (Finset.mem_sdiff.mp (Finset.mem_inter.mp z).1).1 jy.1)
  have wk:Disjoint ((W∪I)∪J) K:=by
    apply Finset.disjoint_left.mpr
    intro p x y
    have ky:=Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_inter.mp y).1).1
    rcases Finset.mem_union.mp x with z|z
    · rcases Finset.mem_union.mp z with a|a
      · exact ky.2 (w a)
      · exact r.ib (unique_mark cop ky.2 (Finset.mem_sdiff.mp (Finset.mem_inter.mp a).1).1 ky.1)
    · exact r.ab (unique_mark cop ky.2 (Finset.mem_sdiff.mp (Finset.mem_filter.mp z).1).1 ky.1)
  have bound:((W∪I)∪J)∪K⊆S:=Finset.union_subset (Finset.union_subset (Finset.union_subset
    (fun _ h=>Finset.mem_union_left _ (core_subset (w h))) Finset.inter_subset_right) (square_seen _)) Finset.inter_subset_right
  have prod:primeProduct (((W∪I)∪J)∪K)=35*primeProduct I*primeProduct J*primeProduct K:=by
    change (∏p∈((W∪I)∪J)∪K,p)=_
    rw [Finset.prod_union wk,Finset.prod_union wj,Finset.prod_union wi]
    have n:(∏p∈W,p)=35:=by decide
    rw [n]
    rfl
  change 35*primeProduct I*primeProduct J*primeProduct K∣heightRadical A B
  have raw:=product_subset bound
  rw [prod] at raw
  exact (product_support A B) ▸ raw

private theorem arithmetic {a b c h u T:ℕ}
    (abc:35*a*b*c∣T) :
    (62208*1225)*((a*h)*b^2*(c*u)^2) ∣ 62208*T^2*u^2*h := by
  obtain ⟨s,hs⟩:=abc
  rw [hs]
  refine ⟨a*s^2,?_⟩
  ring

/-- The new cap divides the previous cap on the very same ordered triple. -/
theorem cap_dvd_previous (r:ThreeRows) {A B:ℤ} (cop:Int.gcd A B=1) :
    cap r A B∣conductorCap r A B := by
  let S:=support A B
  let I:=baseSet r.center A B∩S
  let J:=squareSet r.a A B
  let K:=cubeSet r.b A B∩S
  have inside:core⊆S:=fun _ z=>Finset.mem_union_left _ (core_subset z)
  have a:baseSet r.center A B \ S=residualMark A B r.center:=by
    ext p
    change p∈((formPrimes r.center A B \ core) \ S) ↔ p∈formPrimes r.center A B \ S
    simp only [Finset.mem_sdiff]
    exact ⟨fun h=>⟨h.1.1,h.2⟩,fun h=>⟨⟨h.1,fun m=>h.2 (inside m)⟩,h.2⟩⟩
  have c:cubeSet r.b A B \ S=defective r.b A B:=by
    ext p
    change p∈((formPrimes r.b A B \ core).filter (fun q=>order r.b A B q%3≠0)) \ S ↔
      p∈(formPrimes r.b A B \ S).filter (fun q=>order r.b A B q%3≠0)
    simp only [Finset.mem_sdiff,Finset.mem_filter]
    exact ⟨fun h=>⟨⟨h.1.1.1,h.2⟩,h.1.2⟩,fun h=>⟨⟨⟨h.1.1,fun m=>h.1.2 (inside m)⟩,h.2⟩,h.1.2⟩⟩
  have ia:primeProduct (baseSet r.center A B)=primeProduct I*hidden r.center A B:=by
    exact (decompose _ S).trans (by rw [a];rfl)
  have kc:primeProduct (cubeSet r.b A B)=primeProduct K*noncubic r.b A B:=by
    exact (decompose _ S).trans (by rw [c];rfl)
  have weight:=measured cop r
  unfold cap conductorCap
  rw [ia,kc,show exceptional=62208*1225 by decide]
  rw [show 62208*1225*(primeProduct I*hidden r.center A B)*primeProduct (squareSet r.a A B)^2*
      (primeProduct K*noncubic r.b A B)^2=
    62208*1225*((primeProduct I*hidden r.center A B)*primeProduct J^2*(primeProduct K*noncubic r.b A B)^2) by ring]
  exact arithmetic weight

theorem chart_of_previous {A B:ℤ} (cop:Int.gcd A B=1) : Refinement.Covered A B → ChartTest A B := by
  rintro ⟨r,bound⟩
  have pos:0<conductorCap r A B:=by
    let d:=noncubic r.b A B
    let h:=hidden r.center A B
    have hv:0<h:=Nat.pos_of_ne_zero (prime_product_nonzero _ (fun p m=>Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp m).1))
    have dv:0<d:=Nat.pos_of_ne_zero (prime_product_nonzero _ (fun p m=>Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp (Finset.mem_filter.mp m).1).1))
    have t:0<heightRadical A B:=Nat.mul_pos pos_cutoff (pos_odd _ _)
    change 0<62208*heightRadical A B^2*d^2*h
    positivity
  exact ⟨r,(bound_mono (cap_pos r A B) (Nat.le_of_dvd pos (cap_dvd_previous r cop))).trans bound⟩

end
end Sun28.HeightCubics.Pooled.Logarithmic
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.cap_dvd_previous
#print axioms Sun28.HeightCubics.Pooled.Logarithmic.chart_of_previous
