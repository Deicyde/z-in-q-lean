import MixedSector

namespace Sun28.HeightCubics
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance Sun28.MinimalConductors
open Sun28.HeightFibres Sun28.HeightFibres.Sharp ZInQ.RouteK ZInQBlueprint.TwistDescent
open private kernel_primes from SignedSupport
noncomputable section

def defective (i:Fin 5) (A B:ℤ) :=
  (residualMark A B i).filter fun p=>(oldForm i A B).natAbs.factorization p%3≠0
def hidden (i:Fin 5) (A B:ℤ) := primeProduct (residualMark A B i)
def noncubic (i:Fin 5) (A B:ℤ) := primeProduct (defective i A B)

private theorem away_minor {p:ℕ} (pr:p.Prime) {A B:ℤ} (out:p∉support A B)
    {j k i:Fin 5} (diff:j≠k) (off:oldForm i A B≠0) :
    (det j k*oldForm i A B).natAbs.factorization p=(oldForm i A B).natAbs.factorization p := by
  have nd:¬p∣(det j k).natAbs:=fun d=>out (Finset.mem_union_left _ (determinant_support _ _
    (Nat.mem_primeFactors.mpr ⟨pr,d,Int.natAbs_ne_zero.mpr (det_ne diff)⟩)))
  rw [Int.natAbs_mul,Nat.factorization_mul (Int.natAbs_ne_zero.mpr (det_ne diff)) (Int.natAbs_ne_zero.mpr off),
    Finsupp.add_apply,Nat.factorization_eq_zero_of_not_dvd nd,zero_add]

private theorem away_support {p:ℕ} {A B:ℤ} (out:p∉support A B) {i j k:Fin 5} (ij:i≠j)
    (off:oldForm k A B≠0) (mem:p∈(det i j*oldForm k A B).natAbs.primeFactors) :
    p∈residualMark A B k := by
  rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (det_ne ij)) (Int.natAbs_ne_zero.mpr off)] at mem
  rcases Finset.mem_union.mp mem with a|b
  · exact False.elim (out (Finset.mem_union_left _ (determinant_support _ _ a)))
  · exact Finset.mem_sdiff.mpr ⟨b,out⟩

theorem chart_primes (r:ThreeRows) {A B:ℤ} (off:∀ i,oldForm i A B≠0) :
    mixedPlaces (left r A B) (right r A B) (baseRow r A B) ⊆
      support A B ∪ (defective r.b A B ∪ residualMark A B r.center) := by
  intro p mem
  by_cases seen:p∈support A B
  · exact Finset.mem_union_left _ seen
  apply Finset.mem_union_right
  have pr:=mixed_prime mem
  rcases Finset.mem_union.mp mem with a|rest
  · have nz:det r.center r.b*oldForm r.a A B≠0:=mul_ne_zero (det_ne r.ib) (off _)
    change p∈(sqfInt (det r.center r.b*oldForm r.a A B)).natAbs.primeFactors at a
    rw [kernel_primes nz] at a
    have odd:=(Finset.mem_filter.mp a).2
    rw [padicValInt,←Nat.factorization_def _ pr,away_minor pr seen r.ib (off _),
      Nat.factorization_def _ pr] at odd
    have oddv:Odd (padicValInt p (oldForm r.a A B)):=odd
    have pos:0<padicValInt p (oldForm r.a A B):=by obtain ⟨n,hn⟩:=oddv;omega
    have ncut:p∉oldCutoff:=fun c=>seen (Finset.mem_union_left _ c)
    exact False.elim (seen (Finset.mem_union_right _ (mem_oldContactPrimes.mpr ⟨pr,ncut,r.a,pos,oddv⟩)))
  · rcases Finset.mem_union.mp rest with u|v
    · obtain ⟨fac,ord⟩:=Finset.mem_filter.mp u
      have row:=(away_support seen r.ia.symm (off r.b) fac)
      change (det r.a r.center*oldForm r.b A B).natAbs.factorization p%3≠0 at ord
      rw [away_minor pr seen r.ia.symm (off _)] at ord
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨row,ord⟩)
    · exact Finset.mem_union_right _ (away_support seen r.ab (off r.center) v)

theorem chart_cost {A B:ℤ} (r:ThreeRows) (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0) :
    mixedChart r A B≤heightRadical A B*(noncubic r.b A B*hidden r.center A B) := by
  let d:=defective r.b A B
  let h:=residualMark A B r.center
  let S:=support A B
  have dm {p} (m:p∈d):p∈residualMark A B r.b:=(Finset.mem_filter.mp m).1
  have pr (p) (m:p∈S∪(d∪h)):p.Prime:=by
    rcases Finset.mem_union.mp m with old|other
    · exact support_primes old
    rcases Finset.mem_union.mp other with right|center
    · exact Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp (dm right)).1
    · exact Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp center).1
  have dis:Disjoint d h:=Finset.disjoint_left.mpr (by
    intro p inD inH
    have b:=Finset.mem_sdiff.mp (dm inD)
    exact r.ib (unique_form cop (fun z=>b.2 (Finset.mem_union_left _ z)) (Finset.mem_sdiff.mp inH).1 b.1))
  have sep:Disjoint S (d∪h):=Finset.disjoint_left.mpr (by
    intro p seen rest
    rcases Finset.mem_union.mp rest with x|y
    · exact (Finset.mem_sdiff.mp (dm x)).2 seen
    · exact (Finset.mem_sdiff.mp y).2 seen)
  have inc:=support_mono (chart_primes r off) pr
  change mixedChart r A B≤primeProduct (S∪(d∪h)) at inc
  rw [show primeProduct (S∪(d∪h))=primeProduct S*(primeProduct d*primeProduct h) by
    unfold primeProduct;rw [Finset.prod_union sep,Finset.prod_union dis]] at inc
  exact inc.trans_eq (by rw [←product_support];rfl)

def cycle (i:Fin 5):ThreeRows where
  center:=i
  a:=i+2
  b:=i+1
  ia:=(by decide : ∀ j:Fin 5,j≠j+2) i
  ib:=(by decide : ∀ j:Fin 5,j≠j+1) i
  ab:=(by decide : ∀ j:Fin 5,j+2≠j+1) i

/-- One more product in the pair costs a full hidden prime only at the base row.
In the following row its order modulo 3 decides whether it occurs. -/
theorem pool_covered {A B:ℤ} (cop:Int.gcd A B=1) (off:∀ i,oldForm i A B≠0)
    (budget:(∏ i:Fin 5,hidden i A B*noncubic i A B)≤heightRadical A B^50) : MixedCovered A B := by
  let T:=heightRadical A B
  have pos:0<T:=Nat.mul_pos pos_cutoff (pos_odd _ _)
  have inclusion: (∏ i:Fin 5,mixedChart (cycle i) A B)≤
      ∏ i:Fin 5,T*(noncubic (i+1) A B*hidden i A B):=
    Finset.prod_le_prod (fun i _=>chart_cost (cycle i) cop off)
  have count: (∏ i:Fin 5,T*(noncubic (i+1) A B*hidden i A B))=
      T^5*(∏ i:Fin 5,hidden i A B*noncubic i A B) :=by
    let h (j:Fin 5):=hidden j A B
    let u (j:Fin 5):=noncubic j A B
    change (∏ i:Fin 5,T*(u (i+1)*h i))=T^5*∏ i:Fin 5,h i*u i
    simp only [Fin.prod_univ_succ]
    change T*(u 1*h 0)*(T*(u 2*h 1)*(T*(u 3*h 2)*(T*(u 4*h 3)*(T*(u 0*h 4)*1))))=
      T^5*(h 0*u 0*(h 1*u 1*(h 2*u 2*(h 3*u 3*(h 4*u 4*1)))))
    ring
  have allbound:(∏ i:Fin 5,mixedChart (cycle i) A B)≤T^55:=by
    rw [count] at inclusion
    exact inclusion.trans ((Nat.mul_le_mul_left (T^5) budget).trans_eq (by rw [←pow_add]))
  by_contra bad
  have large (i:Fin 5):T^11< mixedChart (cycle i) A B:=
    lt_of_not_ge (fun le=>bad (mixed_of_conductor _ le))
  have lo:(∏ _i:Fin 5,T^11)<∏ i:Fin 5,mixedChart (cycle i) A B:=
    Finset.prod_lt_prod_of_nonempty₀ (fun _ _=>pow_pos pos _) (fun i _=>large i) Finset.univ_nonempty
  have power:(∏ _i:Fin 5,T^11)=T^55:=by simp [←pow_mul]
  omega

theorem five_height_of_pool (mordell:SupportedMordell74) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (budget:(∏ i:Fin 5,hidden i A B*noncubic i A B)≤heightRadical A B^50) :
    target A B := five_height_of_mixed mordell cop off (pool_covered cop off budget)
end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.chart_primes
#print axioms Sun28.HeightCubics.chart_cost
#print axioms Sun28.HeightCubics.pool_covered
#print axioms Sun28.HeightCubics.five_height_of_pool
