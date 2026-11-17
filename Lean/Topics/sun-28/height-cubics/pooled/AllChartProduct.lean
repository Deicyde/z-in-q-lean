import ConductorPool

namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
noncomputable section

abbrev Triple := Fin 5 × Fin 5 × Fin 5
def ordered : Finset Triple := Finset.univ.filter fun v=>v.1≠v.2.1 ∧ v.1≠v.2.2 ∧ v.2.1≠v.2.2

def fromOrdered (v:Triple) (h:v∈ordered) : ThreeRows :=
  ⟨v.1,v.2.1,v.2.2,(Finset.mem_filter.mp h).2.1,(Finset.mem_filter.mp h).2.2.1,(Finset.mem_filter.mp h).2.2.2⟩

def tripleCap (v:Triple) (A B:ℤ) := exceptional*primeProduct (baseSet v.1 A B)*
  primeProduct (squareSet v.2.1 A B)^2*primeProduct (cubeSet v.2.2 A B)^2

theorem triple_cap (v:Triple) (h:v∈ordered) (A B:ℤ) : tripleCap v A B=cap (fromOrdered v h) A B := rfl

private theorem balance (g:Triple→Fin 5) (h:∀ i,(ordered.filter (fun v=>g v=i)).card=12) (f:Fin 5→ℕ) :
    (∏ v∈ordered,f (g v))=(∏ i:Fin 5,f i)^12:=by
  rw [←Finset.prod_fiberwise_of_maps_to' (t:=(Finset.univ:Finset (Fin 5))) (g:=g)
    (s:=ordered) (fun v _=>Finset.mem_univ (g v))]
  simp only [Finset.prod_const,h,Finset.prod_pow]

/-- Each of the five rows has twelve occurrences in each of the three roles. -/
theorem all_product (A B:ℤ) :
    (∏ v∈ordered,tripleCap v A B)=(exceptional^5*weight A B)^12 := by
  have c:∀ i:Fin 5,(ordered.filter (fun v=>v.1=i)).card=12:=by decide
  have g:∀ i:Fin 5,(ordered.filter (fun v=>v.2.1=i)).card=12:=by decide
  have h:∀ i:Fin 5,(ordered.filter (fun v=>v.2.2=i)).card=12:=by decide
  have card:ordered.card=60:=by decide
  let D (i:Fin 5):=primeProduct (baseSet i A B)
  let S (i:Fin 5):=primeProduct (squareSet i A B)^2
  let C (i:Fin 5):=primeProduct (cubeSet i A B)^2
  change (∏ v∈ordered,exceptional*D v.1*S v.2.1*C v.2.2)=(exceptional^5*∏ i:Fin 5,D i*S i*C i)^12
  simp only [Finset.prod_mul_distrib,Finset.prod_const,card,balance _ c D,balance _ g S,balance _ h C]
  ring

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.triple_cap
#print axioms Sun28.HeightCubics.Pooled.all_product
