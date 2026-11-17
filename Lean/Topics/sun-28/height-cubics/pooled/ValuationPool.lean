import ConductorPool

namespace Sun28.HeightCubics.Pooled
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Sun28.HeightBalance
open Sun28.MinimalConductors Sun28.HeightFibres
noncomputable section

/-- The four positive-order congruence classes. The factorization support
ensures that a valuation divisible by six in a row is strictly positive. -/
inductive Kind where | oddNoncube | oddCube | evenNoncube | evenCube
  deriving DecidableEq

def kind (n:ℕ) : Kind :=
  if n%2=1 then (if n%3=0 then .oddCube else .oddNoncube)
  else (if n%3=0 then .evenCube else .evenNoncube)

def classSet (excluded:Finset ℕ) (k:Kind) (i:Fin 5) (A B:ℤ) :=
  ((formPrimes i A B) \ excluded).filter fun p=>kind (order i A B p)=k

def classProduct (excluded:Finset ℕ) (k:Kind) (A B:ℤ) :=
  ∏ i:Fin 5,primeProduct (classSet excluded k i A B)

theorem class_positive (S:Finset ℕ) (k:Kind) (A B:ℤ) : 0<classProduct S k A B := by
  apply Finset.prod_pos
  intro i _
  exact Nat.pos_of_ne_zero (prime_product_nonzero _ (fun p m=>
    Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp (Finset.mem_filter.mp m).1).1))

private theorem row_classes (i:Fin 5) (A B:ℤ) :
    rowWeight i A B=(primeProduct (classSet core .oddNoncube i A B))^5*
      (primeProduct (classSet core .oddCube i A B))^3*(primeProduct (classSet core .evenNoncube i A B))^3*
      primeProduct (classSet core .evenCube i A B) := by
  unfold rowWeight squareSet cubeSet primeProduct classSet
  simp only [baseSet,Finset.prod_filter,←Finset.prod_pow,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _
  by_cases h:order i A B p%2=1 <;> by_cases e:order i A B p%3=0 <;>
    simp [kind,h,e] <;> ring

theorem weight_classes (A B:ℤ) :
    weight A B=(classProduct core .oddNoncube A B)^5*(classProduct core .oddCube A B)^3*
      (classProduct core .evenNoncube A B)^3*classProduct core .evenCube A B := by
  unfold weight classProduct
  simp only [row_classes,Finset.prod_mul_distrib,Finset.prod_pow]

/-- The cutoff may be enlarged in this estimate provided each omitted row
prime is charged at most five times. -/
private theorem split_class {i:Fin 5} {A B:ℤ} (k:Kind) :
    primeProduct (classSet core k i A B)=
      primeProduct ((classSet core k i A B)∩oldCutoff)*primeProduct (classSet oldCutoff k i A B) := by
  let S:=classSet core k i A B
  have merge:S=(S∩oldCutoff)∪classSet oldCutoff k i A B:=by
    ext p
    simp only [S,classSet,Finset.mem_union,Finset.mem_inter,Finset.mem_filter,Finset.mem_sdiff]
    by_cases h:p∈oldCutoff <;> simp [h,show p∉oldCutoff → p∉core from fun z m=>z (core_subset m)]
  have dis:Disjoint (S∩oldCutoff) (classSet oldCutoff k i A B):=Finset.disjoint_left.mpr
    (fun _ m n=>(Finset.mem_sdiff.mp (Finset.mem_filter.mp n).1).2 (Finset.mem_inter.mp m).2)
  calc
    primeProduct S=primeProduct ((S∩oldCutoff)∪classSet oldCutoff k i A B):=congrArg primeProduct merge
    _ =_:=Finset.prod_union dis

/-- For the final inequality the contribution of small primes is compressed
directly over the disjoint supports of the five rows. -/
def lowWeight (A B:ℤ) :=
  ∏ i:Fin 5, (primeProduct ((classSet core .oddNoncube i A B)∩oldCutoff))^5*
    (primeProduct ((classSet core .oddCube i A B)∩oldCutoff))^3*
    (primeProduct ((classSet core .evenNoncube i A B)∩oldCutoff))^3*
    primeProduct ((classSet core .evenCube i A B)∩oldCutoff)

theorem split_weight (A B:ℤ) : weight A B=lowWeight A B*
    ((classProduct oldCutoff .oddNoncube A B)^5*(classProduct oldCutoff .oddCube A B)^3*
      (classProduct oldCutoff .evenNoncube A B)^3*classProduct oldCutoff .evenCube A B) := by
  unfold weight lowWeight classProduct
  simp only [row_classes,split_class,mul_pow,Finset.prod_mul_distrib,Finset.prod_pow]
  ring

end
end Sun28.HeightCubics.Pooled
#print axioms Sun28.HeightCubics.Pooled.class_positive
#print axioms Sun28.HeightCubics.Pooled.weight_classes
#print axioms Sun28.HeightCubics.Pooled.split_weight
