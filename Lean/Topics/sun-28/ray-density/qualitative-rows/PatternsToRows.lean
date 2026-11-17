import SingleWindow
import ExistingOrders

namespace Sun28.QualitativeRows
open ZInQ Sun28.ContactFactors Sun28.ContactSieve Sun28.ScalarPlaces Sun28.FixedPreparation
open Sun28.RealPoleBounds Sun28.GaussianSelection Sun28.SelectedTrace Sun28.Exceptional Sun28.FiniteWitness
open ManuscriptV15.Arithmetic
noncomputable section


set_option maxHeartbeats 400000

/-- No prime threshold above the support of the radicand is needed. The actual
local order criteria already include any such primes with their correct orientation. -/
theorem admits_of_patterns (sieve : PrimePatterns) {X : ℤ} (w : Window X) : AdmitsRow w := by
  let A:=fixedScale w.n
  let r:=integerRadicand X
  let T:=supportPlaces r
  let κ:=kernelMod r
  let a:=comparisonDepth r
  have two : 2∈T := Finset.mem_union_left _ (by decide : 2∈primes)
  obtain ⟨u,v,values,π,o,_,vp,dv,large,ahead,exclude,oriented,lp,lm,ko,ts,ao⟩ :=
    select_with_orders sieve w.roots (requiredDivisor A) κ T a (divisor_positive A)
      (kernel_positive r) (fun _=>support_prime) two (fun _ _=>by dsimp [κ,a,comparisonDepth];omega)
      (by dsimp [a,comparisonDepth];omega) (slopeThreshold A w.C (1/2)) (selectionBound T)
  exact ⟨u,v,values,π,vp,dv,large,(separated_values values T ahead).1,exclude,oriented,
    balanced_of_orders π r oriented.ray16 o lp lm ko ts ao⟩

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.admits_of_patterns
