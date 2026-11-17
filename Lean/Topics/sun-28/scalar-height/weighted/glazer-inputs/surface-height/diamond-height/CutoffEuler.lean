import TameSign
import SelectedMenus28

namespace ZInQBlueprint.DiamondHeight
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
noncomputable section
set_option maxRecDepth 12000

/-- Removing primality from the Euler factors gives a telescoping majorant. -/
theorem interval_euler (n:ℕ) : eulerFactor (Finset.range n)≤n+1 := by
  have exact_prod (j:ℕ) : eulerFactor (Finset.range (j+1))=(j:ℝ)+1 := by
    induction j with
    | zero => norm_num [eulerFactor]
    | succ j h =>
      unfold eulerFactor at *
      rw [Finset.prod_range_succ,h]
      push_cast
      field_simp
  cases n with
  | zero => simp [eulerFactor]
  | succ n => rw [exact_prod];push_cast;linarith

private theorem member_of_dvd {p:ℕ} (prime:p.Prime) (S:Finset ℕ)
    (primes:∀q∈S,q.Prime) (h:p∣primeProduct S) : p∈S := by
  obtain ⟨q,hq,pq⟩:=(prime.prime.dvd_finsetProd_iff (fun q:ℕ=>q)).mp h
  rwa [(Nat.prime_dvd_prime_iff_eq prime (primes q hq)).mp pq]

theorem support_split (A B:ℤ) :
    (heightRadical A B).primeFactors ⊆ oldCutoff ∪ oddSupport A B := by
  intro p hp
  have pr:=Nat.prime_of_mem_primeFactors hp
  have dv:=Nat.dvd_of_mem_primeFactors hp
  change p∣cutoffProduct*oddProduct A B at dv
  rcases pr.dvd_mul.mp dv with h|h
  · exact Finset.mem_union_left _ (member_of_dvd pr oldCutoff (fun _ hq=>(Finset.mem_filter.mp hq).2) h)
  · exact Finset.mem_union_right _ (member_of_dvd pr (oddSupport A B) (fun _ hq=>(mem_oldContactPrimes.mp hq).1) h)

theorem old_disjoint (A B:ℤ) : Disjoint oldCutoff (oddSupport A B) := by
  apply Finset.disjoint_left.mpr
  intro p h1 h2
  exact (mem_oldContactPrimes.mp h2).2.1 h1

theorem paired_large {N:ℕ} (a b:ℤ)
    (support : N.primeFactors ⊆ (heightRadical a b).primeFactors) :
    (largeUnitOrders (oddSupport a b):ℝ)*eulerFactor N.primeFactors≤2^17*(oddProduct a b:ℝ) := by
  let O:=oddSupport a b
  have dis:=old_disjoint a b
  have small : eulerFactor oldCutoff≤(2:ℝ)^17 := by
    have sub : oldCutoff ⊆ Finset.range 76177 := Finset.filter_subset ..
    have b:= (euler_mono sub).trans (interval_euler 76177)
    exact b.trans (by norm_num)
  have paired : (largeUnitOrders O:ℝ)*eulerFactor O ≤ (oddProduct a b:ℝ) := by
    rw [largeUnitOrders,Nat.cast_prod,eulerFactor,← Finset.prod_mul_distrib]
    change _≤((∏p∈O,p:ℕ):ℝ)
    rw [Nat.cast_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => by positivity)
      (fun _ hp=>paired_prime (mem_oldContactPrimes.mp hp).1)
  have e:=euler_mono (support.trans (support_split a b))
  have join : eulerFactor (oldCutoff∪O)=eulerFactor oldCutoff*eulerFactor O := Finset.prod_union dis
  have lp : 0≤(largeUnitOrders O:ℝ) := by positivity
  have ep : 0≤eulerFactor O:=Finset.prod_nonneg (fun _ _ => by positivity)
  calc
    _ ≤ (largeUnitOrders O:ℝ)*eulerFactor (oldCutoff∪O) := mul_le_mul_of_nonneg_left e lp
    _ = eulerFactor oldCutoff*((largeUnitOrders O:ℝ)*eulerFactor O) := by rw [join];ring
    _ ≤ _ := mul_le_mul small paired (mul_nonneg lp ep) (by norm_num)

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.interval_euler
#print axioms ZInQBlueprint.DiamondHeight.support_split
#print axioms ZInQBlueprint.DiamondHeight.old_disjoint
#print axioms ZInQBlueprint.DiamondHeight.paired_large
