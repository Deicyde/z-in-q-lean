import FivePencils

/-! The five signed pencils have common radical equal to the specified original prime product. -/
namespace Sun28.HeightFibres.Sharp
open Sun28.Ordinary Sun28.FiveMarkUnits ZInQ.RouteK
open private mult catalogue from FivePencils
open private kernel_primes from SignedSupport

def support (A B : ℤ) := oldCutoff∪oddSupport A B

theorem support_primes {A B : ℤ} {p : ℕ} (hp:p∈support A B) : p.Prime := by
  rcases Finset.mem_union.mp hp with hp|hp
  · exact (Finset.mem_filter.mp hp).2
  · exact (mem_oldContactPrimes.mp hp).1

theorem product_support (A B : ℤ) : primeProduct (support A B)=heightRadical A B := by
  have dis : Disjoint oldCutoff (oddSupport A B) :=
    Finset.disjoint_left.mpr fun p hc ho=>(mem_oldContactPrimes.mp ho).2.1 hc
  simp only [support,primeProduct,cutoffProduct,oddProduct,heightRadical,Finset.prod_union dis]

private theorem sqf_support {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (r : Fin 5) :
    (kernel r A B).natAbs.primeFactors⊆support A B := by
  rw [kernel,kernel_primes (off r)]
  intro p hp
  obtain ⟨mem,odd⟩:=Finset.mem_filter.mp hp
  by_cases bad:p∈oldCutoff
  · exact Finset.mem_union_left _ bad
  · have pos : 0<padicValInt p (oldForm r A B) := by obtain ⟨q,e⟩:=odd;omega
    exact Finset.mem_union_right _ (mem_oldContactPrimes.mpr
      ⟨Nat.prime_of_mem_primeFactors mem,bad,r,pos,odd⟩)

private theorem mult_support (i : Fin 5) (j : Fin 3) : (mult i j).natAbs.primeFactors⊆oldCutoff := by
  have raw : ∀ (i : Fin 5) (j : Fin 3), (mult i j).natAbs∣210^12 := by decide
  intro p hp
  have ⟨pr,dv,_⟩ := Nat.mem_primeFactors.mp hp
  have dv2 := pr.dvd_of_dvd_pow (dv.trans (raw i j))
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have n:=Nat.le_of_dvd (by decide : 0<210) dv2;omega),pr⟩

theorem scaled_support {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5) (j : Fin 3) (r : Fin 5) :
    (mult i j*kernel r A B).natAbs.primeFactors⊆support A B := by
  have mr:mult i j≠0:=((catalogue i).1 j).1
  have kr : kernel r A B≠0 := (sqfInt_spec (off r)).1.ne_zero
  rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr mr) (Int.natAbs_ne_zero.mpr kr)]
  exact Finset.union_subset (fun _ h=>Finset.mem_union_left _ (mult_support i j h)) (sqf_support off r)

end Sun28.HeightFibres.Sharp
#print axioms Sun28.HeightFibres.Sharp.product_support
#print axioms Sun28.HeightFibres.Sharp.scaled_support
