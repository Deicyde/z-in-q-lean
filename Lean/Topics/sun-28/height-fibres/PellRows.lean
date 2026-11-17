import GenusTwoHeight
import LeastChart

/-! Three signed square roots on the five-mark slope line. -/
namespace Sun28.HeightFibres
open Sun28.Ordinary Sun28.FiveMarkUnits ZInQ.RouteK
noncomputable section

def heightRadical (A B : ℤ) := cutoffProduct * oddProduct A B
def kernel (i : Fin 5) (A B : ℤ) := sqfInt (oldForm i A B)

/-- Every row squareclass divides the same radical. This includes its sign only
in the squareclass itself. There is no cost for primes with positive even order. -/
theorem kernel_bound {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5) :
    (kernel i A B).natAbs ≤ heightRadical A B := by
  let z:=oldForm i A B
  let S:=z.natAbs.primeFactors.filter fun p=>Odd (z.natAbs.factorization p)
  have nz:z≠0:=off i
  have cast : (kernel i A B).natAbs=primeProduct S := by
    change (sqfInt z).natAbs=_
    rw [sqfInt,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero nz,Int.natAbs_natCast,one_mul]
    rfl
  have sub : S⊆oldCutoff ∪ oddSupport A B := by
    intro p h
    obtain ⟨mem,par⟩:=Finset.mem_filter.mp h
    have pr:=Nat.prime_of_mem_primeFactors mem
    by_cases bad:p∈oldCutoff
    · exact Finset.mem_union_left _ bad
    · have odd : Odd (padicValInt p (oldForm i A B)) := by
        simpa only [padicValInt,←Nat.factorization_def _ pr] using par
      have pos : 0<padicValInt p (oldForm i A B) := by obtain ⟨q,e⟩:=odd;omega
      exact Finset.mem_union_right _ (mem_oldContactPrimes.mpr ⟨pr,bad,i,pos,odd⟩)
  have dis : Disjoint oldCutoff (oddSupport A B) :=
    Finset.disjoint_left.mpr fun p hc ho=>(mem_oldContactPrimes.mp ho).2.1 hc
  have primes (p : ℕ) (h:p∈oldCutoff∪oddSupport A B) : p.Prime := by
    rcases Finset.mem_union.mp h with h|h
    · exact (Finset.mem_filter.mp h).2
    · exact (mem_oldContactPrimes.mp h).1
  rw [cast]
  simpa only [heightRadical,primeProduct,cutoffProduct,oddProduct,Finset.prod_union dis] using
    Sun28.MinimalConductors.support_mono sub primes

/-- On the slope chart with denominator B, taking signed squarefree parts
of three rows gives two simultaneous Pell equations over the integers. -/
theorem simultaneous_rows {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    ∃ g h k a b c : ℤ, g≠0 ∧ h≠0 ∧ k≠0 ∧ a≠0 ∧ b≠0 ∧ c≠0 ∧
      g.natAbs≤heightRadical A B ∧ h.natAbs≤heightRadical A B ∧
      k.natAbs≤heightRadical A B ∧ A=g*a^2 ∧
      g*a^2-h*b^2=B ∧ g*a^2-k*c^2=2401*B := by
  obtain ⟨sg,a,na,ea⟩:=sqfInt_spec (off 1)
  obtain ⟨sh,b,nb,eb⟩:=sqfInt_spec (off 2)
  obtain ⟨sk,c,nc,ec⟩:=sqfInt_spec (off 3)
  change A=kernel 1 A B*a^2 at ea
  change A-B=kernel 2 A B*b^2 at eb
  change A-2401*B=kernel 3 A B*c^2 at ec
  exact ⟨kernel 1 A B,kernel 2 A B,kernel 3 A B,a,b,c,sg.ne_zero,sh.ne_zero,sk.ne_zero,na,nb,nc,
    kernel_bound off 1,kernel_bound off 2,kernel_bound off 3,ea,by rw [←ea,←eb];ring,by rw [←ea,←ec];ring⟩

end
end Sun28.HeightFibres
#print axioms Sun28.HeightFibres.kernel_bound
#print axioms Sun28.HeightFibres.simultaneous_rows
