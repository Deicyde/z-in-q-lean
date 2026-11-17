import ScalarOrders
import ScalarReadouts

/-! Explicit moduli for the finite-local preparation of the scalar tree, Sun §6. -/
namespace Sun28.ScalarPlaces
open ZInQ ZInQ.Size Sun28.ScalarHeight Sun28.Forward Sun28.Scalar Sun28.WitnessIndices
open Sun28.ContactFactors Sun28.FixedPreparation
noncomputable section

def supportPlaces (r : ℤ) : Finset ℕ := primes ∪ r.natAbs.primeFactors

theorem support_prime {r : ℤ} {p : ℕ} (hp : p∈supportPlaces r) : p.Prime := by
  have fixed : ∀ q∈primes,Nat.Prime q := by decide
  rcases Finset.mem_union.mp hp with h|h
  · exact fixed p h
  · exact Nat.prime_of_mem_primeFactors h

def kernelMod (r : ℤ) : ℕ :=
  (Nat.factorial 576) * ∏ p∈supportPlaces r, (p * orderAbove p)

def comparisonDepth (r : ℤ) (p : ℕ) : ℕ :=
  6 + padicValNat p (kernelMod r) + padicValInt p r

def stepMod (r : ℤ) (M : ℕ) : ℕ :=
  M * kernelMod r * ∏ p∈supportPlaces r, p^(comparisonDepth r p + 1 + 48 * padicValInt p r)

theorem kernel_positive (r : ℤ) : 0<kernelMod r :=
  Nat.mul_pos (Nat.factorial_pos _) (Finset.prod_pos fun p hp =>
    Nat.mul_pos (support_prime hp).pos (orderAbove_pos p))

theorem step_spec (r : ℤ) {M : ℕ} (hm : 0<M) :
    0<stepMod r M ∧ M∣stepMod r M ∧ kernelMod r∣stepMod r M := by
  have prod : 0<∏ p∈supportPlaces r, p^(comparisonDepth r p + 1 + 48*padicValInt p r) :=
    Finset.prod_pos fun p hp => pow_pos (support_prime hp).pos _
  exact ⟨Nat.mul_pos (Nat.mul_pos hm (kernel_positive r)) prod,
    (dvd_mul_right M _).trans (dvd_mul_right _ _),(dvd_mul_left _ _).trans (dvd_mul_right _ _)⟩

theorem local_steps {r : ℤ} {M p : ℕ} (hp : p∈supportPlaces r) {h c : ℤ} (cn : c≠0)
    (dc : (stepMod r M:ℤ)∣c) (exact_h : padicValInt p h = comparisonDepth r p) :
    orderAbove p∣kernelMod r ∧
    1+padicValInt p r≤(padicValInt p h:ℤ)-padicValNat p (kernelMod r) ∧
    1+48*(padicValInt p r:ℤ)≤(padicValInt p c:ℤ)-padicValInt p h := by
  have := Fact.mk (support_prime hp)
  have fac := Finset.dvd_prod_of_mem (fun q => q*orderAbove q) hp
  have ent : orderAbove p∣kernelMod r := (dvd_mul_left _ _).trans (fac.trans (dvd_mul_left _ _))
  let k:=comparisonDepth r p+1+48*padicValInt p r
  have pw : p^k∣stepMod r M := (Finset.dvd_prod_of_mem
    (fun q => q^(comparisonDepth r q+1+48*padicValInt q r)) hp).trans (dvd_mul_left _ _)
  have cv := (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr cn)).mp
    (pw.trans (Int.ofNat_dvd_left.mp dc))
  change k≤padicValInt p c at cv
  dsimp [k] at cv
  rw [exact_h]
  refine ⟨ent,?_,?_⟩
  · unfold comparisonDepth
    push_cast
    omega
  · omega

/-- For the early choices of h and c in §6, all three quadratic-field
quantities have the depths needed to divide by r, r and r^48. -/
theorem multiple_depths {r h c : ℤ} {p M : ℕ} (pp : p∈supportPlaces r)
    (mp : 0<M) (hn : h≠0) (cn : c≠0) (hc : (kernelMod r:ℤ)∣h) (cc : (stepMod r M:ℤ)∣c)
    (exact_h : padicValInt p h=comparisonDepth r p) :
    Deep p (1+padicValInt p r) (scalarRec h) ∧ Deep p (1+padicValInt p r) (scalarRec c) ∧
    Deep p (1+48*padicValInt p r) (scalarParam c/scalarParam h) := by
  have := Fact.mk (support_prime pp)
  obtain ⟨ord,high,gap⟩ := local_steps pp cn cc exact_h
  have ck := (Int.natCast_dvd_natCast.mpr (step_spec r mp).2.2).trans cc
  by_cases dy : p=2
  · subst p
    simp only [Deep,ite_true]
    obtain ⟨k,hk,a,b,z⟩ := dyadic_pair (kernel_positive r) hn cn hc ck
    dsimp only at a b
    refine ⟨(WithTop.coe_le_coe.mpr (by omega)).trans a,
      (WithTop.coe_le_coe.mpr (by omega)).trans b,?_⟩
    rw [z]
    exact WithTop.coe_le_coe.mpr (by omega)
  · simp only [Deep,ite_eq_right dy]
    have each (π : Zs) (hπ : Prime π) (above : π∣(p:Zs)) := odd_pair dy π hπ above
      (kernel_positive r) ord hn cn hc ck
    constructor
    · intro π hπ above
      obtain ⟨k,hk,a,_,_⟩ := each π hπ above
      dsimp only at *
      exact (WithTop.coe_le_coe.mpr (by omega)).trans a
    constructor
    · intro π hπ above
      obtain ⟨k,hk,_,b,_⟩ := each π hπ above
      dsimp only at *
      exact (WithTop.coe_le_coe.mpr (by omega)).trans b
    · intro π hπ above
      obtain ⟨_,_,_,_,z⟩ := each π hπ above
      rw [z]
      exact WithTop.coe_le_coe.mpr gap

theorem scalar_unit_of_indices {r : ℤ} (rn : r≠0) {p M : ℕ} (pp : p∈supportPlaces r)
    (mp : 0<M) {w : NinePoints} {a : Labels} {b c : ℤ} (data : Consequences w M b a)
    (step : a.n 1-1=c) (hc : (kernelMod r:ℤ)∣a.h) (cc : (stepMod r M:ℤ)∣c)
    (exact_h : padicValInt p a.h=comparisonDepth r p) :
    scalarTree (r:ℚ) (scalarEntries w M)≠0 ∧ padicValRat p (scalarTree (r:ℚ) (scalarEntries w M))=0 := by
  have := Fact.mk (support_prime pp)
  obtain ⟨ha,ca,ratio⟩ := multiple_depths pp mp data.h_nonzero (step ▸ data.scalar_nonzero) hc cc exact_h
  have ce : c • P=scalarPoint w M := step ▸ data.scalar_point
  apply scalar_unit_of_depths rn w M
  · simpa only [scalarRec,data.represented.h_point] using ha
  · simpa only [scalarRec,ce] using ca
  · simpa only [scalarParam,ce,data.represented.h_point] using ratio

end
end Sun28.ScalarPlaces
#print axioms Sun28.ScalarPlaces.support_prime
#print axioms Sun28.ScalarPlaces.kernel_positive
#print axioms Sun28.ScalarPlaces.step_spec
#print axioms Sun28.ScalarPlaces.local_steps
#print axioms Sun28.ScalarPlaces.multiple_depths
#print axioms Sun28.ScalarPlaces.scalar_unit_of_indices
