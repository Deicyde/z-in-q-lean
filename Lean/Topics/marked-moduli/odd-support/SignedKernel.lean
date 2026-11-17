import ContactParity

/-! A signed squarefree integer whose prime support is controlled by the
public odd-contact product at every prime. -/
open ZInQ ZInQ.Mult
namespace ZInQBlueprint.OddSupport
noncomputable section

def binary (a b : ℤ) : ℤ :=
  a*(a+15*b)*(a+20*b)*(a+24*b)*(a+30*b)*(a+60*b)

def integerValue (u : ℚ) : ℤ := binary u.num (u.den:ℤ)

theorem binary_identity (u : ℚ) : (integerValue u:ℚ) = contactPoly u * (u.den:ℚ)^6 := by
  have repl : (u.num:ℚ)=u*(u.den:ℚ) := (div_eq_iff (by exact_mod_cast u.den_nz)).mp u.num_div_den
  simp only [integerValue,binary,Int.cast_mul,Int.cast_add,Int.cast_ofNat,Int.cast_natCast,
    contactPoly,repl]
  ring

/-- The signed squarefree part is taken before choosing a place. -/
def IsKernel (u : ℚ) (d e : ℤ) : Prop := Squarefree d ∧ d*e^2=integerValue u

theorem exists_kernel (u : ℚ) : ∃ d e : ℤ, IsKernel u d e := by
  obtain ⟨e,d,h,hd⟩ := exists_sq_mul_squarefree (integerValue u)
  exact ⟨d,e,hd,(mul_comm d _).trans h⟩

theorem Kernel_nonzero {u : ℚ} (hu : u ∉ contactSet) {d e : ℤ} (h : IsKernel u d e) :
    d ≠ 0 ∧ e ≠ 0 := by
  have den : (u.den:ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have zq : (integerValue u:ℚ)≠0 := by rw [binary_identity]; exact mul_ne_zero (contactPoly_ne_zero hu) (pow_ne_zero _ den)
  have zi : integerValue u≠0 := by exact_mod_cast zq
  rw [←h.2] at zi
  exact ⟨(mul_ne_zero_iff.mp zi).1,fun he => zi (by rw [he]; ring)⟩

/-- Squarefree integers have valuation zero or one. Its odd parity detects
the prime divisors of the absolute value, including for negative integers. -/
theorem squarefree_odd_order {d : ℤ} (h : Squarefree d) {p : ℕ} [hp : Fact p.Prime] :
    p ∣ d.natAbs ↔ Odd (padicValRat p (d:ℚ)) := by
  rw [padicValRat.of_int,padicValInt,←Nat.factorization_def _ hp.out]
  have sq := Int.squarefree_natAbs.mpr h
  constructor
  · intro hd
    rw [Nat.factorization_eq_one_of_squarefree sq hp.out hd]
    exact ⟨0,by norm_num⟩
  · intro odd
    by_contra hd
    rw [Nat.factorization_eq_zero_of_not_dvd hd] at odd
    exact (Int.not_even_iff_odd.mpr odd) (by norm_num)

/-- A prime divides the signed kernel exactly when the rational sextic has odd
order there. The sixth power of the denominator has even order. -/
theorem kernel_order {u : ℚ} (hu : u ∉ contactSet) {d e : ℤ} (h : IsKernel u d e)
    {p : ℕ} [hp : Fact p.Prime] :
    p ∣ d.natAbs ↔ Odd (padicValRat p (contactPoly u)) := by
  obtain ⟨hd,he⟩ := Kernel_nonzero hu h
  have hdq : (d:ℚ) ≠ 0 := by exact_mod_cast hd
  have heq : (e:ℚ) ≠ 0 := by exact_mod_cast he
  have den : (u.den:ℚ) ≠ 0 := by exact_mod_cast u.den_nz
  have identity : (d:ℚ)*(e:ℚ)^2=contactPoly u*(u.den:ℚ)^6 := by
    rw [←binary_identity]; exact_mod_cast h.2
  have val := congrArg (padicValRat p) identity
  rw [padicValRat.mul hdq (pow_ne_zero _ heq),padicValRat.mul (contactPoly_ne_zero hu) (pow_ne_zero _ den),
    padicValRat.pow,padicValRat.pow] at val
  rw [squarefree_odd_order h.1]
  constructor
  · rintro ⟨k,hk⟩
    exact ⟨k+padicValRat p (e:ℚ)-3*padicValRat p (u.den:ℚ),by push_cast at val; omega⟩
  · rintro ⟨k,hk⟩
    exact ⟨k-padicValRat p (e:ℚ)+3*padicValRat p (u.den:ℚ),by push_cast at val; omega⟩

theorem kernel_prime_inclusion {u : ℚ} (hu : u ∉ contactSet) {d e : ℤ} (h : IsKernel u d e)
    (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) (hd : p ∣ d.natAbs) :
    p ∣ contactSupport S u := by
  have : Fact p.Prime := ⟨hp⟩
  exact (prime_dvd_contactSupport_iff' hu hp).mpr ⟨hpS, odd_poly_contact hu ((kernel_order hu h).mp hd)⟩

theorem kernel_prime_iff {u : ℚ} (hu : u ∉ contactSet) {d e : ℤ} (h : IsKernel u d e)
    (S : Finset ℕ) {p : ℕ} (hp : p.Prime) (hpS : p ∉ S) (h5 : 5<p) :
    p ∣ d.natAbs ↔ p ∣ contactSupport S u := by
  have : Fact p.Prime := ⟨hp⟩
  rw [kernel_order hu h,odd_poly_iff hu h5,prime_dvd_contactSupport_iff' hu hp]
  simp [hpS]

/-- This divisibility gives a literal size bound even when S omits 2, 3 or 5. -/
theorem kernel_dvd {u : ℚ} (hu : u ∉ contactSet) {d e : ℤ} (h : IsKernel u d e)
    (S : Finset ℕ) : d.natAbs ∣ (∏ p ∈ S, p) * contactSupport S u := by
  have hs := Int.squarefree_natAbs.mpr h.1
  let M : ℕ := (∏ p ∈ S,p)*contactSupport S u
  change d.natAbs ∣ M
  by_cases hz : M=0
  · rw [hz]; exact dvd_zero _
  refine (Nat.prod_primeFactors_of_squarefree hs) ▸ (Nat.prod_primeFactors_dvd_iff hz).mpr ?_
  intro p hp
  obtain ⟨prime,hd,_⟩ := Nat.mem_primeFactors.mp hp
  apply Nat.mem_primeFactors.mpr
  refine ⟨prime,?_,hz⟩
  by_cases hin : p ∈ S
  · exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem _ hin) _
  · exact dvd_mul_of_dvd_right (kernel_prime_inclusion hu h S prime hin hd) _

#print axioms binary_identity
#print axioms exists_kernel
#print axioms squarefree_odd_order
#print axioms kernel_order
#print axioms kernel_prime_inclusion
#print axioms kernel_prime_iff
#print axioms kernel_dvd
end
end ZInQBlueprint.OddSupport
