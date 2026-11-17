import ScaledConductor

/-! Localize at the prime divisors of the actual two rational units. -/
namespace Sun28.MinimalConductors
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples
noncomputable section

def core : Finset ℕ := (210:ℕ).primeFactors
def smallSet (t : Fin 10) (A B : ℤ) :=
  core ∪ triplePrimes (first t) (second t) (third t) A B
def rationalSupport (x : ℚ) := x.num.natAbs.primeFactors ∪ x.den.primeFactors
def leastSet (t : Fin 10) (A B : ℤ) :=
  let x := crossRatio (first t) (second t) (third t) A B
  rationalSupport x ∪ rationalSupport (1-x)

theorem core_product : primeProduct core=210 := by
  have h : core={2,3,5,7} := by
    have p2 : Nat.Prime 2 := by decide
    have p3 : Nat.Prime 3 := by decide
    have p5 : Nat.Prime 5 := by decide
    have p7 : Nat.Prime 7 := by decide
    rw [core,show (210:ℕ)=2*3*5*7 by decide]
    simp (disch := decide) only [Nat.primeFactors_mul,p2.primeFactors,p3.primeFactors,p5.primeFactors,p7.primeFactors]
    decide
  rw [h,primeProduct]
  decide +revert
theorem core_subset : core ⊆ oldCutoff := by
  intro p h
  obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp h
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have le:=Nat.le_of_dvd (by decide : 0<210) dvd;omega),prime⟩

theorem minor_support (i j : Fin 5) : (det i j).natAbs.primeFactors ⊆ core := by
  intro p hp
  obtain ⟨prime,dvd,nz⟩ := Nat.mem_primeFactors.mp hp
  have lookup : ∀ i j : Fin 5, det i j≠0 → (det i j).natAbs∣210^8 := by decide
  exact Nat.mem_primeFactors.mpr ⟨prime,prime.dvd_of_dvd_pow (dvd.trans (lookup i j (Int.natAbs_ne_zero.mp nz))),by decide⟩

theorem unique_mark {i j : Fin 5} {A B : ℤ} (primitive : Int.gcd A B=1)
    {p : ℕ} (away : p∉core) (hi : p∈formPrimes i A B) (hj : p∈formPrimes j A B) : i=j := by
  by_contra distinct
  have prime := Nat.prime_of_mem_primeFactors hi
  have P : Prime (p:ℤ) := by simpa [Int.prime_iff_natAbs_prime] using prime
  have a : (p:ℤ) ∣ oldForm i A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors hi)
  have b : (p:ℤ) ∣ oldForm j A B := Int.natAbs_dvd_natAbs.mp (by simpa using Nat.dvd_of_mem_primeFactors hj)
  have nd : ¬(p:ℤ)∣det i j := by
    intro d
    apply away (minor_support i j ?_)
    exact Nat.mem_primeFactors.mpr ⟨prime,by simpa using Int.natAbs_dvd_natAbs.mpr d,Int.natAbs_ne_zero.mpr (det_ne distinct)⟩
  have da : (p:ℤ)∣det i j*A := by
    have m := dvd_sub (dvd_mul_of_dvd_right a (coeffB j)) (dvd_mul_of_dvd_right b (coeffB i))
    convert m using 1
    simp only [det,form_coeff]
    ring
  have db : (p:ℤ)∣det i j*B := by
    have m := dvd_sub (dvd_mul_of_dvd_right b (coeffA i)) (dvd_mul_of_dvd_right a (coeffA j))
    convert m using 1
    simp only [det,form_coeff]
    ring
  have g := Int.dvd_coe_gcd ((P.dvd_mul.mp da).resolve_left nd) ((P.dvd_mul.mp db).resolve_left nd)
  rw [primitive] at g
  exact prime.not_dvd_one (Int.natCast_dvd_natCast.mp g)

private theorem supported {S : Finset ℕ} {x : ℚ} :
    RationalSUnit S x ↔ x≠0 ∧ rationalSupport x⊆S := by
  simp only [RationalSUnit,rationalSupport,Finset.union_subset_iff]

theorem signed_units (t : Fin 10) (A B : ℤ) (off : ∀ i,oldForm i A B≠0) :
    let x:=crossRatio (first t) (second t) (third t) A B
    RationalSUnit (smallSet t A B) x ∧ RationalSUnit (smallSet t A B) (1-x) := by
  let i:=first t
  let j:=second t
  let k:=third t
  have ij : i≠j:=ne_of_lt (increasing t).1
  have jk : j≠k:=ne_of_lt (increasing t).2
  have ik : i≠k:=ne_of_lt (lt_trans (increasing t).1 (increasing t).2)
  let S:=smallSet t A B
  have a : formPrimes i A B⊆S:=fun _ h=>Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have b : formPrimes j A B⊆S:=fun _ h=>Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have c : formPrimes k A B⊆S:=fun _ h=>Finset.mem_union_right _ (Finset.mem_union_right _ h)
  have bound (u v n : Fin 5) (diff : u≠v) (sub : formPrimes n A B⊆S) :
      (det u v*oldForm n A B).natAbs.primeFactors⊆S := by
    rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr (det_ne diff)) (Int.natAbs_ne_zero.mpr (off n))]
    exact Finset.union_subset (fun _ h=>Finset.mem_union_left _ (minor_support u v h)) sub
  have dn:=mul_ne_zero (det_ne ij) (off k)
  have d:=bound i j k ij c
  have u:=ratio_unit (mul_ne_zero (det_ne jk.symm) (off i)) dn (bound k j i jk.symm a) d
  have v:=ratio_unit (mul_ne_zero (det_ne ik) (off j)) dn (bound i k j ik b) d
  let y:=((det i k*oldForm j A B:ℤ):ℚ)/((det i j*oldForm k A B:ℤ):ℚ)
  have sum : crossRatio i j k A B+y=1 := by
    unfold crossRatio y
    rw [←add_div,←Int.cast_add,minor_identity,div_self (by exact_mod_cast dn)]
  exact ⟨u,(show 1-crossRatio i j k A B=y by linarith).symm ▸ v⟩

theorem least_set_iff (t : Fin 10) (A B : ℤ) (off : ∀ i,oldForm i A B≠0) (S : Finset ℕ) :
    let x:=crossRatio (first t) (second t) (third t) A B
    RationalSUnit S x ∧ RationalSUnit S (1-x) ↔ leastSet t A B⊆S := by
  obtain ⟨u,v⟩:= signed_units t A B off
  dsimp only
  constructor
  · rintro ⟨hx,hy⟩
    exact Finset.union_subset (supported.1 hx).2 (supported.1 hy).2
  · intro h
    rcases Finset.union_subset_iff.1 h with ⟨hx,hy⟩
    exact ⟨supported.2 ⟨u.1,hx⟩,supported.2 ⟨v.1,hy⟩⟩

theorem least_subset (t : Fin 10) (A B : ℤ) (off : ∀ i,oldForm i A B≠0) :
    leastSet t A B⊆smallSet t A B := (least_set_iff t A B off _).1 (signed_units t A B off)

theorem small_primes (t : Fin 10) (A B : ℤ) {p : ℕ} (mem : p∈smallSet t A B) : p.Prime := by
  rcases Finset.mem_union.mp mem with x|x
  · exact Nat.prime_of_mem_primeFactors x
  · exact support_prime x

theorem support_mono {S T : Finset ℕ} (sub : S⊆T) (prime : ∀ p∈T,Nat.Prime p) :
    primeProduct S≤primeProduct T := by
  exact Nat.le_of_dvd (Finset.prod_pos fun p hp => (prime p hp).pos)
    (Finset.prod_dvd_prod_of_subset S T (fun p => p) sub)

end
end Sun28.MinimalConductors
#print axioms Sun28.MinimalConductors.core_product
#print axioms Sun28.MinimalConductors.core_subset
#print axioms Sun28.MinimalConductors.minor_support
#print axioms Sun28.MinimalConductors.unique_mark
#print axioms Sun28.MinimalConductors.signed_units
#print axioms Sun28.MinimalConductors.least_set_iff
#print axioms Sun28.MinimalConductors.least_subset
#print axioms Sun28.MinimalConductors.small_primes
#print axioms Sun28.MinimalConductors.support_mono
