import PairedUnits
import MordellSupport

/-! Remove the full cube divisor from a signed coefficient. -/
namespace Sun28.HeightCubics
open Sun28.FiveMarkUnits
noncomputable section

def surviving (a:ℤ) : Finset ℕ :=
  a.natAbs.primeFactors.filter fun p=>a.natAbs.factorization p%3≠0

def cubePart (a:ℤ) : ℤ :=
  a.sign * ((∏ p∈surviving a,p^(a.natAbs.factorization p%3):ℕ):ℤ)

def cubeRoot (a:ℤ) : ℤ :=
  ((∏ p∈a.natAbs.primeFactors,p^(a.natAbs.factorization p/3):ℕ):ℤ)

theorem factor_cube {a:ℤ} (nz:a≠0) : a=cubePart a*cubeRoot a^3 := by
  let f:=a.natAbs.primeFactors
  let e:ℕ:=∏ p∈surviving a,p^(a.natAbs.factorization p%3)
  let u:ℕ:=∏ p∈f,p^(a.natAbs.factorization p/3)
  have comp : e= ∏ p∈f,p^(a.natAbs.factorization p%3):=by
    unfold e surviving
    apply Finset.prod_subset (Finset.filter_subset _ _)
    intro p hp no
    have h : a.natAbs.factorization p%3=0:=by
      by_contra bad;exact no (Finset.mem_filter.mpr ⟨hp,bad⟩)
    simp [h]
  have fact:a.natAbs=e*u^3:=by
    rw [comp];unfold u;rw [←Finset.prod_pow,←Finset.prod_mul_distrib]
    calc
      a.natAbs=∏ p∈f,p^(a.natAbs.factorization p):= Nat.prod_primeFactors_pow_factorization (Int.natAbs_ne_zero.mpr nz)
      _ = _ := by
        apply Finset.prod_congr rfl
        intro p _
        rw [←pow_mul,←pow_add]
        congr 1
        omega
  have sign:=Int.sign_mul_natAbs a
  change a=a.sign*(e:ℤ)*(u:ℤ)^3
  calc
    a=a.sign*(a.natAbs:ℤ):=sign.symm
    _ = _ :=by rw [fact];push_cast;ring

theorem cap_part {a:ℤ} (nz:a≠0) : (cubePart a).natAbs≤(primeProduct (surviving a))^2 := by
  unfold cubePart primeProduct
  rw [Int.natAbs_mul,Int.natAbs_sign_of_ne_zero nz,one_mul,Int.natAbs_natCast,←Finset.prod_pow]
  exact Finset.prod_le_prod (fun p hp=>Nat.pow_le_pow_right
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos (by omega))

theorem part_dvd {a:ℤ} (nz:a≠0) : cubePart a∣a := ⟨_,factor_cube nz⟩

theorem root_dvd {a:ℤ} (nz:a≠0) : cubeRoot a∣a := ⟨cubePart a*cubeRoot a^2,by
  conv_lhs=>rw [factor_cube nz]
  ring⟩

theorem coeff_primes {a:ℤ} (nz:a≠0) : (cubePart a).natAbs.primeFactors⊆surviving a := by
  let f:=surviving a
  have ep:0<∏ p∈f,p^(a.natAbs.factorization p%3):=
    Finset.prod_pos fun p hp=>pow_pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos _
  unfold cubePart
  rw [Int.natAbs_mul,Int.natAbs_sign_of_ne_zero nz,one_mul,Int.natAbs_natCast]
  intro p mem
  have ⟨pr,dv,_⟩:=Nat.mem_primeFactors.mp mem
  obtain ⟨q,hq,d⟩:=(pr.prime.dvd_finsetProd_iff _).mp dv
  have pq:=pr.dvd_of_dvd_pow d
  have eq:=(Nat.prime_dvd_prime_iff_eq pr (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1)).mp pq
  exact eq ▸ hq

end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.factor_cube
#print axioms Sun28.HeightCubics.cap_part
#print axioms Sun28.HeightCubics.part_dvd
#print axioms Sun28.HeightCubics.root_dvd
#print axioms Sun28.HeightCubics.coeff_primes
