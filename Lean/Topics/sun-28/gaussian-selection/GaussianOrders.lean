import OrderLcms
import LocalModulus
import RayOrders

namespace Sun28.GaussianSelection
open ManuscriptV15.Arithmetic Sun28.ContactFactors

/-- An order calculation on the actual Gaussian generators of the selected rational primes. -/
theorem orders_of_generators {ι : Type*} [Fintype ι] [Nonempty ι] (π : ι→Gaussian)
    (κ : ℕ) (T : Finset ℕ) (a : ℕ→ℕ)
    (κpos : 0<κ) (primes : ∀ p∈T,p.Prime) (two : 2∈T)
    (depth : ∀ p∈T,padicValNat p κ≤a p) (a2 : 6≤a 2)
    (ray : ∀ i,gaussianCongruent 16 (π i) (9,0))
    (cross : ∀ i j,(adjacentNorm (π i) false).gcd (adjacentNorm (π j) true)=4)
    (cop : ∀ i e,(adjacentNorm (π i) e).Coprime (7*avoidModulus T κ)) :
    ∃ o : Orders, o.plusOrder=orderLcm π true ∧ o.minusOrder=orderLcm π false ∧
      o.kernelModulus=κ ∧ o.T=T ∧ o.a=a := by
  classical
  have nz (i) (e) : adjacentNorm (π i) e≠0 := by
    intro eq
    cases e with
    | false => have v:=(ray_dyadic (ray i)).2; rw [eq,padicValNat_zero_right] at v; contradiction
    | true => have v:=(ray_dyadic (ray i)).1; rw [eq,padicValNat_zero_right] at v; contradiction
  have l0 (e) : 0<orderLcm π e := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i _=>nz i e))
  have vp : padicValNat 2 (orderLcm π true)=2 := constant_order_lcm _ Finset.univ_nonempty _ Nat.prime_two
    (fun i _=>nz i true) (fun i _=>(ray_dyadic (ray i)).1)
  have vm : padicValNat 2 (orderLcm π false)=6 := constant_order_lcm _ Finset.univ_nonempty _ Nat.prime_two
    (fun i _=>nz i false) (fun i _=>(ray_dyadic (ray i)).2)
  have gc : (orderLcm π true).gcd (orderLcm π false)=4 :=
    pairwise_gcd_lcms Finset.univ _ _ (fun i _=> nz i true) (fun j _=>nz j false) vp vm
      (fun i _ j _=> Nat.gcd_comm .. ▸ cross j i)
  obtain ⟨_,_,_,_,div⟩:=avoid_modulus_spec T κ primes
  have off (p : ℕ) (prime : p.Prime) (mem : p∈T∪κ.primeFactors) (odd : p≠2) (e) :
      ¬p∣orderLcm π e := by
    intro divides
    obtain ⟨i,_,bad⟩:=(prime_dvd_lcm_iff _ _ prime).mp divides
    exact ((prime.coprime_iff_not_dvd).mp ((cop i e).symm.of_dvd_left (div p mem odd))) bad
  let o : Orders := {
    plusOrder:=orderLcm π true, minusOrder:=orderLcm π false, kernelModulus:=κ, T:=T, a:=a
    plus_pos:=l0 true, minus_pos:=l0 false, kernel_pos:=κpos, prime:=primes, two:=two
    common:=gc, dyadic_plus:=vp, dyadic_minus:=vm, depth:=depth, dyadic_depth:=a2
    local_avoid:=fun p h odd d=>
      ((primes p h).dvd_mul.mp d).elim
        (off p (primes p h) (Finset.mem_union_left _ h) odd true)
        (off p (primes p h) (Finset.mem_union_left _ h) odd false)
    kernel_avoid:=fun p h odd=>off p (Nat.prime_of_mem_primeFactors h) (Finset.mem_union_right _ h) odd false }
  exact ⟨o,rfl,rfl,rfl,rfl,rfl⟩

end Sun28.GaussianSelection
#print axioms Sun28.GaussianSelection.orders_of_generators
