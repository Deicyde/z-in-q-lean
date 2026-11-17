import SieveOrders

namespace Sun28.ContactSieve
open ZInQ Sun28.Ordinary Sun28.FixedPreparation Sun28.Forward Sun28.RealPoleBounds
open Sun28.ContactFactors Sun28.GaussianSelection ManuscriptV15.Arithmetic

/-- The archived all-shift theorem implies the restricted arithmetic input.
Same-sign pairs, the redundant primality witness and the auxiliary rays do not enter its conclusion. -/
theorem of_gaussianTuples (gauss : GaussianTuples) : PrimePatterns := by
  intro X c q n roots d κ T dp κp primes two H Y
  let A:=fixedScale n
  let a (p : ℕ) := max 6 (padicValNat p κ)
  have unit : A 0=1 := by norm_num [A,fixedScale,scaleRoot]
  have alive : ∀ j,A j≠0 := fun j=>(actual_scales_positive n (fun i=>(roots.odd i).1.ne') j).ne'
  obtain ⟨u,v,h,π,_,_,vp,div,big,ahead,_,o,_,_,_,_,_⟩:=
    GaussianSelection.select_with_orders gauss A unit alive d κ T a dp κp primes two
      (fun _ _=>le_max_right ..) (le_max_left ..) H Y
  refine ⟨u,v,h,π,vp,div,big,ahead,⟨fun r=>(o.norm r).2,o.ray16,o.ray7⟩,?_,?_,?_⟩
  · intro r s l prime odd _ coll
    have d4 : l∣4 := o.cross s r ▸ Nat.dvd_gcd coll.2 coll.1
    have d2 : l∣2 := (prime.dvd_mul.mp (show l∣2*2 from d4)).elim id id
    exact odd ((Nat.prime_dvd_prime_iff_eq prime Nat.prime_two).mp d2)
  · intro l hT odd _ r e collision
    have all := (avoid_modulus_spec T κ primes).2.2.2.2 l (Finset.mem_union_left _ hT) odd
    exact ((primes l hT).coprime_iff_not_dvd.mp ((o.avoid r e).symm.of_dvd_left all)) collision
  · intro l hκ _ odd _ r collision
    have all := (avoid_modulus_spec T κ primes).2.2.2.2 l (Finset.mem_union_right _ hκ) odd
    exact ((Nat.prime_of_mem_primeFactors hκ).coprime_iff_not_dvd.mp
      ((o.avoid r false).symm.of_dvd_left all)) collision

end Sun28.ContactSieve
#print axioms Sun28.ContactSieve.of_gaussianTuples
