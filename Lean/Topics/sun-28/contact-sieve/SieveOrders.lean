import ContactSieve

namespace Sun28.ContactSieve
open ZInQ Sun28.Ordinary Sun28.FixedPreparation Sun28.Forward Sun28.RealPoleBounds
open Sun28.ContactFactors Sun28.GaussianSelection ManuscriptV15.Arithmetic

private theorem seven_free {z : Gaussian} (r7 : gaussianCongruent 7 z (1,3)) (e : Bool) :
    ¬7∣adjacentNorm z e := by
  intro d
  have eq : (adjacentNorm z e:ℤ) ≡ 0 [ZMOD 7] :=
    Int.modEq_zero_iff_dvd.mpr (Int.natCast_dvd_natCast.mpr d)
  cases e with
  | true => exact (by decide : ¬(6:ℤ) ≡ 0 [ZMOD 7]) ((ray_seven r7).1.symm.trans eq)
  | false => exact (by decide : ¬(2:ℤ) ≡ 0 [ZMOD 7]) ((ray_seven r7).2.symm.trans eq)

/-- Only odd mixed collision exclusion is needed to determine the gcd of the two lcms. -/
theorem gcd_four_of_mixed {x y : ℕ} (xp : 0<x) (yp : 0<y)
    (vx : padicValNat 2 x=2) (vy : padicValNat 2 y=6)
    (off : ∀ l : ℕ,l.Prime → l≠2 → ¬(l∣x ∧ l∣y)) : x.gcd y=4 := by
  apply Nat.eq_of_factorization_eq (by simp [Nat.gcd_eq_zero_iff,xp.ne']) (by decide)
  intro p
  by_cases two : p=2
  · subst p
    rw [Nat.factorization_gcd xp.ne' yp.ne']
    change min (x.factorization 2) (y.factorization 2) = Nat.factorization 4 2
    rw [Nat.factorization_def _ Nat.prime_two,Nat.factorization_def _ Nat.prime_two,
      Nat.factorization_def _ Nat.prime_two,vx,vy]
    exact (padicValNat.prime_pow (p:=2) 2).symm
  by_cases prime : p.Prime
  · have nod : ¬p∣4 := by
      rw [show 4=2*2 by decide,prime.dvd_mul,Nat.prime_dvd_prime_iff_eq prime Nat.prime_two]
      simp [two]
    have nog : ¬p∣x.gcd y := fun d=>off p prime two
      ⟨d.trans (Nat.gcd_dvd_left ..),d.trans (Nat.gcd_dvd_right ..)⟩
    rw [Nat.factorization_eq_zero_of_not_dvd nog,Nat.factorization_eq_zero_of_not_dvd nod]
  · rw [Nat.factorization_eq_zero_of_not_prime _ prime,Nat.factorization_eq_zero_of_not_prime _ prime]

private theorem build_orders {A : Fin 3→ℚ} {u v : ℕ} {h : PrimeValues A u v}
    {π : ↥(shifts A)→Gaussian} (az : NormRays A h π) (κ : ℕ) (T : Finset ℕ) (a : ℕ→ℕ)
    (κp : 0<κ) (primes : ∀ p∈T,p.Prime) (two : 2∈T) (depth : ∀ p∈T,padicValNat p κ≤a p)
    (a2 : 6≤a 2) (mixed : MixedAndLocal π T κ) :
    ∃ o : Orders, o.plusOrder=orderLcm π true ∧ o.minusOrder=orderLcm π false ∧
      o.kernelModulus=κ ∧ o.T=T ∧ o.a=a := by
  classical
  let _ : Nonempty ↥(shifts A) := ⟨⟨-0/A 0,shift_mem A 0 (by norm_num [marks])⟩⟩
  have nz (i) (e) : adjacentNorm (π i) e≠0 := by
    intro eq
    cases e with
    | false => have vv:=(ray_dyadic (az.ray16 i)).2; rw [eq,padicValNat_zero_right] at vv; contradiction
    | true => have vv:=(ray_dyadic (az.ray16 i)).1; rw [eq,padicValNat_zero_right] at vv; contradiction
  have l0 (e) : 0<orderLcm π e := Nat.pos_of_ne_zero (Finset.lcm_ne_zero_iff.mpr (fun i _=>nz i e))
  have vp : padicValNat 2 (orderLcm π true)=2 := constant_order_lcm _ Finset.univ_nonempty _ Nat.prime_two
    (fun i _=>nz i true) (fun i _=>(ray_dyadic (az.ray16 i)).1)
  have vm : padicValNat 2 (orderLcm π false)=6 := constant_order_lcm _ Finset.univ_nonempty _ Nat.prime_two
    (fun i _=>nz i false) (fun i _=>(ray_dyadic (az.ray16 i)).2)
  have gcd : (orderLcm π true).gcd (orderLcm π false)=4 := by
    apply gcd_four_of_mixed (l0 _) (l0 _) vp vm
    intro p prime odd collision
    obtain ⟨r,_,plus⟩ := (prime_dvd_lcm_iff _ _ prime).mp collision.1
    obtain ⟨s,_,minus⟩ := (prime_dvd_lcm_iff _ _ prime).mp collision.2
    by_cases seven : p=7
    · exact seven_free (az.ray7 r) true (seven ▸ plus)
    · exact mixed.1 r s p prime odd seven ⟨plus,minus⟩
  have avoidT (p) (hp : p∈T) (odd : p≠2) e : ¬p∣orderLcm π e := by
    intro d
    obtain ⟨r,_,g⟩ := (prime_dvd_lcm_iff _ _ (primes p hp)).mp d
    by_cases seven : p=7
    · exact seven_free (az.ray7 r) e (seven ▸ g)
    · exact mixed.2.1 p hp odd seven r e g
  have avoidκ (p) (hp : p∈κ.primeFactors) (odd : p≠2) : ¬p∣orderLcm π false := by
    by_cases mem : p∈T
    · exact avoidT p mem odd false
    intro d
    obtain ⟨r,_,g⟩ := (prime_dvd_lcm_iff _ _ (Nat.prime_of_mem_primeFactors hp)).mp d
    by_cases seven : p=7
    · exact seven_free (az.ray7 r) false (seven ▸ g)
    · exact mixed.2.2 p hp mem odd seven r g
  exact ⟨{ plusOrder:=orderLcm π true,minusOrder:=orderLcm π false,kernelModulus:=κ,T:=T,a:=a
           plus_pos:=l0 true,minus_pos:=l0 false,kernel_pos:=κp,prime:=primes,two:=two
           common:=gcd,dyadic_plus:=vp,dyadic_minus:=vm,depth:=depth,dyadic_depth:=a2
           local_avoid:=fun p hp odd d=>((primes p hp).dvd_mul.mp d).elim (avoidT p hp odd true) (avoidT p hp odd false)
           kernel_avoid:=avoidκ },rfl,rfl,rfl,rfl,rfl⟩

theorem select_with_orders (sieve : PrimePatterns) {X c q : ℤ} {n : Fin 4→ℤ}
    (roots : AdmissibleRoots X c q n) (d κ : ℕ) (T : Finset ℕ) (a : ℕ→ℕ) (dp : 0<d) (κp : 0<κ)
    (primes : ∀ p∈T,p.Prime) (two : 2∈T) (depth : ∀ p∈T,padicValNat p κ≤a p) (a2 : 6≤a 2)
    (H Y : ℝ) :
    let A:=fixedScale n
    ∃ (u v : ℕ) (h : PrimeValues A u v) (π : ↥(shifts A)→Gaussian) (o : Orders),
      0<u ∧ 0<v ∧ d∣v ∧ H<(Sun28.ContactFactors.slope A u v:ℝ) ∧ (∀ r∈shifts A,Y<(h.value r:ℝ)) ∧
      (∀ j,∀ p∈selected h j,¬p∣dilation A ∧ ¬p∣separation ∧ padicValRat p (A j)=0) ∧
      NormRays A h π ∧ o.plusOrder=orderLcm π true ∧ o.minusOrder=orderLcm π false ∧
      o.kernelModulus=κ ∧ o.T=T ∧ o.a=a := by
  let A:=fixedScale n
  have alive : ∀ j,A j≠0 := fun j=>(actual_scales_positive n (fun i=>(roots.odd i).1.ne') j).ne'
  obtain ⟨u,v,h,π,vp,div,big,large,oriented,mixed⟩:=sieve X c q n roots d κ T dp κp primes two H (primeSize A Y)
  have up : 0<u := by
    have mem : (0:ℚ)∈shifts A := by simpa using (shift_mem A 0 (by norm_num [marks] : (0:ℚ)∈marks))
    have eq:=h.equation 0 mem
    have eq' : h.value 0=u := by exact_mod_cast (by simpa [offset] using eq : (h.value 0:ℤ)=u)
    exact eq' ▸ (h.prime 0 mem).pos
  obtain ⟨o,plus,minus,ko,ts,as⟩:=build_orders oriented κ T a κp primes two depth a2 mixed
  have good (r : ℚ) (hr : r∈shifts A) := large_prime_exclusions A Y alive (large r hr)
  refine ⟨u,v,h,π,o,up,vp,div,big,fun r hr=>(good r hr).1,?_,oriented,plus,minus,ko,ts,as⟩
  intro j p hp
  obtain ⟨θ,hθ,rfl⟩:=Finset.mem_image.mp hp
  have g := (good (-θ/A j) (shift_mem A j hθ)).2
  exact ⟨g.1,g.2.1,g.2.2 j⟩

end Sun28.ContactSieve
#print axioms Sun28.ContactSieve.gcd_four_of_mixed
#print axioms Sun28.ContactSieve.select_with_orders
