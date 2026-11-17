import PreparedPoleData
import FamilyLocal

namespace Sun28.TwistRank
open ZInQ.RouteK PreparedPoles PairedClasses FixedPreparation ScalarHeight
noncomputable section

/-- The odd local symbols required by the actual preparation primes.  The
dyadic class is already determined by θ = 1 modulo 24. -/
def FixedSquares (θ : ℕ) : Prop := ∀ p ∈ primes, p.Prime → p≠2 →
  ¬p∣θ ∧ LocalSquareAt p θ

/-- The extra relation arising from the two squareclasses of the same B.
Both coordinates are nonzero for a prepared positive B. -/
def NormConic (β θ : ℕ) : Prop :=
  ∃ u v : ℚ, u≠0 ∧ v≠0 ∧ (β:ℚ)*u^2+θ*v^2=1

theorem conic_of_scales {B b t m a d : ℚ} (bm : m*B≠0) (an : a≠0) (dn : d≠0)
    (first : m*B=b*a^2) (second : (m*B)*(m*B-B^2)=t*d^2) :
    ∃ u v : ℚ, u≠0 ∧ v≠0 ∧ b*u^2+t*v^2=1 := by
  have mn:=left_ne_zero_of_mul bm
  have bn:=right_ne_zero_of_mul bm
  refine ⟨a/m,d/(m*B),div_ne_zero an mn,div_ne_zero dn bm,?_⟩
  field_simp
  linear_combination B^2 * first.symm - second

/-- Integer membership in the printed finite list prevents square factors at
every prime. This applies to the multiplier returned by choose_classes. -/
theorem listed_squarefree {m : ℤ} (member : (m:ℚ)∈smallMultipliers) : Squarefree m := by
  obtain ⟨⟨n,a,b,i⟩,_,eq⟩ := Finset.mem_image.mp member
  change (shift n a b i:ℚ)=(m:ℚ) at eq
  have e : shift n a b i=m := by exact_mod_cast eq
  rw [←e,←Int.squarefree_natAbs]
  have div : (shift n a b i).natAbs∣FixedPreparation.primorial :=
    (show ∀ n a b : Bool, ∀ i : Fin 8, (shift n a b i).natAbs∣FixedPreparation.primorial by decide) n a b i
  have prime : ∀ p∈primes, Nat.Prime p := by decide
  have prod : Squarefree FixedPreparation.primorial := by
    rw [←prime_product]
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq ne=>?_) (fun p hp=>(prime p hp).squarefree)
    simp only [Function.onFun,←Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (prime p hp) (prime q hq)).mpr ne
  exact prod.squarefree_of_dvd div

/-- Recover the conic both as a rational equation and as an integral
factorization with controlled numerator depth. -/
theorem integral_conic {B : ℚ} (h : Prepared B) {m : ℤ} (mp : 0 < m) :
    ∃ a k c : ℤ, 0<k ∧ (∀ p∈primes, p.Prime → ¬(p:ℤ)∣k ∧ (p:ℤ)^4∣a) ∧
      thetaOf B m*c^2=(m*k)^2-m*a := by
  obtain ⟨k,hk,hn,_,_,_⟩ := (prepared_admissible h).decode
  have mr : (m:ℚ)≠B := by
    have m1 : (1:ℚ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    linarith [h.2.2.1]
  obtain ⟨_,e⟩ := betaOf_thetaOf_eq_sqfInt hk mp.ne' h.2.1.ne' mr
  have kn : 0<k := Nat.pos_of_ne_zero (fun z => B.den_ne_zero (by simpa only [z,zero_pow two_ne_zero] using hk))
  have v : (m*(k:ℤ))^2-m*B.num≠0 := by
    intro z
    have f : m*(m*(k:ℤ)^2-B.num)=0 := by linear_combination z
    have eq := (mul_eq_zero.mp f).resolve_left mp.ne'
    apply mr
    rw [← Rat.num_div_den B,eq_div_iff (by exact_mod_cast B.den_ne_zero)]
    exact_mod_cast (show m*(B.den:ℤ)=B.num by rw [hk];push_cast;linarith)
  obtain ⟨_,c,_,pc⟩ := sqfInt_spec v
  refine ⟨B.num,k,c,by exact_mod_cast kn,?_,by rw [e];exact pc.symm⟩
  intro p mem pp
  obtain ⟨nk,depth⟩ := numerator_depth h pp mem
  exact ⟨fun d=>nk (hk ▸ dvd_pow (Int.natCast_dvd_natCast.mp d) two_ne_zero),depth⟩

private theorem local_symbols {p : ℕ} (pp : p.Prime) {m a k θ c : ℤ}
    [Fact p.Prime] (ms : Squarefree m) (den : ¬(p:ℤ)∣k) (deep : (p:ℤ)^4∣a) (sf : Squarefree θ)
    (eqn : θ*c^2=(m*k)^2-m*a) : ¬(p:ℤ)∣θ ∧ legendreSym p θ=1 := by
  have pr := Nat.prime_iff_prime_int.mp pp
  obtain ⟨b,rfl⟩ := deep
  by_cases pm : (p:ℤ)∣m
  · obtain ⟨d,rfl⟩ := pm
    have d0 : ¬(p:ℤ)∣d := fun e => pr.not_isUnit (ms (p:ℤ) (by
      exact mul_dvd_mul_left _ e))
    have u : ¬(p:ℤ)∣d*k := fun e => (pr.dvd_or_dvd e).elim d0 den
    obtain ⟨nd,x,nx,hx⟩ := local_unit_square (e:=1) (j:=3) (X:=(p:ℤ)*d*((p:ℤ)^4*b))
      pp (by decide) sf u ⟨d*b,by ring⟩ (by rw [eqn];ring)
    exact ⟨nd,legendreSym_eq_one_of_modEq nx u (hx.of_dvd (dvd_pow_self _ (by decide : 3≠0)))⟩
  · have u : ¬(p:ℤ)∣m*k := fun e => (pr.dvd_or_dvd e).elim pm den
    obtain ⟨nd,x,nx,hx⟩ := local_unit_square (e:=0) (j:=3) (X:=m*((p:ℤ)^4*b))
      pp (by decide) sf u ⟨m*(p:ℤ)*b,by ring⟩ (by rw [eqn];ring)
    exact ⟨nd,legendreSym_eq_one_of_modEq nx u (hx.of_dvd (dvd_pow_self _ (by decide : 3≠0)))⟩

/-- On every pole input, the second class is a unit square at every odd
preparation prime, including primes not dividing β.  The squarefree classes
already used by the source can be kept exactly. -/
theorem actual_pair {B : ℚ} (h : Prepared B) {m : ℤ} {β θ : ℕ}
    (member : (m:ℚ)∈smallMultipliers) (classes : PreparedClasses B m β θ) :
    FixedSquares θ ∧ NormConic β θ := by
  obtain ⟨a,an,A⟩ := classes.beta_scale
  obtain ⟨d,dn,H⟩ := classes.theta_scale
  have bp : (0:ℚ)<β := by exact_mod_cast classes.beta_positive
  have pos : (0:ℚ) < m*B := by rw [A]; exact mul_pos bp (sq_pos_of_ne_zero an)
  have mp : 0 < m := by exact_mod_cast pos_of_mul_pos_left pos h.2.1.le
  have te : thetaOf B m=(θ:ℤ) := by
    apply sqf_eq_of_eq_mul_sq (Int.squarefree_natCast.mpr classes.theta_sf) (div_ne_zero dn h.2.1.ne')
    change (m:ℚ)*(m-B)=(θ:ℚ)*(d/B)^2
    field_simp [h.2.1.ne']
    linear_combination H
  refine ⟨?_,conic_of_scales pos.ne' an dn A H⟩
  obtain ⟨a,k,c,_,depth,eq⟩ := integral_conic h mp
  rw [te] at eq
  intro p mem pp odd
  let : Fact p.Prime := ⟨pp⟩
  obtain ⟨den,deep⟩ := depth p mem pp
  obtain ⟨nd,leg⟩ := local_symbols pp (listed_squarefree member) den deep
    (Int.squarefree_natCast.mpr classes.theta_sf) eq
  exact ⟨fun d=>nd (Int.natCast_dvd_natCast.mpr d),local_square_of_legendre odd leg⟩

end
end Sun28.TwistRank
#print axioms Sun28.TwistRank.conic_of_scales
#print axioms Sun28.TwistRank.listed_squarefree
#print axioms Sun28.TwistRank.integral_conic
#print axioms Sun28.TwistRank.actual_pair
