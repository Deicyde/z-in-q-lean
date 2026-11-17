import CubePart

/-! Integral cube decompositions give a point on a rational Mordell curve. -/
namespace Sun28.HeightCubics
open Sun28.FiveMarkUnits Sun28.MinimalConductors ZInQBlueprint.TwistDescent
noncomputable section

def places (P Q R : ℤ) : Finset ℕ :=
  surviving P ∪ (surviving Q ∪ (R.natAbs.primeFactors ∪ (2:ℕ).primeFactors))

def conductor (P Q R : ℤ) := primeProduct (places P Q R)

theorem places_prime {P Q R : ℤ} {p:ℕ} (mem:p∈places P Q R) : p.Prime := by
  simp only [places,Finset.mem_union] at mem
  rcases mem with a|b|c|d
  · exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp a).1
  · exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp b).1
  · exact Nat.prime_of_mem_primeFactors c
  · exact Nat.prime_of_mem_primeFactors d

private theorem integral {S:Finset ℕ} (n w:ℤ) (wn:w≠0) (inc:w.natAbs.primeFactors⊆S)
    {j:ℕ} (jp:j≠0) : IsSInteger S ((n:ℚ)/(w:ℚ)^j) := by
  have d:=Rat.den_dvd n (w^j)
  rw [Rat.divInt_eq_div,Int.cast_pow] at d
  have m:=Int.natAbs_dvd_natAbs.mpr d
  rw [Int.natAbs_natCast,Int.natAbs_pow] at m
  exact (Nat.primeFactors_mono m (pow_ne_zero _ (Int.natAbs_ne_zero.mpr wn))).trans
    (by rw [Nat.primeFactors_pow _ jp];exact inc)

private theorem mul_support {S:Finset ℕ} {u v:ℤ} (un:u≠0) (vn:v≠0)
    (m:u.natAbs.primeFactors⊆S) (n:v.natAbs.primeFactors⊆S) : (u*v).natAbs.primeFactors⊆S := by
  rw [Int.natAbs_mul,Nat.primeFactors_mul (Int.natAbs_ne_zero.mpr un) (Int.natAbs_ne_zero.mpr vn)]
  exact Finset.union_subset m n

/-- The slope P/R and the point share the same chosen sign of the ordinate. -/
theorem mordell_point {P Q R:ℤ} (pn:P≠0) (qn:Q≠0) (rn:R≠0) (sum:P+Q=R) :
    ∃ (c:ℤ) (X Y:ℚ),c≠0 ∧ c.natAbs≤4*conductor P Q R^6 ∧
    (c^2).natAbs.primeFactors⊆places P Q R ∧
    IsSInteger (places P Q R) X ∧ IsSInteger (places P Q R) Y ∧
    Y^2=X^3+(c:ℚ)^2 ∧ (P:ℚ)/R=(1+Y/(c:ℚ))/2 := by
  let g:=cubePart P
  let h:=cubePart Q
  let k:=cubePart R
  let u:=cubeRoot P
  let v:=cubeRoot Q
  let w:=cubeRoot R
  let S:=places P Q R
  have eP:P=g*u^3:=factor_cube pn
  have eQ:Q=h*v^3:=factor_cube qn
  have eR:R=k*w^3:=factor_cube rn
  have gn:g≠0:=fun z=>pn (by simp [eP,z])
  have hn:h≠0:=fun z=>qn (by simp [eQ,z])
  have kn:k≠0:=fun z=>rn (by simp [eR,z])
  have wn:w≠0:=fun z=>rn (by simp [eR,z])
  have subP:surviving P⊆S:=Finset.subset_union_left
  have subQ:surviving Q⊆S:=Finset.subset_union_left.trans Finset.subset_union_right
  have subR:R.natAbs.primeFactors⊆S:=Finset.subset_union_left.trans
    (Finset.subset_union_right.trans Finset.subset_union_right)
  have subK:surviving R⊆S:=(Finset.filter_subset _ _).trans subR
  have sub2:(2:ℕ).primeFactors⊆S:=Finset.subset_union_right.trans
    (Finset.subset_union_right.trans Finset.subset_union_right)
  have pr (p) (m:p∈S):p.Prime:=places_prime m
  have bound (a:ℤ) (an:a≠0) (sub:surviving a⊆S) : (cubePart a).natAbs≤conductor P Q R^2:=
    (cap_part an).trans (Nat.pow_le_pow_left (support_mono sub pr) _)
  have gs:g.natAbs.primeFactors⊆S:=(coeff_primes pn).trans subP
  have hs:h.natAbs.primeFactors⊆S:=(coeff_primes qn).trans subQ
  have ks:k.natAbs.primeFactors⊆S:=(coeff_primes rn).trans subK
  have ws:w.natAbs.primeFactors⊆S:=(Nat.primeFactors_mono (Int.natAbs_dvd_natAbs.mpr (root_dvd rn))
      (Int.natAbs_ne_zero.mpr rn)).trans subR
  have s4:(4:ℤ).natAbs.primeFactors⊆S:=by
    change ((2:ℕ)^2).primeFactors⊆S
    rw [Nat.primeFactors_pow _ (by decide : 2≠0)];exact sub2
  let c:ℤ:=4*g*h*k
  let X:ℚ:=((-4*g*h*u*v:ℤ):ℚ)/(w:ℚ)^2
  let Y:ℚ:=((4*g*h*(P-Q):ℤ):ℚ)/(w:ℚ)^3
  have cn:c≠0:=mul_ne_zero (mul_ne_zero (mul_ne_zero (by decide) gn) hn) kn
  have cs:c.natAbs.primeFactors⊆S:=mul_support (mul_ne_zero (mul_ne_zero (by decide) gn) hn) kn
    (mul_support (mul_ne_zero (by decide) gn) hn (mul_support (by decide) gn s4 gs) hs) ks
  refine ⟨c,X,Y,cn,?_,?_,integral _ _ wn ws (by decide),integral _ _ wn ws (by decide),?_,?_⟩
  · dsimp only [c];simp only [Int.natAbs_mul];change 4*g.natAbs*h.natAbs*k.natAbs≤_
    calc
      _ ≤ 4*(conductor P Q R^2)*(conductor P Q R^2)*(conductor P Q R^2) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left _ (bound _ pn subP)) (bound _ qn subQ)) (bound _ rn subK)
      _ = _ :=by ring
  · rw [Int.natAbs_pow,Nat.primeFactors_pow _ (by decide : 2≠0)];exact cs
  · have id : (4*g*h*(P-Q))^2=(-4*g*h*u*v)^3+c^2*w^6 := by
      have a:P*Q=g*h*(u*v)^3:=by rw [eP,eQ];ring
      have b:c*w^3=4*g*h*(P+Q):=by rw [sum,eR];dsimp only [c];ring
      linear_combination -64*g^2*h^2*a-(c*w^3+4*g*h*(P+Q))*b
    have qi : ((4*g*h*(P-Q):ℤ):ℚ)^2=((-4*g*h*u*v:ℤ):ℚ)^3+(c:ℚ)^2*(w:ℚ)^6 := by exact_mod_cast id
    have wz:(w:ℚ)≠0:=by exact_mod_cast wn
    dsimp only [X,Y]
    rw [div_pow,div_pow,←pow_mul,←pow_mul]
    change ((4*g*h*(P-Q):ℤ):ℚ)^2/(w:ℚ)^6=((-4*g*h*u*v:ℤ):ℚ)^3/(w:ℚ)^6+(c:ℚ)^2
    rw [qi,add_div]
    field_simp
  · have scale : ((4*g*h*(P-Q):ℤ):ℚ)/(w:ℚ)^3/(c:ℚ)=((P-Q:ℤ):ℚ)/(R:ℚ) := by
      rw [eR];dsimp only [c];push_cast
      field_simp [show (w:ℚ)≠0 by exact_mod_cast wn,show (g:ℚ)≠0 by exact_mod_cast gn,
        show (h:ℚ)≠0 by exact_mod_cast hn,show (k:ℚ)≠0 by exact_mod_cast kn]
    change (P:ℚ)/R=(1+((4*g*h*(P-Q):ℤ):ℚ)/(w:ℚ)^3/(c:ℚ))/2
    rw [scale]
    have su:(P:ℚ)+(Q:ℚ)=R:=by exact_mod_cast sum
    field_simp [show (R:ℚ)≠0 by exact_mod_cast rn]
    push_cast
    linarith only [su]
end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.places_prime
#print axioms Sun28.HeightCubics.mordell_point
