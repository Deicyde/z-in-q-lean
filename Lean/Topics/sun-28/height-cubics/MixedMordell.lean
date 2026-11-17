import CubicMordell

/-! The three different weights of a Mordell equation absorb squares, cubes and sixth powers. -/
namespace Sun28.HeightCubics
open Sun28.FiveMarkUnits Sun28.MinimalConductors ZInQBlueprint.TwistDescent ZInQ.RouteK
open private integral mul_support from CubicMordell
open private kernel_primes from SignedSupport
noncomputable section

def mixedPlaces (P Q R:ℤ) : Finset ℕ :=
  (sqfInt P).natAbs.primeFactors ∪ (surviving Q ∪ R.natAbs.primeFactors)
def mixedN (P Q R:ℤ) := primeProduct (mixedPlaces P Q R)

theorem mixed_prime {P Q R:ℤ} {p:ℕ} (m:p∈mixedPlaces P Q R) : p.Prime := by
  rcases Finset.mem_union.mp m with a|b
  · exact Nat.prime_of_mem_primeFactors a
  rcases Finset.mem_union.mp b with a|b
  · exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp a).1
  · exact Nat.prime_of_mem_primeFactors b

private theorem squarecap {z:ℤ} (nz:z≠0) :
    (sqfInt z).natAbs=primeProduct (sqfInt z).natAbs.primeFactors := by
  rw [kernel_primes nz,sqfInt,Int.natAbs_mul,Int.natAbs_sign_of_ne_zero nz,one_mul,Int.natAbs_natCast]
  unfold sqfNat primeProduct
  congr 1
  apply Finset.filter_congr
  intro p mem
  rw [padicValInt,←Nat.factorization_def _ (Nat.prime_of_mem_primeFactors mem)]

private theorem prime_sub {u v:ℤ} (d:u∣v) (nz:v≠0) : u.natAbs.primeFactors⊆v.natAbs.primeFactors :=
  Nat.primeFactors_mono (Int.natAbs_dvd_natAbs.mpr d) (Int.natAbs_ne_zero.mpr nz)

/-- For the signed weighted equation d*u²+e*v³=f*w⁶ the point is
X=-d*e*v/w², Y=d²*e*u/w³. Only the squarefree and cubefree parts
of the first two nonzero rows can enter the set of inverted primes. -/
theorem mixed_point {P Q R:ℤ} (pn:P≠0) (qn:Q≠0) (rn:R≠0) (sum:P+Q=R) :
    ∃ (a:ℤ) (X Y:ℚ),a≠0 ∧ a.natAbs≤ mixedN P Q R^12 ∧
    a.natAbs.primeFactors⊆mixedPlaces P Q R ∧
    IsSInteger (mixedPlaces P Q R) X ∧ IsSInteger (mixedPlaces P Q R) Y ∧
    Y^2=X^3+(a:ℚ) ∧ (P:ℚ)/R=Y^2/(a:ℚ) := by
  let S:=mixedPlaces P Q R
  let N:=mixedN P Q R
  let d:=sqfInt P
  let e:=cubePart Q
  let v:=cubeRoot Q
  let m:=cubeRoot R
  let k:=cubePart R
  obtain ⟨sd,u,_,pEq⟩:=sqfInt_spec pn
  have pE:P=d*u^2:=pEq
  have qE:Q=e*v^3:=factor_cube qn
  have rE:R=k*m^3:=factor_cube rn
  have en:e≠0:=fun z=>qn (by simp [qE,z])
  have kn:k≠0:=fun z=>rn (by simp [rE,z])
  have mn:m≠0:=fun z=>rn (by simp [rE,z])
  have dn:d≠0:=sd.ne_zero
  let L:=sqfInt m
  obtain ⟨sl,w,wn,mE⟩:=sqfInt_spec mn
  have mW:m=L*w^2:=mE
  let f:=k*L^3
  have fn:f≠0:=mul_ne_zero kn (pow_ne_zero _ sl.ne_zero)
  have rW:R=f*w^6:=by rw [rE,mW];dsimp only [f];ring
  have pr (p) (mem:p∈S):p.Prime:=mixed_prime mem
  have dp:d.natAbs.primeFactors⊆S:=Finset.subset_union_left
  have eq:surviving Q⊆S:=Finset.subset_union_left.trans Finset.subset_union_right
  have rr:R.natAbs.primeFactors⊆S:=Finset.subset_union_right.trans Finset.subset_union_right
  have kp:surviving R⊆S:=(Finset.filter_subset _ _).trans rr
  have mp:m.natAbs.primeFactors⊆S:=(prime_sub (root_dvd rn) rn).trans rr
  have lp:L.natAbs.primeFactors⊆S:=(prime_sub (show L∣m from ⟨w^2,mW⟩) mn).trans mp
  have wp:w.natAbs.primeFactors⊆S:=(prime_sub (show w∣m from ⟨L*w,by rw [mW];ring⟩) mn).trans mp
  have ep:e.natAbs.primeFactors⊆S:=(coeff_primes qn).trans eq
  have ks:k.natAbs.primeFactors⊆S:=(coeff_primes rn).trans kp
  have dd:d.natAbs≤N:=(squarecap pn).le.trans (support_mono dp pr)
  have ll:L.natAbs≤N:=(squarecap mn).le.trans (support_mono lp pr)
  have ee:e.natAbs≤N^2:=(cap_part qn).trans (Nat.pow_le_pow_left (support_mono eq pr) _)
  have kk:k.natAbs≤N^2:=(cap_part rn).trans (Nat.pow_le_pow_left (support_mono kp pr) _)
  have power (n:ℕ) (nn:n≠0) (z:ℤ) (hz:z.natAbs.primeFactors⊆S) : (z^n).natAbs.primeFactors⊆S:=by
    rw [Int.natAbs_pow,Nat.primeFactors_pow _ nn];exact hz
  let a:=d^3*e^2*f
  let X:ℚ:=((-d*e*v:ℤ):ℚ)/(w:ℚ)^2
  let Y:ℚ:=((d^2*e*u:ℤ):ℚ)/(w:ℚ)^3
  have an:a≠0:=mul_ne_zero (mul_ne_zero (pow_ne_zero _ dn) (pow_ne_zero _ en)) fn
  have fs:f.natAbs.primeFactors⊆S:=mul_support kn (pow_ne_zero _ sl.ne_zero) ks (power 3 (by decide) _ lp)
  refine ⟨a,X,Y,an,?_,mul_support (mul_ne_zero (pow_ne_zero _ dn) (pow_ne_zero _ en)) fn
    (mul_support (pow_ne_zero _ dn) (pow_ne_zero _ en) (power 3 (by decide) _ dp) (power 2 (by decide) _ ep)) fs,
    integral _ _ wn wp (by decide),integral _ _ wn wp (by decide),?_,?_⟩
  · dsimp only [a,f];simp only [Int.natAbs_mul,Int.natAbs_pow]
    calc
      _ ≤ N^3*(N^2)^2*(N^2*N^3) :=Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left dd _) (Nat.pow_le_pow_left ee _)) (Nat.mul_le_mul kk (Nat.pow_le_pow_left ll _))
      _ = _ :=by ring
  · have eqi:(d^2*e*u)^2=(-d*e*v)^3+a*w^6 :=by
      have g:d*u^2+e*v^3=f*w^6:=by rw [←pE,←qE,←rW,sum]
      dsimp only [a];linear_combination d^3*e^2*g
    have eqr:((d^2*e*u:ℤ):ℚ)^2=((-d*e*v:ℤ):ℚ)^3+(a:ℚ)*(w:ℚ)^6:=by exact_mod_cast eqi
    have wz:(w:ℚ)≠0:=by exact_mod_cast wn
    dsimp only [X,Y];rw [div_pow,div_pow,←pow_mul,←pow_mul]
    change ((d^2*e*u:ℤ):ℚ)^2/(w:ℚ)^6=((-d*e*v:ℤ):ℚ)^3/(w:ℚ)^6+(a:ℚ)
    rw [eqr,add_div];field_simp
  · change (P:ℚ)/R=(((d^2*e*u:ℤ):ℚ)/(w:ℚ)^3)^2/(a:ℚ)
    rw [pE,rW];dsimp only [a];push_cast
    field_simp [show (d:ℚ)≠0 by exact_mod_cast dn,show (e:ℚ)≠0 by exact_mod_cast en,
      show (f:ℚ)≠0 by exact_mod_cast fn,show (w:ℚ)≠0 by exact_mod_cast wn]
end
end Sun28.HeightCubics
#print axioms Sun28.HeightCubics.mixed_prime
#print axioms Sun28.HeightCubics.mixed_point
