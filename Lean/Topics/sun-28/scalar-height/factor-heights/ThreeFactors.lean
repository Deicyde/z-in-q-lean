import ScalarKernels
import SignedSupport

namespace Sun28.FactorHeights
open Sun28.ScalarQuotients Sun28.WitnessHeight ZInQ.RouteK
open private kernel_member from SignedSupport
noncomputable section

def alpha : Fin 4→ℤ := ![2,1,1,64]
def gamma : Fin 4→ℤ := ![3,1,-1199,439]
def base (i:Fin 4) : ℕ := ![14,30,210,210] i

def row (i:Fin 4) (a b:ℤ):ℤ := alpha i*a^2+gamma i*b^2
def value (i:Fin 4) (x:ℚ) :ℤ:=row i x.num x.den
def coeff (i:Fin 4) (x:ℚ):ℤ:=sqfInt (value i x)

/-- The quadratic factors carrying every large odd valuation form at most one row. -/
def concentrated (x:ℚ) (i:Fin 4):Prop :=
  ∀p:ℕ,p.Prime → ¬p∣210 → p∣(scalarClass x).natAbs → (p:ℤ)∣value i x

theorem literal_product (a b:ℤ) : (∏i:Fin 4,row i a b)=homogenized a b := by
  rw [Fin.prod_univ_four]
  change (2*a^2+3*b^2)*(1*a^2+1*b^2)*(1*a^2+(-1199)*b^2)*(64*a^2+439*b^2)=_
  unfold homogenized;ring

theorem row_ne (x:ℚ) (i:Fin 4): value i x≠0 := by
  obtain ⟨sf,y,yn,h⟩:=octic_twist x
  obtain ⟨u,eu⟩:=integral_point sf yn h
  have en:homogenized x.num (x.den:ℤ)≠0:=by
    have bn:(x.den:ℚ)≠0:=by exact_mod_cast x.den_nz
    have num: (x.num:ℚ)=x*x.den:=(div_eq_iff bn).mp x.num_div_den
    have e:((homogenized x.num (x.den:ℤ):ℤ):ℚ)=octic x*(x.den:ℚ)^8:=by
      dsimp [homogenized,octic];push_cast;rw [num];ring
    intro z;rw [z,Int.cast_zero,h] at e
    exact (mul_ne_zero (mul_ne_zero (by exact_mod_cast sf.ne_zero) (pow_ne_zero _ yn)) (pow_ne_zero _ bn)) e.symm
  rw [←literal_product] at en
  exact Finset.prod_ne_zero_iff.mp en _ (Finset.mem_univ _)

private theorem det_bound : ∀(i j:Fin 4), i≠j →
    (alpha i*gamma j-gamma i*alpha j).natAbs∣base i^4 := by decide

theorem common_row_prime {x:ℚ} {i j:Fin 4} (ij:i≠j) {p:ℕ} (pp:p.Prime)
    (a:(p:ℤ)∣value i x) (b:(p:ℤ)∣value j x) : p∣base i := by
  have pd:=prime_divides_determinant pp (show x.num.natAbs.Coprime (x.den:ℤ).natAbs by simpa using x.reduced) a b
  have dv:p∣(alpha i*gamma j-gamma i*alpha j).natAbs:=by simpa using Int.natAbs_dvd_natAbs.mpr pd
  exact pp.dvd_of_dvd_pow (dv.trans (det_bound i j ij))

theorem coeff_dvd_value (x:ℚ) (i:Fin 4):coeff i x∣value i x := by
  obtain ⟨_,u,_,e⟩:=sqfInt_spec (row_ne x i)
  exact ⟨u^2,e⟩

/-- A prime occurring in a row kernel is either common to two binary forms
or occurs in the signed octic squareclass. -/
theorem row_support {x:ℚ} (i:Fin 4) {p:ℕ} (pp:p.Prime) (pk:p∣(coeff i x).natAbs) :
    p∣base i ∨ p∣(scalarClass x).natAbs := by
  have sf:Squarefree (coeff i x):=(sqfInt_spec (row_ne x i)).1
  have pk':(p:ℤ)∣coeff i x:=Int.natAbs_dvd_natAbs.mp (by simpa using pk)
  have pv:=pk'.trans (coeff_dvd_value x i)
  by_cases coll:∃j:Fin 4,j≠i ∧ (p:ℤ)∣value j x
  · obtain ⟨j,ne,pd⟩:=coll;exact Or.inl (common_row_prime ne.symm pp pv pd)
  right
  obtain ⟨s,y,yn,h⟩:=octic_twist x
  obtain ⟨u,eu⟩:=integral_point s yn h
  have had:=row_ne x
  have total:(∏j:Fin 4,value j x)=scalarClass x*u^2:=(literal_product ..).trans eu
  have tn:scalarClass x*u^2≠0 := total ▸ Finset.prod_ne_zero_iff.mpr (fun j _=>had j)
  have un:u≠0:=by intro eq;simp [eq] at tn
  have ss:sqfInt (∏j:Fin 4,value j x)=scalarClass x:=by
    exact (sqf_intCast _).symm.trans (sqf_eq_of_eq_mul_sq s (by exact_mod_cast un : (u:ℚ)≠0)
      (show ((∏j:Fin 4,value j x:ℤ):ℚ)=(scalarClass x:ℚ)*(u:ℚ)^2 by exact_mod_cast total))
  have ip:(p:ℤ)∣value i x:=pv
  let _:Fact p.Prime:=⟨pp⟩
  have odd:Odd (padicValInt p (value i x)):=(kernel_member (had i) pp).mp
    (Nat.mem_primeFactors.mpr ⟨pp,pk,Int.natAbs_ne_zero.mpr sf.ne_zero⟩)
  have zero:∀j:Fin 4,j≠i → padicValInt p (value j x)=0:=by
    intro j ne
    apply padicValNat.eq_zero_of_not_dvd
    intro dv
    exact coll ⟨j,ne,Int.natAbs_dvd_natAbs.mp (by simpa using dv)⟩
  have prod (S:Finset (Fin 4)) : padicValInt p (∏j∈S,value j x)=∑j∈S,padicValInt p (value j x) := by
    induction S using Finset.induction_on with
    | empty=>simp [padicValInt]
    | @insert a t ha ih=>
      rw [Finset.prod_insert ha,Finset.sum_insert ha,padicValInt,Int.natAbs_mul,
        padicValNat.mul (Int.natAbs_ne_zero.mpr (had a)) (Int.natAbs_ne_zero.mpr
          (Finset.prod_ne_zero_iff.mpr (fun j _=>had j)))]
      exact congrArg (fun z=>padicValInt p (value a x)+z) ih
  have ot:Odd (padicValInt p (∏j:Fin 4,value j x)):=by
    rw [prod,Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun j _ ne=>zero j ne)]
    exact odd
  have hh:=(kernel_member (show (∏j:Fin 4,value j x)≠0 from total.symm ▸ tn) pp).mpr ot
  rw [ss] at hh
  exact Nat.dvd_of_mem_primeFactors hh

theorem concentrated_divisors {x:ℚ} {i:Fin 4} (h:concentrated x i) {j:Fin 4} (ji:j≠i) :
    (coeff j x).natAbs ∣ 210 := by
  have sf:Squarefree (coeff j x).natAbs:=Int.squarefree_natAbs.mpr (sqfInt_spec (row_ne x j)).1
  rw [←Nat.prod_primeFactors_of_squarefree sf,Nat.prod_primeFactors_dvd_iff (by decide:210≠0)]
  intro p hp
  have pp:=Nat.prime_of_mem_primeFactors hp
  have pk:=Nat.dvd_of_mem_primeFactors hp
  apply Nat.mem_primeFactors.mpr
  refine ⟨pp,?_,by decide⟩
  have small:base j∣210:=by fin_cases j <;> decide
  rcases row_support j pp pk with q|q
  · exact q.trans small
  by_contra ps
  have pk':(p:ℤ)∣coeff j x:=Int.natAbs_dvd_natAbs.mp (by simpa using pk)
  exact ps ((common_row_prime ji pp (pk'.trans (coeff_dvd_value x j)) (h p pp ps q)).trans small)

end
end Sun28.FactorHeights
#print axioms Sun28.FactorHeights.literal_product
#print axioms Sun28.FactorHeights.row_ne
#print axioms Sun28.FactorHeights.common_row_prime
#print axioms Sun28.FactorHeights.coeff_dvd_value
#print axioms Sun28.FactorHeights.row_support
#print axioms Sun28.FactorHeights.concentrated_divisors
