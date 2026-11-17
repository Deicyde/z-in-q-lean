import ElementaryConvolution
import ElementaryLower

namespace Sun28.ConeEuler.Elementary
open Finset ArithmeticFunction
noncomputable section

def invPrime (q : ℕ) : ℝ := 1/(q:ℝ)
def bothWeight (q : ℕ) : ℝ := (1+chi q)/q

theorem trim_weight (f : ℕ→ℝ) {K : ℝ} (non : 0≤K)
    (bound : ∀ q : ℕ,q.Prime → f q≤K) (B n p : ℕ) :
    (∑ q∈primesUpTo n,f q)≤(∑ q∈auxPrimes B n p,f q)+K*(B+2) := by
  let S:=primesUpTo n
  let P:=auxPrimes B n p
  have sub : P⊆S:=by intro q h;obtain ⟨hp,_,hn,_⟩:=mem_auxPrimes.mp h;exact mem_primesUpTo.mpr ⟨hp,hn⟩
  have lost : S\P ⊆ insert p (range (B+1)) := by
    intro q h
    obtain ⟨hq,miss⟩:=mem_sdiff.mp h
    obtain ⟨prime,limit⟩:=mem_primesUpTo.mp hq
    by_cases e:q=p
    · simp [e]
    · have hq' : q≤B := by by_contra! too;exact miss (mem_auxPrimes.mpr ⟨prime,too,limit,e⟩)
      exact mem_insert_of_mem (mem_range.mpr (by omega))
  have card : (S\P).card≤B+2 := (card_le_card lost).trans (by simpa using card_insert_le p (range (B+1)))
  have cap : (∑ q∈ S\P,f q)≤((S\P).card:ℝ)*K := by
    simpa only [nsmul_eq_mul] using (S\P).sum_le_card_nsmul f K (fun q h=>bound q (mem_primesUpTo.mp (mem_sdiff.mp h).1).1)
  have c : ((S\P).card:ℝ)≤(B:ℝ)+2 := by exact_mod_cast card
  change (∑ q∈S,f q)≤(∑ q∈P,f q)+K*(B+2)
  linarith only [sum_sdiff (f:=f) sub,cap,mul_le_mul_of_nonneg_right c non]

theorem gaussian_prime (q : ℕ) (hq : q.Prime) : gaussian q = 1+chi q := by
  simpa [sum_range_succ] using gaussian_pow hq 1

theorem harmonic_to_logs {n : ℕ} (hn : 2≤n) :
    Real.log (Real.log n)≤(∑ q∈primesUpTo n,invPrime q)+8*squareSum ∧
    Real.log (Real.log n)≤(∑ q∈primesUpTo n,bothWeight q)+8*squareSum+Real.log (3/2) := by
  have lg : 0<Real.log n := Real.log_pos (by exact_mod_cast (show 1<n by omega))
  have hb : Real.log n≤(harmonic n:ℝ) := (Real.log_le_log (by positivity : (0:ℝ)<n)
    (show (n:ℝ)≤(n:ℝ)+1 by linarith)).trans (by simpa using log_add_one_le_harmonic n)
  have one (m : ℕ) (hm : m≠0) : oneFun m=1 := by simp [oneFun,hm]
  have ew:=finite_euler oneFun isMultiplicative_zeta.natCast
    (fun m=>by simp [oneFun];positivity) (fun q h i=>by rw [one _ (pow_ne_zero _ h.ne_zero)];linarith [Nat.cast_nonneg (α:=ℝ) i]) n
  have e1 : (harmonic n:ℝ)≤Real.exp ((∑ q∈primesUpTo n,invPrime q)+8*squareSum) := by
    rw [harmonic_eq_sum_Icc,Rat.cast_sum]
    convert! ew using 1
    · apply sum_congr rfl;intro m h
      rw [one _ (by have z:=(mem_Icc.mp h).1;omega)];simp [one_div]
    · congr 2
      apply sum_congr rfl;intro q h;rw [one _ (mem_primesUpTo.mp h).1.ne_zero];rfl
  have gw:=finite_euler gaussian gaussian_mult gaussian_nonneg (fun q h i=>(gaussian_bounds h i).2) n
  have e2 : (2/3:ℝ)*(harmonic n:ℝ)≤Real.exp ((∑ q∈primesUpTo n,bothWeight q)+8*squareSum) := by
    apply (harmonic_gaussian n).trans
    convert! gw using 2
    congr 1
    apply sum_congr rfl;intro q h;rw [gaussian_prime _ (mem_primesUpTo.mp h).1];rfl
  constructor
  · exact (Real.log_le_iff_le_exp lg).mpr (hb.trans e1)
  · apply (Real.log_le_iff_le_exp lg).mpr
    rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<3/2)]
    linarith only [hb,e2]

theorem first_order_lower {B k n p : ℕ} (hb : 2≤B) (lo : 2≤k) (hn : 2≤n) :
    (k:ℝ)*Real.log (Real.log n) - (((k:ℝ)-2)*((B:ℝ)+2+8*squareSum)
       +2*(2*((B:ℝ)+2)+8*squareSum+Real.log (3/2))) ≤
    ∑ q∈auxPrimes B n p,dimension k q/q := by
  let P:=auxPrimes B n p
  have lin : (∑ q∈P,dimension k q/q)=((k:ℝ)-2)*(∑ q∈P,invPrime q)+2*(∑ q∈P,bothWeight q) := by
    rw [mul_sum,mul_sum,←sum_add_distrib]
    apply sum_congr rfl;intro q h
    obtain ⟨pr,large,_,_⟩:=mem_auxPrimes.mp h
    have odd:=pr.eq_two_or_odd.resolve_left (by omega)
    dsimp [dimension,invPrime,bothWeight,chi]
    rw [ZMod.χ₄_nat_eq_if_mod_four]
    simp only [show q%2≠0 by omega,ite_false]
    split_ifs <;> push_cast <;> ring
  have u:=trim_weight invPrime (by norm_num : (0:ℝ)≤1) (fun q hp=>
    (div_le_one (by exact_mod_cast hp.pos)).mpr (by exact_mod_cast hp.one_lt.le)) B n p
  have v:=trim_weight bothWeight (by norm_num : (0:ℝ)≤2) (fun q hp=>by
    dsimp only [bothWeight]
    rw [←gaussian_prime q hp]
    apply (div_le_iff₀ (by exact_mod_cast hp.pos)).mpr
    have b:= (gaussian_bounds hp 1).2
    simp only [pow_one,Nat.cast_one] at b
    have qq : (1:ℝ)≤q:=by exact_mod_cast hp.one_lt.le
    linarith) B n p
  obtain ⟨a,b⟩:=harmonic_to_logs hn
  change _≤∑ q∈P,dimension k q/q
  rw [lin]
  have left:=mul_le_mul_of_nonneg_left (a.trans (add_le_add_left u _))
    (sub_nonneg.mpr (by exact_mod_cast lo) : 0≤(k:ℝ)-2)
  dsimp [P];linarith only [left,b,v]

end
end Sun28.ConeEuler.Elementary
#print axioms Sun28.ConeEuler.Elementary.trim_weight
#print axioms Sun28.ConeEuler.Elementary.gaussian_prime
#print axioms Sun28.ConeEuler.Elementary.harmonic_to_logs
#print axioms Sun28.ConeEuler.Elementary.first_order_lower
