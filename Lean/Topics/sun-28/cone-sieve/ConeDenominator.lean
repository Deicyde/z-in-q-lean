import ConeBound

namespace Sun28.ConeSieve
open Finset
noncomputable section
open scoped Classical

/-- The logarithmic size of the squarefree product of the selected primes. -/
def logSize (r : Finset ℕ) := ∑ p∈r, Real.log p

theorem mean_log (P : Finset ℕ) (g : ℕ → ℝ) (lt : ∀ p∈P,g p<1) :
    (∑ r ∈ P.powerset, (∏ p∈r,odds g p)*logSize r) =
    (∏ p∈P,(1+odds g p))*(∑ p∈P,g p*Real.log p) := by
  classical
  have term (p : ℕ) (hp : p∈P) :
      (∑ r∈P.powerset, (∏ q∈r,odds g q)*indicator (p∈r)) = (∏ q∈P,(1+odds g q))*g p := by
    have h (r : Finset ℕ) (hr : r∈P.powerset) :
        (∏ q∈r,odds g q) = (∏ q∈P,(1+odds g q))*probability P g r := by
      have sub:=mem_powerset.mp hr
      have nz (q : ℕ) (hq : q∈P) : 1-g q≠0 := ne_of_gt (sub_pos.mpr (lt q hq))
      have e (q : ℕ) (hq : q∈P) : (1+odds g q)*(1-g q)=1 := by dsimp [odds];field_simp [nz q hq];ring
      have e' (q : ℕ) (hq : q∈P) : (1+odds g q)*g q=odds g q := by dsimp [odds];field_simp [nz q hq];ring
      unfold probability
      rw [←prod_sdiff sub (f:=fun q=>1+odds g q)]
      rw [show ∀ a b c d:ℝ,(a*b)*(c*d)=(b*c)*(a*d) from fun _ _ _ _=>by ring,
        ←prod_mul_distrib,←prod_mul_distrib]
      have unit : (∏ q∈P\r,(1+odds g q)*(1-g q))=1 := prod_eq_one (fun q hq=>e q (mem_sdiff.mp hq).1)
      rw [unit,mul_one]
      exact prod_congr rfl (fun q hq=>(e' q (sub hq)).symm)
    calc
      _ = (∏ q∈P,(1+odds g q))*∑ r∈P.powerset,probability P g r*indicator ({p}⊆r) := by
        rw [mul_sum];apply sum_congr rfl;intro r hr;rw [h r hr];simp [mul_assoc]
      _ = _ := by rw [model_flag P {p} g (by simpa using hp)];simp
  have rewriteLog (r : Finset ℕ) (hr : r∈P.powerset) :
      logSize r=∑ p∈P,indicator (p∈r)*Real.log p := by
    have cut : P.filter (fun p=>p∈r)=r := by
      ext q;simp;exact fun h=>mem_powerset.mp hr h
    simp only [indicator,ite_mul,one_mul,zero_mul,←sum_filter,cut,logSize]
  calc
    _ = ∑ r∈P.powerset, ∑ p∈P,((∏ q∈r,odds g q)*indicator (p∈r))*Real.log p := by
      apply sum_congr rfl;intro r hr;rw [rewriteLog r hr,mul_sum]; apply sum_congr rfl;intro _ _;ring
    _ = _ := by
      rw [sum_comm,mul_sum];apply sum_congr rfl;intro p hp;rw [←sum_mul,term p hp];ring

/-- Truncating the Euler product at z retains at least half its mass if its mean
logarithm is at most half log z. The omitted collision prime can be absent from P. -/
theorem half_euler_product (P : Finset ℕ) (g : ℕ → ℝ) (z : ℕ) (hz : 1<z)
    (pr : ∀ p∈P,p.Prime) (bd : ∀ p∈P,0≤g p ∧ g p<1)
    (mean : 2*∑ p∈P,g p*Real.log p ≤ Real.log z) :
    (∏ p∈P,(1+odds g p))≤2*denominator g (index P z) := by
  classical
  let M:=fun r : Finset ℕ => ∏ p∈r,odds g p
  let L:=Real.log (z:ℝ)
  let full:=∏ p∈P,(1+odds g p)
  have lp : 0<L := Real.log_pos (by exact_mod_cast hz)
  have unr {r : Finset ℕ} (hr : r∈P.powerset) : 0≤M r := prod_nonneg
    (fun p hp=> div_nonneg (bd p (mem_powerset.mp hr hp)).1 (sub_nonneg.mpr (bd p (mem_powerset.mp hr hp)).2.le))
  have size {r : Finset ℕ} (hr : r∈P.powerset) :
      Real.log ((∏ p∈r,p : ℕ):ℝ) = logSize r := by
    unfold logSize;push_cast;apply Real.log_prod;intro p hp;exact_mod_cast (pr p (mem_powerset.mp hr hp)).ne_zero
  have point (r : Finset ℕ) (hr : r∈P.powerset) : L*M r ≤
      M r * logSize r + (if (∏ p∈r,p)≤z then L*M r else 0) := by
    by_cases small : (∏ p∈r,p)≤z
    · simp only [small,ite_true]
      apply le_add_of_nonneg_left;apply mul_nonneg (unr hr)
      apply sum_nonneg;intro p hp;exact Real.log_nonneg (by exact_mod_cast (pr p (mem_powerset.mp hr hp)).one_lt.le)
    · simp only [small,ite_false,add_zero]
      rw [mul_comm (M r),←size hr]
      exact mul_le_mul_of_nonneg_right (Real.log_le_log (by positivity) (by exact_mod_cast (Nat.le_of_not_ge small))) (unr hr)
  have result:=sum_le_sum point
  rw [←mul_sum,sum_add_distrib,←sum_filter,←mul_sum] at result
  have fullE : (∑ r∈P.powerset,M r)=full := (prod_one_add P).symm
  rw [fullE] at result
  have moment:=mean_log P g (fun p hp=>(bd p hp).2)
  change _ ≤ (∑ r∈P.powerset,(∏ p∈r,odds g p)*logSize r)+L*denominator g (index P z) at result
  rw [moment] at result
  have posfull:0≤full := fullE ▸ sum_nonneg (fun r hr=>unr hr)
  have budget:=mul_le_mul_of_nonneg_left mean posfull
  change _ ≤ full*_+_ at result
  change _ ≤ full*L at budget
  apply (le_of_mul_le_mul_left _ lp : full≤2*denominator g (index P z))
  nlinarith only [result,budget]

end
end Sun28.ConeSieve
#print axioms Sun28.ConeSieve.mean_log
#print axioms Sun28.ConeSieve.half_euler_product
