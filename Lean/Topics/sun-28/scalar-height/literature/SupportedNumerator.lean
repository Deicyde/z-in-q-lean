import NormalizedPencil
import UnitNumerator
import SharpEstimate

/-! Strip any divisor from the reduced scalar numerator. Its height is charged
only through its prime divisors. The complementary factor is charged logarithmically. -/
namespace Sun28.ScalarPencil
open Sun28.WitnessHeight Sun28.ScalarHeight Sun28.Ordinary Sun28.FiveMarkUnits
open Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.HeightExtension Sun28.HeightBudget
open Sun28.HeightRefinement ZInQ.RouteK Height
open private numberLog_le from PellSectors
open private large_margin from BudgetSector
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 160

def NumeratorTest (x:ℚ) (u c:ℤ) : Prop :=
  x.num=u*c ∧ primeBase u≤totalRadical x ∧
    (primeBase u:ℝ)^18*(ell (totalRadical x))^4*numberLog c≤625*(totalRadical x:ℝ)^23

theorem of_numerator_split (pell:PublishedAllPell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) {x:ℚ} (nonzero:x≠0) {u c:ℤ} (test:NumeratorTest x u c) :
    logHeight₁ (beta x)≤glazerConstant24*(primeProduct (scalarPrimes x):ℝ)^24 := by
  obtain ⟨split,small,mixed⟩:=test
  let A:ℤ:=(beta x).num
  let B:ℤ:=(beta x).den
  let T:ℝ:=totalRadical x
  let P:=u.natAbs.primeFactors
  let D:ℝ:=primeProduct P
  let Z:=numberLog c
  have cn:c≠0:=by intro e;simp [e] at split; exact nonzero split
  have nn:0≤Z:=nonneg_numberLog cn
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have tp:0<T:=by linarith
  have pP (p:ℕ) (hp:p∈P):p.Prime:=Nat.prime_of_mem_primeFactors hp
  have dpos:1≤D:=Nat.one_le_cast.mpr (prime_product_pos pP)
  have dsmall:D≤T:=by dsimp only [D,T,P];exact_mod_cast small
  change D^18*(ell T)^4*Z≤625*T^23 at mixed
  obtain ⟨h,k,X,Y,V,nh,nk,gs,hs,ks,b₀,b₁,b₂,xP,yP,zP,e₁,e₂,ratio⟩:=rational_pencil nonzero split
  have pr (p:ℕ) (hp:p∈support A B):p.Prime:=support_primes hp
  obtain ⟨L,isfin,dim,sr,sw,disc⟩:=character_field (by decide:(6:ℤ)≠0) nh nk pr gs hs ks (conductor_from_characters formula)
  let _ : FiniteDimensional ℚ L:=isfin
  have CD:((NumberField.discr L).natAbs:ℝ)≤64*T^2:=by
    rw [product_support] at disc
    change ((NumberField.discr L).natAbs:ℝ)≤64*(heightRadical A B:ℝ)^2
    exact_mod_cast disc
  have ⟨cr,r,hc⟩:=class_bounds classes L dim t CD
  obtain ⟨a,pb,bq,ub,_,br,_,estimate⟩:=pell L dim P pP
  let W:=Real.log (2^32*T)
  have aw (v:ℤ) (nv:v≠0) (bound:v.natAbs≤2^32*heightRadical A B):numberLog v≤W:=by
    apply numberLog_le nv
    change (v.natAbs:ℝ)≤2^32*(heightRadical A B:ℝ)
    exact (by simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℝ)).mpr bound)
  have cc:0<c^2:=sq_pos_of_ne_zero cn
  have out:=estimate 6 h k (-4*c^2) (-6*c^2) X Y V (by decide) nh nk
    (mul_ne_zero (by decide) cc.ne') (mul_ne_zero (by decide) cc.ne') (by omega) sr sw xP yP zP e₁ e₂
    W (2*Z+6) (aw 6 (by decide) (by simpa only [show (6:ℤ).natAbs=6 by decide] using b₀))
    (aw h nh b₁) (aw k nk b₂) (shifted_log cn (-4) (by decide) (by decide))
    (shifted_log cn (-6) (by decide) (by decide))
  have capR:=(NumberField.Units.regulator_pos L).le
  have capH:=Nat.cast_nonneg (α:=ℝ) (NumberField.classNumber L)
  have reg:a.regulator≤(2^12*T*(ell T)^3)*D^2:=br.trans (mul_le_mul_of_nonneg_right cr (by positivity))
  have cost:(pellConstant (4*(P.card+1)):ℝ)≤(2:ℝ)^1310800*D^12:=by
    dsimp [D];exact_mod_cast HeightRefinement.Sharp.constant_twelve P pP
  have lo:0≤1+logStar a.regulator:=by unfold logStar;linarith only [le_max_left (1:ℝ) (Real.log a.regulator)]
  let factor:ℝ:=(pellConstant (4*(P.card+1)):ℝ)*a.primeNorm*a.regulator*(1+logStar a.regulator)
  have fp:0≤factor:=mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) ((by norm_num:(0:ℝ)≤1).trans a.one_le_primeNorm)) a.regulator_pos.le) lo
  let v:ℝ:=NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*a.logarithmQ
  have v0:0≤v:=add_nonneg capR (mul_nonneg capH bq)
  have lg2 : (1:ℝ)/2≤Real.log 2 := by
    have h:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at h;norm_num at h;linarith
  have wcap:6≤2*W:=by
    dsimp only [W];rw [Real.log_mul (by positivity) tp.ne',Real.log_pow]
    norm_num;linarith only [lg2,Real.log_nonneg t]
  change logHeight₁ X≤factor*(v+4*W+(2*Z+6)) at out
  have out':logHeight₁ X/2≤factor*(v+5*W+Z):=by
    have bound:(v+4*W+(2*Z+6))/2≤v+5*W+Z:=by linarith only [wcap,v0]
    exact (div_le_div_of_nonneg_right out (by norm_num)).trans (by rw [mul_div_assoc];exact mul_le_mul_of_nonneg_left bound fp)
  have hh:logHeight₁ X/2≤2^1310861*T^24:=HeightRefinement.Sharp.sharp_numeric t dpos dsmall nn mixed
    a.regulator_pos a.one_le_primeNorm pb bq ub r hc reg capR capH cost (by simpa only [W,factor,v] using out')
  have ht:=frac_height cn ratio
  change logHeight₁ (beta x)≤2*Z+2*logHeight₁ X+4 at ht
  have ep:1≤ell T:=by unfold ell;linarith only [Real.log_nonneg t]
  have coeff:(1:ℝ)≤D^18*(ell T)^4:=by simpa using mul_le_mul (one_le_pow₀ dpos (n:=18)) (one_le_pow₀ ep (n:=4)) (by norm_num) (by positivity)
  have zm:=mul_le_mul_of_nonneg_right coeff nn
  rw [one_mul] at zm
  have zsmall:Z≤625*T^24:=(zm.trans mixed).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ t (by decide:23≤24)) (by norm_num))
  have o:1≤T^24:=one_le_pow₀ t
  have big:(32:ℝ)≤2^1310861:=calc
    (32:ℝ)=2^5:=by norm_num
    _≤_:=pow_le_pow_right₀ (by norm_num) (by decide)
  have res:logHeight₁ (beta x)≤2^1310870*T^24:=by
    rw [show 1310870=1310861+9 by decide,pow_add]
    generalize (2:ℝ)^1310861=V at hh big ⊢
    have zz:Z≤(33*V)*T^24:=zsmall.trans (mul_le_mul_of_nonneg_right (by linarith only [big] : (625:ℝ)≤33*V) (pow_nonneg tp.le _))
    have vl:T^24≤V*T^24:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith only [big] : (1:ℝ)≤V) (pow_nonneg tp.le 24)
    rw [show V*2^9*T^24=512*(V*T^24) by ring]
    rw [mul_assoc] at zz
    generalize V*T^24=Y at hh vl zz ⊢
    linarith only [hh,ht,zz,vl,o]
  have eq:oddProduct A B=primeProduct (scalarPrimes x):=by
    dsimp only [A,B];simp only [oddProduct,oddSupport,scalar_support_exact]
  exact res.trans (eq ▸ large_margin A B)

theorem of_numerator_radical (pell:PublishedAllPell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) {x:ℚ} (nonzero:x≠0) (small:primeBase x.num≤totalRadical x) :
    logHeight₁ (beta x)≤glazerConstant24*(primeProduct (scalarPrimes x):ℝ)^24 := by
  apply of_numerator_split pell classes formula nonzero (u:=x.num) (c:=1)
  refine ⟨(mul_one _).symm,small,?_⟩
  simp only [numberLog,Int.natAbs_one,Nat.cast_one,Real.log_one,mul_zero]
  positivity
end
end Sun28.ScalarPencil
#print axioms Sun28.ScalarPencil.of_numerator_split
#print axioms Sun28.ScalarPencil.of_numerator_radical
