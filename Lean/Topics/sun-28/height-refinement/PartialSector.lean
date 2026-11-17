import PartialPencil
import PartialEstimate

namespace Sun28.HeightRefinement
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget
  Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Height
open private numberLog_le from PellSectors
open private large_margin from BudgetSector
noncomputable section
set_option exponentiation.threshold 160
set_option maxRecDepth 8192

/-- The two factors may have common prime divisors. The logarithm is taken
only on the complementary integer c, while the selected square is charged
through the radical of its root b. -/
def Admissible (i:Fin 5) (A B b c : ℤ) : Prop :=
  oldForm i A B=b^2*c ∧ primeBase b≤heightRadical A B ∧
    (primeBase b:ℝ)^20*(ell (heightRadical A B))^4*numberLog c≤625*(heightRadical A B:ℝ)^23

theorem partial_height (pell:PublishedAllPell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) {A B b c:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (i:Fin 5) (test:Admissible i A B b c) : target A B := by
  obtain ⟨split,small,mixed⟩:=test
  let T:ℝ:=heightRadical A B
  let P:=b.natAbs.primeFactors
  let D:ℝ:=primeProduct P
  let Z:=numberLog c
  have cn:c≠0:=fun z=>(off i) (by simp [split,z])
  have nn:0≤Z:=nonneg_numberLog cn
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have tp:0<T:=by linarith
  have pP (p:ℕ) (hp:p∈P):p.Prime:=Nat.prime_of_mem_primeFactors hp
  have dpos:1≤D:=Nat.one_le_cast.mpr (prime_product_pos pP)
  have dsmall:D≤T:=by dsimp only [D,T,P];exact_mod_cast small
  change D^20*(ell T)^4*Z≤625*T^23 at mixed
  obtain ⟨g,h,k,I,J,x,y,z,ng,nh,nk,ni,nj,ij,gs,hs,ks,cap,ci,cj,xP,yP,zP,e₁,e₂,ratio⟩:=partial_pencil off i split
  have pr (p:ℕ) (hp:p∈support A B):p.Prime:=support_primes hp
  obtain ⟨L,isfin,dim,sr,sw,disc⟩:=character_field ng nh nk pr gs hs ks (conductor_from_characters formula)
  let _ : FiniteDimensional ℚ L:=isfin
  have CD:((NumberField.discr L).natAbs:ℝ)≤64*T^2:=by
    rw [product_support] at disc
    dsimp only [T];exact_mod_cast disc
  have ⟨cr,r,hc⟩:=class_bounds classes L dim t CD
  obtain ⟨a,pb,bq,ub,_,br,_,estimate⟩:=pell L dim P pP
  let W:=Real.log (2^32*T)
  have aw (v : ℤ) (nz:v≠0) (hs:v∈([g,h,k]:List ℤ)):numberLog v≤W:=by
    apply numberLog_le nz
    dsimp only [T];exact_mod_cast cap v hs
  have lg2 : (1:ℝ)/2≤Real.log 2 := by
    have h:=Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<(2:ℝ)⁻¹)
    rw [Real.log_inv] at h;norm_num at h;linarith
  have wcap : 32≤2*W := by
    dsimp only [W]
    rw [Real.log_mul (by positivity) tp.ne',Real.log_pow]
    norm_num;linarith only [lg2,Real.log_nonneg t]
  have out:=estimate g h k I J x y z ng nh nk ni nj ij sr sw xP yP zP e₁ e₂ W (Z+32)
    (aw g ng (by simp)) (aw h nh (by simp)) (aw k nk (by simp)) ci cj
  have capR:= (NumberField.Units.regulator_pos L).le
  have capH:= (Nat.cast_nonneg (α:=ℝ) (NumberField.classNumber L))
  have reg:a.regulator≤(2^12*T*(ell T)^3)*D^2:=br.trans (mul_le_mul_of_nonneg_right cr (by positivity))
  have cost : (pellConstant (4*(P.card+1)):ℝ) ≤ (2:ℝ)^1310800*D^14 := by
    dsimp [D];exact_mod_cast constant_bound P pP
  have lo:0≤1+logStar a.regulator:=by unfold logStar;linarith only [le_max_left (1:ℝ) (Real.log a.regulator)]
  have kn:0≤(pellConstant (4*(P.card+1)):ℝ):=Nat.cast_nonneg _
  have pn:0≤a.primeNorm:=le_trans (by norm_num) a.one_le_primeNorm
  let factor:ℝ:=(pellConstant (4*(P.card+1)):ℝ)*a.primeNorm*a.regulator*(1+logStar a.regulator)
  have fp:0≤factor:=mul_nonneg (mul_nonneg (mul_nonneg kn pn) a.regulator_pos.le) lo
  let v:ℝ:=NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*a.logarithmQ
  change logHeight₁ x≤factor*(v+4*W+(Z+32)) at out
  have ep:1≤ell T:=by unfold ell;linarith only [Real.log_nonneg t]
  have out':logHeight₁ x/2≤factor*(v+5*W+Z):=by
    have v0:0≤v:=add_nonneg capR (mul_nonneg capH bq)
    have bound : (v+4*W+(Z+32))/2≤v+5*W+Z :=by linarith only [wcap,v0,nn]
    exact (div_le_div_of_nonneg_right out (by norm_num)).trans (by rw [mul_div_assoc];exact mul_le_mul_of_nonneg_left bound fp)
  have hh : logHeight₁ x/2≤2^1310861*T^24 := partial_numeric t dpos dsmall nn
    mixed a.regulator_pos a.one_le_primeNorm pb bq ub r hc reg capR capH cost (by simpa only [W,factor,v] using out')
  have ht:=partial_recovery cop off i x cn ratio
  change pairLogHeight A B≤2*logHeight₁ x+Real.log T+Z+96 at ht
  have coeff:(1:ℝ)≤D^20*(ell T)^4:=by simpa using mul_le_mul (one_le_pow₀ dpos (n:=20)) (one_le_pow₀ ep (n:=4)) (by norm_num) (by positivity)
  have zm:=mul_le_mul_of_nonneg_right coeff nn
  rw [one_mul] at zm
  have zsmall:Z≤625*T^24:=(zm.trans mixed).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ t (by decide:23≤24)) (by norm_num))
  have t24:T≤T^24:=by simpa using pow_le_pow_right₀ t (by decide:1≤24)
  have lg:Real.log T≤T^24:=(Real.log_le_sub_one_of_pos tp).trans ((sub_le_self T (by norm_num)).trans t24)
  have o:1≤T^24:=one_le_pow₀ t
  have big:(32:ℝ)≤2^1310861:=calc
    (32:ℝ)=2^5:=by norm_num
    _≤_:=pow_le_pow_right₀ (by norm_num) (by decide)
  have res:pairLogHeight A B≤2^1310870*T^24:=by
    rw [show 1310870=1310861+9 by decide,pow_add]
    generalize (2:ℝ)^1310861=V at hh big ⊢
    have zz:Z≤(33*V)*T^24:=zsmall.trans (mul_le_mul_of_nonneg_right (by linarith only [big] : (625:ℝ)≤33*V) (pow_nonneg tp.le _))
    have vl:T^24≤V*T^24:=by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (by linarith only [big] : (1:ℝ)≤V) (pow_nonneg tp.le 24)
    rw [show V*2^9*T^24=512*(V*T^24) by ring]
    rw [mul_assoc] at zz
    generalize V*T^24=Y at hh vl zz ⊢
    linarith only [hh,ht,zz,vl,lg,o]
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using res.trans (large_margin A B)

def Residual : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,625*(heightRadical A B:ℝ)^23<(ell (heightRadical A B))^4*numberLog (oldForm i A B)) →
    (∀ i,¬SparseRepeated i A B) →
    (∀ i,heightRadical A B<primeProduct (repeatedPrimes i A B)) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬Admissible i A B b c) → target A B

theorem original_iff_partial (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ Residual := by
  classical
  constructor
  · exact fun full A B cop off _ _ _ _ _=>full A B cop off
  · intro rem;apply (original_iff_budget units pell classes formula).mpr
    intro A B cop off deep sparse high fails
    by_cases good:∃ i b c,Admissible i A B b c
    · obtain ⟨i,b,c,h⟩:=good;exact partial_height pell classes formula cop off i h
    · exact rem A B cop off deep sparse high fails (fun i b c h=>good ⟨i,b,c,h⟩)

end
end Sun28.HeightRefinement
#print axioms Sun28.HeightRefinement.partial_height
#print axioms Sun28.HeightRefinement.original_iff_partial
