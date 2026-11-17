import BudgetEstimate

namespace Sun28.HeightBudget
open Sun28.HeightExtension (PublishedClassRegulator prime_product_pos class_bounds slope_from_coordinate)
open Sun28.HeightExtension.SquareSupport Sun28.HeightFibres Sun28.HeightFibres.Sharp
  Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Height
open private rational_pencil from SquareSupport
open private numberLog_le from PellSectors
noncomputable section
set_option exponentiation.threshold 160
set_option maxRecDepth 8192

private def rSBound (T D r : ℝ) := r≤(2^12*T*(ell T)^3)*D^2

private theorem recover {H X L T U : ℝ} (start:H≤2*X+2*L+96) (coordinate:X≤U*T^24)
    (logL:L≤T-1) (growth:T≤T^24) (one:1≤T^24) (product:T^24≤U*T^24) :
    H≤(U*2^10)*T^24 := by
  rw [show U*2^10*T^24=1024*(U*T^24) by ring]
  generalize hx:U*T^24=Y at coordinate product ⊢
  linarith only [start,coordinate,logL,growth,one,product]

private theorem large_margin (A B:ℤ) : (2:ℝ)^1310870*(heightRadical A B:ℝ)^24≤
    glazerConstant24*(oddProduct A B:ℝ)^24 := by
  have c : (2:ℝ)^1310870≤(4608:ℝ)^165888 := calc
    _ ≤ 2^(12*165888):=pow_le_pow_right₀ (by norm_num) (by decide)
    _ = ((2:ℝ)^12)^165888:=by rw [pow_mul]
    _ ≤ _:=pow_le_pow_left₀ (by positivity) (by norm_num) _
  have o : 0≤(oddProduct A B:ℝ)^24:=by positivity
  have cap : (2:ℝ)^1310870≤2*(4608^165888+6^100) := by
    let M:ℝ:=(4608:ℝ)^165888
    let Q:ℝ:=(6:ℝ)^100
    have m0 : 0≤M:=pow_nonneg (by norm_num) _
    have q0 : 0≤Q:=pow_nonneg (by norm_num) _
    change (2:ℝ)^1310870≤M at c
    change (2:ℝ)^1310870≤2*(M+Q)
    exact c.trans ((le_add_of_nonneg_right q0).trans (by rw [two_mul];exact le_add_of_nonneg_right (add_nonneg m0 q0)))
  have eq : glazerConstant24=2*((4608:ℝ)^165888+6^100)*(cutoffProduct:ℝ)^24+128 := by
    simp only [glazerConstant24,cutoffProduct,primeProduct,Nat.cast_prod]
  rw [heightRadical,Nat.cast_mul,mul_pow,eq,add_mul,mul_assoc]
  simpa only [mul_assoc] using (mul_le_mul_of_nonneg_right cap (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _) o)).trans
    (le_add_of_nonneg_right (mul_nonneg (by norm_num : (0:ℝ)≤128) o))

theorem unrestricted_height (pell:PublishedAllPell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (i:Fin 5) (budget:primeProduct (repeatedPrimes i A B)≤heightRadical A B) : target A B := by
  let T:ℝ:=heightRadical A B
  let P:=repeatedPrimes i A B
  let D:ℝ:=primeProduct P
  have pP (p:ℕ) (mem:p∈P):p.Prime:=Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp mem).1
  have dpos:1≤D:=Nat.one_le_cast.mpr (prime_product_pos pP)
  have dsmall:D≤T:=by dsimp only [D,T];exact_mod_cast budget
  have t:1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have tp:0<T:=by linarith
  obtain ⟨g,h,k,I,J,x,y,z,ng,nh,nk,ni,nj,ij,gs,hs,ks,cap,xP,yP,zP,e₁,e₂,ratio⟩:=rational_pencil off i
  have pr (p:ℕ) (hp:p∈support A B):p.Prime:=support_primes hp
  obtain ⟨L,isfin,dim,sr,sw,disc⟩:=character_field ng nh nk pr gs hs ks (conductor_from_characters formula)
  let _ : FiniteDimensional ℚ L:=isfin
  have CD:((NumberField.discr L).natAbs:ℝ)≤64*T^2:=by
    rw [product_support] at disc
    dsimp only [T];exact_mod_cast disc
  have ⟨cr,r,hc⟩:=class_bounds classes L dim t CD
  obtain ⟨b,pb,bq,ub,_,br,_,estimate⟩:=pell L dim P pP
  let W:=Real.log (2^32*T)
  have aw (a : ℤ) (nz:a≠0) (hs:a∈([g,h,k,I,J]:List ℤ)):numberLog a≤W:=by
    apply numberLog_le nz
    dsimp only [T];exact_mod_cast cap a hs
  have out:=estimate g h k I J x y z ng nh nk ni nj ij sr sw xP yP zP e₁ e₂ W W
    (aw g ng (by simp)) (aw h nh (by simp)) (aw k nk (by simp)) (aw I ni (by simp)) (aw J nj (by simp))
  rw [show NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*b.logarithmQ+4*W+W=NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*b.logarithmQ+5*W by ring] at out
  have reg:rSBound T D b.regulator := by
    exact br.trans (mul_le_mul_of_nonneg_right cr (by positivity))
  have bound := constant_bound P pP
  have cg : (pellConstant (4*(P.card+1)):ℝ) ≤ (2:ℝ)^1310800*D^14 := by
    dsimp [D];exact_mod_cast bound
  have hh : logHeight₁ x≤2^1310860*T^24:=budget_numeric t dpos dsmall b.regulator_pos
    b.one_le_primeNorm pb bq ub r hc reg (NumberField.Units.regulator_pos L).le (Nat.cast_nonneg _) cg
    (by simpa only [W] using out)
  have ht:=slope_from_coordinate cop off i x ratio
  change pairLogHeight A B≤2*logHeight₁ x+2*Real.log T+96 at ht
  have p24:T≤T^24:=by simpa using pow_le_pow_right₀ t (by decide:1≤24)
  have cap:pairLogHeight A B≤2^1310870*T^24 := by
    let V:ℝ:=2^1310860
    have vp:(1:ℝ)≤V:=one_le_pow₀ (by norm_num) (n:=1310860)
    have vT:T^24≤V*T^24:=by simpa only [one_mul] using mul_le_mul_of_nonneg_right vp (pow_nonneg tp.le 24)
    have unit:1≤T^24:=one_le_pow₀ t
    rw [show 1310870=1310860+10 by decide,pow_add]
    exact recover ht hh (Real.log_le_sub_one_of_pos tp) p24 unit vT
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using cap.trans (large_margin A B)

def Residual : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,625*(heightRadical A B:ℝ)^23<(ell (heightRadical A B))^4*numberLog (oldForm i A B)) →
    (∀ i,¬SparseRepeated i A B) →
    (∀ i,heightRadical A B<primeProduct (repeatedPrimes i A B)) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) → target A B

theorem original_iff_budget (units:PublishedCorollary72) (pell:PublishedAllPell)
    (classes:PublishedClassRegulator) (formula:QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ Residual := by
  classical
  constructor
  · exact fun full A B cop off _ _ _ _=>full A B cop off
  · intro remainder
    apply (original_iff_repeated units (integral_of_all pell) (finite_of_all pell) classes formula).mpr
    intro A B cop off deep sparse high
    by_cases h:∃ i,primeProduct (repeatedPrimes i A B)≤heightRadical A B
    · obtain ⟨i,hi⟩:=h;exact unrestricted_height pell classes formula cop off i hi
    · exact remainder A B cop off deep sparse (fun i=>lt_of_not_ge (fun e=>h ⟨i,e⟩)) high

end
end Sun28.HeightBudget
#print axioms Sun28.HeightBudget.unrestricted_height
#print axioms Sun28.HeightBudget.original_iff_budget
