import ContactHeight

namespace Sun28.HeightExtension
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Sun28.HeightFibres Sun28.HeightFibres.Sharp Height
open private numberLog_le from PellSectors
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 1500

/-- One row of the original primitive tuple. Its prime valuations can be arbitrarily large. -/
def Sparse (i : Fin 5) (A B : ℤ) : Prop :=
  (rowPrimes i A B).card≤4 ∧ primeProduct (rowPrimes i A B)≤heightRadical A B^4

theorem sparse_height (finitePell:PublishedFinitePell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (i:Fin 5) (sparse:Sparse i A B) : target A B := by
  let T:ℝ:=heightRadical A B
  let P:=rowPrimes i A B
  let D:ℝ:=primeProduct P
  have pP (p:ℕ) (mem:p∈P):p.Prime:=Nat.prime_of_mem_primeFactors mem
  have dpos:1≤D:=Nat.one_le_cast.mpr (prime_product_pos pP)
  have dsmall:D≤T^4:=by dsimp only [D,T];exact_mod_cast sparse.2
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
  obtain ⟨b,pb,bq,ub,br,pell⟩:=finitePell L dim P pP sparse.1
  let W:=Real.log (2^32*T)
  have aw (a : ℤ) (nz:a≠0) (hs:a∈([g,h,k,I,J]:List ℤ)):numberLog a≤W:=by
    apply numberLog_le nz
    dsimp only [T];exact_mod_cast cap a hs
  have out:=pell g h k I J x y z ng nh nk ni nj ij sr sw xP yP zP e₁ e₂ W W
    (aw g ng (by simp)) (aw h nh (by simp)) (aw k nk (by simp)) (aw I ni (by simp)) (aw J nj (by simp))
  rw [show NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*b.logarithmQ+4*W+W=NumberField.Units.regulator L+(NumberField.classNumber L:ℝ)*b.logarithmQ+5*W by ring] at out
  have br' : b.regulator≤(2^12*T*(ell T)^3)*(max 1 (4*Real.log D))^16:=
    br.trans (mul_le_mul_of_nonneg_right cr (by positivity))
  have nonnegative : 0≤(NumberField.classNumber L:ℝ):=Nat.cast_nonneg _
  have hh : logHeight₁ x≤2^720*T^24:=finitePell_numeric t dpos dsmall b.regulator_pos
    b.one_le_primeNorm pb bq ub r hc br' (NumberField.Units.regulator_pos L).le nonnegative
    (by simpa only [W] using out)
  have ht:=slope_from_coordinate cop off i x ratio
  change pairLogHeight A B≤2*logHeight₁ x+2*Real.log T+96 at ht
  have p24:T≤T^24:=by simpa using pow_le_pow_right₀ t (by decide:1≤24)
  have capped : pairLogHeight A B≤2^810*T^24 := by
    linarith only [ht,hh,Real.log_le_sub_one_of_pos tp,p24,one_le_pow₀ t (n:=24)]
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using capped.trans (original_margin A B)

/-- Lemma 3.5 with the class number retained implies the ordinary regulator
bound, since every number field has class number at least one. -/
theorem ordinary_regulator (published : PublishedClassRegulator) : Regulator35 := by
  intro L finite dim
  have h : (1:ℝ)≤(NumberField.classNumber L:ℝ):=Nat.one_le_cast.mpr (NumberField.classNumber_pos L)
  exact (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h (NumberField.Units.regulator_pos L).le :
    NumberField.Units.regulator L≤(NumberField.classNumber L:ℝ)*NumberField.Units.regulator L).trans
    (published L dim).2

/-- A row supported on 2,3,5,7 is covered at every positive valuation. -/
theorem smooth_row (finitePell:PublishedFinitePell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (i:Fin 5) (smooth:rowPrimes i A B⊆({2,3,5,7}:Finset ℕ)) :
    target A B := by
  let Q:Finset ℕ:={2,3,5,7}
  have inc : Q⊆oldCutoff:=by
    intro p hp
    simp [Q] at hp
    rcases hp with rfl|rfl|rfl|rfl <;> apply Finset.mem_filter.mpr <;> exact ⟨Finset.mem_range.mpr (by decide),by decide⟩
  have rad:primeProduct (rowPrimes i A B)≤heightRadical A B:=by
    rw [←product_support]
    apply support_mono (fun p hp=>Finset.mem_union_left _ (inc (smooth hp))) (fun _ hp=>support_primes hp)
  have one:1≤heightRadical A B:=Nat.mul_pos pos_cutoff (pos_odd A B)
  apply sparse_height finitePell classes formula cop off i
  exact ⟨(Finset.card_le_card smooth).trans (by decide),
    rad.trans (by simpa using pow_le_pow_right₀ one (by decide:1≤4))⟩

def LargeAndDense : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,625*(heightRadical A B:ℝ)^23<(ell (heightRadical A B))^4*numberLog (oldForm i A B)) →
    (∀ i,¬Sparse i A B) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) → target A B

theorem original_iff_large_and_dense (units:PublishedCorollary72) (integral:PublishedPell312)
    (finitePell:PublishedFinitePell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ LargeAndDense := by
  classical
  constructor
  · exact fun full A B cop off _ _ _=>full A B cop off
  · intro rem
    apply (original_iff_published_deep units integral (ordinary_regulator classes) formula).mpr
    intro A B cop off deep failed
    by_cases test:∃ i,Sparse i A B
    · obtain ⟨i,sp⟩:=test
      exact sparse_height finitePell classes formula cop off i sp
    · exact rem A B cop off deep (fun i sp=>test ⟨i,sp⟩) failed

end
end Sun28.HeightExtension
#print axioms Sun28.HeightExtension.sparse_height
#print axioms Sun28.HeightExtension.ordinary_regulator
#print axioms Sun28.HeightExtension.smooth_row
#print axioms Sun28.HeightExtension.original_iff_large_and_dense
