import Extension

/-! Only repeated prime factors enter the simultaneous-Pell denominators. -/
namespace Sun28.HeightExtension.SquareSupport
open Sun28.HeightExtension Sun28.HeightFibres Sun28.HeightFibres.Sharp Sun28.Ordinary
  Sun28.FiveMarkUnits Sun28.MinimalConductors ZInQ.RouteK Height
open private leftRow midRow rightRow mult catalogue delta₁ delta₂ equation_rows from FivePencils
open private numberLog_le from PellSectors
noncomputable section
set_option maxRecDepth 8192
set_option exponentiation.threshold 1500

def repeatedPrimes (i : Fin 5) (A B : ℤ) : Finset ℕ :=
  (rowPrimes i A B).filter fun p => p^2 ∣ (oldForm i A B).natAbs

def SparseRepeated (i : Fin 5) (A B : ℤ) : Prop :=
  (repeatedPrimes i A B).card≤4 ∧ primeProduct (repeatedPrimes i A B)≤heightRadical A B^4

/-- A reduced denominator of a/v divides v. Its prime divisors therefore occur
at least twice in the selected nonzero form, even if a/v admits cancellation. -/
theorem fraction_primes {i : Fin 5} {A B c v a : ℤ}
    (fv : oldForm i A B=c*v^2) (live : oldForm i A B≠0) :
    (((a:ℚ)/(v:ℚ)).den).primeFactors⊆repeatedPrimes i A B := by
  intro p hp
  have rel : ((((a:ℚ)/(v:ℚ)).den:ℕ):ℤ)∣v := by
    simpa only [←Rat.divInt_eq_div] using Rat.den_dvd a v
  have dv : ((a:ℚ)/(v:ℚ)).den∣v.natAbs := Int.natAbs_dvd_natAbs.mpr rel
  have pv : p∣v.natAbs := (Nat.dvd_of_mem_primeFactors hp).trans dv
  have ps : p^2∣(oldForm i A B).natAbs := by
    rw [fv,Int.natAbs_mul,Int.natAbs_pow]
    exact (pow_dvd_pow_of_dvd pv 2).trans (dvd_mul_left _ _)
  have pf : p∣(oldForm i A B).natAbs := (dvd_pow_self _ two_ne_zero).trans ps
  exact Finset.mem_filter.mpr ⟨Nat.mem_primeFactors.mpr
    ⟨Nat.prime_of_mem_primeFactors hp,pf,Int.natAbs_ne_zero.mpr live⟩,ps⟩

/-- Three rationals with the same explicit denominator repack the two equations.
The remaining right sides are the signed squarefree part of the selected row,
multiplied by fixed determinants. -/
private theorem rational_pencil {A B : ℤ} (off : ∀ i,oldForm i A B≠0) (i : Fin 5) :
    ∃ (g h k I J : ℤ) (x y z : ℚ),
      g≠0 ∧ h≠0 ∧ k≠0 ∧ I≠0 ∧ J≠0 ∧ I≠J ∧
      g.natAbs.primeFactors⊆support A B ∧ h.natAbs.primeFactors⊆support A B ∧ k.natAbs.primeFactors⊆support A B ∧
      (∀ c∈([g,h,k,I,J]:List ℤ),c.natAbs≤2^32*heightRadical A B) ∧
      x.den.primeFactors⊆repeatedPrimes i A B ∧ y.den.primeFactors⊆repeatedPrimes i A B ∧ z.den.primeFactors⊆repeatedPrimes i A B ∧
      (g:ℚ)*x^2-(h:ℚ)*y^2=(I:ℚ) ∧ (g:ℚ)*x^2-(k:ℚ)*z^2=(J:ℚ) ∧
      (oldForm (leftRow i) A B:ℚ)/(oldForm i A B:ℚ)=
        (kernel (leftRow i) A B:ℚ)/(kernel i A B:ℚ)*x^2 := by
  let l:=leftRow i;let m:=midRow i;let n:=rightRow i
  obtain ⟨_,a,_,fa⟩:=sqfInt_spec (off l)
  obtain ⟨_,b,_,fb⟩:=sqfInt_spec (off m)
  obtain ⟨_,c,_,fc⟩:=sqfInt_spec (off n)
  obtain ⟨_,v,nv,fv⟩:=sqfInt_spec (off i)
  change oldForm l A B=kernel l A B*a^2 at fa
  change oldForm m A B=kernel m A B*b^2 at fb
  change oldForm n A B=kernel n A B*c^2 at fc
  change oldForm i A B=kernel i A B*v^2 at fv
  obtain ⟨mu,nd,ne,de,bd,be⟩:=catalogue i
  have nz (r : Fin 5):kernel r A B≠0 := (sqfInt_spec (off r)).1.ne_zero
  let G (j:Fin 3) (r:Fin 5):=mult i j*kernel r A B
  have live (j r) : G j r≠0:=mul_ne_zero (mu j).1 (nz r)
  have cap {d:ℤ} (hd:d.natAbs≤2^32) (r:Fin 5) :
      (d*kernel r A B).natAbs≤2^32*heightRadical A B := by
    rw [Int.natAbs_mul];exact Nat.mul_le_mul hd (kernel_bound off r)
  have ps (a:ℤ) : (((a:ℚ)/(v:ℚ)).den).primeFactors⊆repeatedPrimes i A B :=
    fraction_primes fv (off i)
  obtain ⟨e₁,e₂⟩:=equation_rows i A B
  change mult i 0*oldForm l A B-mult i 1*oldForm m A B=delta₁ i*oldForm i A B at e₁
  change mult i 0*oldForm l A B-mult i 2*oldForm n A B=delta₂ i*oldForm i A B at e₂
  rw [fa,fb,fv] at e₁;rw [fa,fc,fv] at e₂
  have qnv:(v:ℚ)≠0:=by exact_mod_cast nv
  have cast₁:=congrArg (fun u:ℤ=>(u:ℚ)) e₁
  have cast₂:=congrArg (fun u:ℤ=>(u:ℚ)) e₂
  push_cast at cast₁ cast₂
  refine ⟨G 0 l,G 1 m,G 2 n,delta₁ i*kernel i A B,delta₂ i*kernel i A B,
    (a:ℚ)/v,(b:ℚ)/v,(c:ℚ)/v,live 0 l,live 1 m,live 2 n,mul_ne_zero nd (nz i),
    mul_ne_zero ne (nz i),fun e=>de (mul_right_cancel₀ (nz i) e),
    scaled_support off i 0 l,scaled_support off i 1 m,scaled_support off i 2 n,?_,
    ps a,ps b,ps c,?_,?_,?_⟩
  · intro w hw;simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl
    exacts [cap (mu 0).2 l,cap (mu 1).2 m,cap (mu 2).2 n,cap bd i,cap be i]
  · dsimp [G];push_cast;field_simp;linear_combination cast₁
  · dsimp [G];push_cast;field_simp;linear_combination cast₂
  · rw [fa,fv];push_cast;ring

theorem repeated_height (finitePell:PublishedFinitePell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) {A B:ℤ} (cop:Int.gcd A B=1)
    (off:∀ i,oldForm i A B≠0) (i:Fin 5) (sparse:SparseRepeated i A B) : target A B := by
  let T:ℝ:=heightRadical A B
  let P:=repeatedPrimes i A B
  let D:ℝ:=primeProduct P
  have pP (p:ℕ) (mem:p∈P):p.Prime:=Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp mem).1
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


def RepeatedResidual : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,625*(heightRadical A B:ℝ)^23<(ell (heightRadical A B))^4*numberLog (oldForm i A B)) →
    (∀ i,¬SparseRepeated i A B) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) → target A B

theorem original_iff_repeated (units:PublishedCorollary72) (integral:PublishedPell312)
    (finitePell:PublishedFinitePell) (classes:PublishedClassRegulator)
    (formula:QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ RepeatedResidual := by
  classical
  constructor
  · exact fun full A B cop off _ _ _=>full A B cop off
  · intro rem
    apply (original_iff_published_deep units integral (ordinary_regulator classes) formula).mpr
    intro A B cop off deep failed
    by_cases test:∃ i,SparseRepeated i A B
    · obtain ⟨i,sp⟩:=test
      exact repeated_height finitePell classes formula cop off i sp
    · exact rem A B cop off deep (fun i sp=>test ⟨i,sp⟩) failed


theorem sparse_implies_repeated {A B : ℤ} (i : Fin 5) (old : Sparse i A B) : SparseRepeated i A B := by
  have sub : repeatedPrimes i A B ⊆ rowPrimes i A B := Finset.filter_subset _ _
  exact ⟨(Finset.card_le_card sub).trans old.1,
    (support_mono sub (fun _ hp=>Nat.prime_of_mem_primeFactors hp)).trans old.2⟩

end
end Sun28.HeightExtension.SquareSupport
#print axioms Sun28.HeightExtension.SquareSupport.fraction_primes
#print axioms Sun28.HeightExtension.SquareSupport.repeated_height
#print axioms Sun28.HeightExtension.SquareSupport.original_iff_repeated
#print axioms Sun28.HeightExtension.SquareSupport.sparse_implies_repeated
