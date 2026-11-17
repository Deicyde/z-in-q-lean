import ScalarContact
import ScalarTree

/-! From the two rational pole equations to index divisibility on Sun's fixed curve. -/
open NumberField IsDedekindDomain Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary
open scoped NumberField
namespace Sun28.ScalarHeight

def signedValue (r δ Γ : ℚ) (D : ℕ) (W : ℚ) : ℚ :=
  ((Γ/(1+(D:ℚ)*(δ*r)^2))*W)^2 * (δ*r)

theorem signedValue_display (r δ Γ : ℚ) (D : ℕ) (W : ℚ) :
    signedValue r δ Γ D W=Γ^2*(δ*r)*W^2/(1+D*(δ*r)^2)^2 := by
  unfold signedValue
  have nz : 1+(D:ℚ)*(δ*r)^2≠0 := by positivity
  field_simp [nz]

private theorem pole_square {p : ℕ} [Fact p.Prime] (big : 3<p) (M : Finset ℚ)
    (multipliers : ∀ μ∈M,padicValRat p μ=0) {a r : ℚ} (an : a≠0) (rn : r≠0)
    (odd : Odd (padicValRat p r)) (certificate : polePredicate M (a^2*r)) :
    0≤padicValRat p (a^2*r) := by
  apply polePredicate_sound big M multipliers certificate
  rw [padicValRat.mul (pow_ne_zero 2 an) rn,padicValRat.pow]
  obtain ⟨k,hk⟩ := odd
  exact ⟨padicValRat p a+k,by omega⟩

private theorem denom_ne (r : ℚ) (D : ℕ) : 1+(D:ℚ)*r^2≠0 := by positivity

theorem pole_tree_bound {p : ℕ} [Fact p.Prime] (big : 3<p) (M : Finset ℚ)
    (multipliers : ∀ μ∈M,padicValRat p μ=0) (v : AddValuation ℚ (WithTop ℤ))
    (base : ∀ {q : ℚ}, q≠0 → v q=((padicValRat p q:ℤ):WithTop ℤ))
    {r δ Γ W : ℚ} (D : ℕ) (sign : δ=1 ∨ δ= -1)
    (positive : 0<padicValRat p r) (odd : Odd (padicValRat p r))
    (gn : Γ≠0) (gu : padicValRat p Γ=0) (live : W≠0)
    (certificate : polePredicate M (signedValue r δ Γ D W)) :
    ((-(padicValRat p r):ℤ):WithTop ℤ)<v W := by
  let R:=padicValRat p r
  have rn : r≠0 := by rintro rfl; simp at positive
  have sn : δ*r≠0 := by rcases sign with rfl|rfl <;> simpa using rn
  have sv : padicValRat p (δ*r)=R := by rcases sign with rfl|rfl <;> simp [R]
  let A := Γ/(1+(D:ℚ)*(δ*r)^2)
  have an : A≠0 := div_ne_zero gn (denom_ne _ _)
  have rn' := base sn
  rw [sv] at rn'
  have dun : 0≤v (D:ℚ) := by
    rcases eq_or_ne D 0 with rfl|d
    · simp
    rw [base (by exact_mod_cast d)]
    exact WithTop.coe_le_coe.mpr (zero_le_padicValRat_of_nat (p:=p) D)
  have av : v A=0 := front_unit v positive rn' (by rw [base gn,gu];rfl) dun
  have nz : signedValue r δ Γ D W≠0 := mul_ne_zero (pow_ne_zero 2 (mul_ne_zero an live)) sn
  have b := pole_square big M multipliers (mul_ne_zero an live) sn (sv ▸ odd) certificate
  have nonneg : 0≤v (signedValue r δ Γ D W) := (base nz).symm ▸ WithTop.coe_le_coe.mpr b
  have wv := base live
  change 0≤v ((A*W)^2*(δ*r)) at nonneg
  rw [v.map_mul,v.map_pow,v.map_mul,av,zero_add,wv,rn',←WithTop.coe_nsmul,←WithTop.coe_add] at nonneg
  have z : 0≤(2:ℕ) • padicValRat p W+R := WithTop.coe_le_coe.mp nonneg
  rw [wv]
  apply WithTop.coe_lt_coe.mpr
  dsimp [R] at z
  omega

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

def pair (ρ : K) (a b : ℚ) : K := algebraMap ℚ K a+ρ*algebraMap ℚ K b

/-- The six rational entries in the paper's fixed basis, in their displayed order. -/
structure Components {ρ : K} (root : ρ^2=2) (h s : ℤ) (g : Fin 6 → ℚ) : Prop where
  first : reciprocal (h • paperGenerator root)=pair ρ (g 0) (g 1)
  middle : reciprocal ((s-1) • paperGenerator root)=pair ρ (g 2) (g 3)
  quotient : parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)=pair ρ (g 4) (g 5)

def TreeCertificate {ρ : K} (root : ρ^2=2) (h s : ℤ) (r Γ : ℚ) (D : ℕ) (M : Finset ℚ) : Prop :=
  ∃ (δ : ℚ) (g : Fin 6 → ℚ), (δ=1 ∨ δ= -1) ∧ Components root h s g ∧
    scalarTree r g≠0 ∧ polePredicate M (signedValue r δ Γ D (scalarTree r g))

def TraceCertificate {ρ : K} (root : ρ^2=2) (h s : ℤ) (r Γ : ℚ) (D : ℕ) (M : Finset ℚ) : Prop :=
  let H:=h • paperGenerator root
  let R:=(s-1) • paperGenerator root
  scalarTheta r (reciprocal H) (parameter R/parameter H) ≠ 0 ∧
    polePredicate M (scalarValue r Γ (D:ℚ) (reciprocal H) (parameter R/parameter H))

theorem tree_prime48 {p : ℕ} [Fact p.Prime] (big : 3<p) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (charts : MinimalFormalGroupTheorems p w)
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D : ℕ) (M : Finset ℚ)
    (positive : 0<padicValRat p r) (odd : Odd (padicValRat p r)) (gn : Γ≠0)
    (gu : padicValRat p Γ=0) (multipliers : ∀ μ∈M,padicValRat p μ=0)
    (certificate : TreeCertificate root h s r Γ D M) : (p:ℤ)^48 ∣ s-1 := by
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unram := sqrtTwo_unramified root v w name (by omega)
  let u := discreteOrder (w.valuation K)
  let t := u.comap (algebraMap ℚ K)
  have base {q : ℚ} (nz : q≠0) : t q=((padicValRat p q:ℤ):WithTop ℤ) := by
    change u (algebraMap ℚ K q)=_
    simpa [u,name,unram] using prime_order_rat v w nz
  obtain ⟨δ,g,sgn,c,live,accept⟩ := certificate
  have depth := pole_tree_bound big M multipliers t base D sgn positive odd gn gu live accept
  have rn : r≠0 := by rintro rfl; simp at positive
  obtain ⟨a,b,e,f⟩ := scalarTree_orders t g (base rn) positive odd depth
  have two : u (2:K)=0 := by
    have nd : ¬p∣2 := fun h => (Nat.not_lt_of_ge (Nat.le_of_dvd (by decide) h)) (by omega)
    have ht : padicValRat p (2:ℚ)=0 := by
      simpa [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd nd] using (padicValRat.of_nat (p:=p) (n:=2))
    have e : u (algebraMap ℚ K 2)=((padicValRat p 2:ℤ):WithTop ℤ) := base (q:=2) (by norm_num)
    simpa [ht,map_ofNat] using e
  have rhon : ρ≠0 := by rintro rfl; norm_num at root
  obtain ⟨i,vi⟩ := finite_order u rhon
  have eq := congrArg u root
  rw [u.map_pow,vi,two] at eq
  have twice : 2*i=0 := by exact_mod_cast eq
  have ru : u ρ=0 := by rw [vi,show i=0 by omega];rfl
  have linear {a b : ℚ} {k : WithTop ℤ} (l : k≤t a) (r' : k≤t b) : k≤u (pair ρ a b) := by
    apply u.map_le_add l
    rw [u.map_mul,ru,zero_add]
    exact r'
  have compare := formalComparison_at_prime (p:=p) (by omega) w root 1
    (completedFilteredLog_of_minimalModel (by omega) w root (minimalModelLogarithms_of_formal_group_theorems charts) 1)
    (paperGenerator root)
  have infinite (j : ℤ) (hj : j≠0) : j • paperGenerator root≠0 := by
    intro z
    have dvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr z
    rw [paperGenerator_infinite root] at dvd
    simp [hj] at dvd
  apply cyclic_scalar48 (p:=p) (by omega) u root two (paperGenerator root) infinite compare hh
  · rw [c.first]; exact linear a b
  · rw [c.quotient]; exact linear e f

theorem trace_prime48 {p : ℕ} [Fact p.Prime] (big : 3<p) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (charts : MinimalFormalGroupTheorems p w)
    {h s : ℤ} (hh : h≠0) {r Γ : ℚ} (D : ℕ) (M : Finset ℚ)
    (positive : 0<padicValRat p r) (odd : Odd (padicValRat p r)) (gn : Γ≠0)
    (gu : padicValRat p Γ=0) (multipliers : ∀ μ∈M,padicValRat p μ=0)
    (certificate : TraceCertificate root h s r Γ D M) : (p:ℤ)^48 ∣ s-1 := by
  let X:=reciprocal (h • paperGenerator root)
  let Y:=parameter ((s-1) • paperGenerator root)/parameter (h • paperGenerator root)
  obtain ⟨live,accept⟩ := certificate
  have rn : r≠0 := by rintro rfl; simp at positive
  let A := (Γ/(1+(D:ℚ)*r^2))/scalarTheta r X Y
  have an : A≠0 := div_ne_zero (div_ne_zero gn (denom_ne _ _)) live
  have beq : scalarValue r Γ (D:ℚ) X Y=A^2*r := by
    unfold scalarValue A
    have nz : scalarTheta r X Y≠0 := live
    field_simp [denom_ne r D,nz]
  have cert : polePredicate M (A^2*r) := beq ▸ accept
  have nonneg := pole_square big M multipliers an rn odd cert
  exact odd_prime_scalar48_of_formal_group_theorems (by omega) w root charts hh D positive odd gn gu live
    (beq.symm ▸ nonneg)

end Sun28.ScalarHeight
#print axioms Sun28.ScalarHeight.signedValue_display
#print axioms Sun28.ScalarHeight.pole_tree_bound
#print axioms Sun28.ScalarHeight.tree_prime48
#print axioms Sun28.ScalarHeight.trace_prime48
