import ScalarHeight
import OrdinaryChart

/-! One completed formal chart for both the ordinary and scalar comparisons. -/
open NumberField IsDedekindDomain Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Height Filter Topology
open scoped NumberField
namespace Sun28.ScalarHeight
variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

omit [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K] in
private theorem series_isometry {p : ℕ} [Fact p.Prime] (large : 65<p)
    (w : HeightOneSpectrum (𝓞 K)) {b z A : w.adicCompletion K}
    (int : ∀ n : ℕ, n≠0 → completionOrder w (n:w.adicCompletion K)=((padicValNat p n:ℤ):WithTop ℤ))
    (bi : 0≤completionOrder w b) (formal : (1:WithTop ℤ)≤completionOrder w z)
    (limit : Tendsto (fun n => logTrunc (shortDifferential b) n z) atTop (𝓝 A)) :
    completionOrder w A=completionOrder w z := by
  rcases eq_or_ne z 0 with rfl|nz
  · have same : Tendsto (fun n : ℕ => (0:w.adicCompletion K)) atTop (𝓝 A) := by simpa [logTrunc_zero] using limit
    have zero : (0:w.adicCompletion K)=A := tendsto_nhds_unique tendsto_const_nhds same
    rw [←zero]
  obtain ⟨d,vd⟩ := finite_order (completionOrder w) nz
  have pos : 0<d := by
    rw [vd] at formal
    exact WithTop.coe_lt_coe.mp (lt_of_lt_of_le (by decide : (0:WithTop ℤ)<1) formal)
  have tail := log_trunc_error w (k:=1) (p:=p) (by omega) _ (shortDifferential_integral _ bi) int pos vd limit
  have first : logTrunc (shortDifferential b) 1 z=z := by simp [logTrunc,shortDifferential]
  rw [first] at tail
  have swapped := (completionOrder w).map_sub_swap z A
  rw [vd]
  exact trunc_order _ vd (k:=1) (by decide) (swapped.symm ▸ tail)

theorem goodModel_of_ordinary_chart {p : ℕ} [Fact p.Prime] (large : 65<p) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (chart : OrdinaryFormalChart p w) : GoodModelLogarithms p w := by
  classical
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩
  have name : (Rat.HeightOneSpectrum.primesEquiv v).1=p :=
    congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).apply_symm_apply ⟨p,Fact.out⟩)
  have unram := sqrtTwo_unramified root v w name (by omega)
  have integer (n : ℕ) (nz : n≠0) : completionOrder w (n:w.adicCompletion K)=((padicValNat p n:ℤ):WithTop ℤ) := by
    have eq := prime_order_rat v w (q:=(n:ℚ)) (by exact_mod_cast nz)
    rw [←map_natCast (algebraMap K (w.adicCompletion K)),completionOrder_algebraMap]
    simpa [name,unram,padicValRat.of_nat] using eq
  intro b _ normalized integral good
  obtain ⟨T,A,series⟩ := ordinaryLogarithms_of_chart w chart b large normalized integral good
  refine ⟨{ kernel:=T.kernel, formal:=T.membership, log:=A.comp T.chart.toAddMonoidHom, level:=?_ }⟩
  intro Q r _
  change _ ≤ completionOrder w (A (T.chart Q)) ↔ _
  rw [series_isometry large w integer integral (by simpa using T.integral (T.chart Q)) (series (T.chart Q)),T.chart_parameter]

theorem tree_prime48_of_ordinary_chart {p : ℕ} [Fact p.Prime] (big : 65<p) (w : HeightOneSpectrum (𝓞 K))
    [w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,Fact.out⟩).asIdeal]
    {ρ : K} (root : ρ^2=2) (chart : OrdinaryFormalChart p w)
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
  have depth := pole_tree_bound (by omega) M multipliers t base D sgn positive odd gn gu live accept
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
    (completedFilteredLog_of_goodModel (by omega) (by omega) w root (goodModel_of_ordinary_chart big w root chart) 1)
    (paperGenerator root)
  have infinite (j : ℤ) (hj : j≠0) : j • paperGenerator root≠0 := by
    intro z
    have dvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr z
    rw [paperGenerator_infinite root] at dvd
    simp [hj] at dvd
  apply cyclic_scalar48 (p:=p) (by omega) u root two (paperGenerator root) infinite compare hh
  · rw [c.first]; exact linear a b
  · rw [c.quotient]; exact linear e f

def OrdinaryCharts (S : Finset ℕ) (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ (p : ℕ) [hp : Fact p.Prime], p∉S → ∀ (w : HeightOneSpectrum (𝓞 K)),
    w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal →
    OrdinaryFormalChart p w

theorem scalar_product48_at_cutoff {ρ : K} (root : ρ^2=2) (h s : ℤ) (x Γ : ℚ) (D : ℕ) (M : Finset ℚ)
    (E : Finset ℕ) (enlarged : exceptional Γ M ⊆ E)
    (hh : h≠0) (gn : Γ≠0) (classicalInputs : OrdinaryCharts E K)
    (accept : TreeCertificate root h s (scalarRadicand (beta x)) Γ D M) :
    ((oldRadical E (beta x):ℤ)^48) ∣ s-1 := by
  unfold oldRadical
  rw [Nat.cast_prod]
  apply product_prime_powers (fun p mem => (mem_oldContactPrimes.mp mem).1)
  intro p mem
  obtain ⟨prime,away,_⟩ := mem_oldContactPrimes.mp mem
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨big,gu,multipliers⟩ := exceptional_outside (fun h => away (enlarged h))
  obtain ⟨pos,odd⟩ := old_scalar_contact big x _ mem
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,prime⟩
  obtain ⟨P,maximal,lie⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=𝓞 K) v.asIdeal
  let w : HeightOneSpectrum (𝓞 K) := ⟨P,maximal.isPrime,Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨maximal.isPrime,lie⟩⟩
  let : w.asIdeal.LiesOver v.asIdeal := lie
  have charts := classicalInputs p away w lie
  exact tree_prime48_of_ordinary_chart (by omega) w root charts hh D M pos odd gn gu multipliers accept

theorem scalar_sqrt_height_at_cutoff {ρ : K} (root : ρ^2=2) (h s : ℤ) (x Γ : ℚ) (D : ℕ) (M : Finset ℚ)
    (E : Finset ℕ) (enlarged : exceptional Γ M ⊆ E)
    (hh : h≠0) (gn : Γ≠0) (classicalInputs : OrdinaryCharts E K)
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff)
    (guard : (s-1) • paperGenerator root≠0)
    (accept : TreeCertificate root h s (scalarRadicand (beta x)) Γ D M) :
    logHeight₁ (beta x) ≤ (glazerConstant24*(∏ p ∈ extraPrimes oldCutoff E,(p:ℝ))^24)*Real.sqrt |((s-1:ℤ):ℝ)| := by
  let t:=beta x
  have nz : s-1≠0 := fun z => guard (by rw [z,zero_zsmul])
  have dv := scalar_product48_at_cutoff root h s x Γ D M E enlarged hh gn classicalInputs accept
  have bound := sqrt_of_power_dvd nz dv
  have original := upstream t.num t.den (beta_primitive x) (beta_off_forms x)
  change pairLogHeight t.num t.den≤_ at original
  have source : logHeight₁ t=pairLogHeight t.num t.den := by
    rw [Rat.logHeight₁_eq_log_max]
    unfold pairLogHeight pairHeight
    congr 1
    norm_cast
    simp
  have orig : logHeight₁ t≤glazerConstant24*(oldRadical oldCutoff t:ℝ)^24 := by
    rw [source]
    simpa only [oldRadical,Nat.cast_prod] using original
  have ex : (oldRadical oldCutoff t:ℝ)≤(∏ p ∈ extraPrimes oldCutoff E,(p:ℝ))*(oldRadical E t:ℝ) := by
    rw [←Nat.cast_prod]
    exact_mod_cast old_radical_enlargement oldCutoff E t
  have lift := pow_le_pow_left₀ (by positivity : 0≤(oldRadical oldCutoff t:ℝ)) ex 24
  rw [mul_pow] at lift
  have cpos : 0≤glazerConstant24 := by unfold glazerConstant24; positivity
  calc
    logHeight₁ (beta x) ≤ glazerConstant24*(oldRadical oldCutoff t:ℝ)^24 := orig
    _ ≤ glazerConstant24*((∏ p ∈ extraPrimes oldCutoff E,(p:ℝ))^24*(oldRadical E t:ℝ)^24) :=
      mul_le_mul_of_nonneg_left lift cpos
    _ = (glazerConstant24*(∏ p ∈ extraPrimes oldCutoff E,(p:ℝ))^24)*(oldRadical E t:ℝ)^24 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (mul_nonneg cpos (by positivity))

theorem scalar_sqrt_height_of_ordinary_chart {ρ : K} (root : ρ^2=2) (h s : ℤ) (x Γ : ℚ) (D : ℕ) (M : Finset ℚ)
    (hh : h≠0) (gn : Γ≠0) (charts : OrdinaryCharts (exceptional Γ M) K)
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff) (guard : (s-1) • paperGenerator root≠0)
    (tree : TreeCertificate root h s (scalarRadicand (beta x)) Γ D M) :
    logHeight₁ (beta x) ≤ scalarConstant Γ M*Real.sqrt |((s-1:ℤ):ℝ)| :=
  scalar_sqrt_height_at_cutoff root h s x Γ D M _ (fun _ m => m) hh gn charts upstream guard tree

theorem ordinaryCharts_of_large {M : Finset ℚ} {Γ : ℚ}
    (charts : ∀ (p : ℕ) [hp : Fact p.Prime], 65<p → ∀ (w : HeightOneSpectrum (𝓞 K)),
      w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal →
      OrdinaryFormalChart p w) : OrdinaryCharts (exceptional Γ M) K := by
  intro p hp away w lies
  have big := (exceptional_outside away).1
  exact charts p (by omega) w lies

end Sun28.ScalarHeight
#print axioms Sun28.ScalarHeight.goodModel_of_ordinary_chart
#print axioms Sun28.ScalarHeight.tree_prime48_of_ordinary_chart
#print axioms Sun28.ScalarHeight.scalar_product48_at_cutoff
#print axioms Sun28.ScalarHeight.scalar_sqrt_height_at_cutoff
#print axioms Sun28.ScalarHeight.scalar_sqrt_height_of_ordinary_chart
#print axioms Sun28.ScalarHeight.ordinaryCharts_of_large
