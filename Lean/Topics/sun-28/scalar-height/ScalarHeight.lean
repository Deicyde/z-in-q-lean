import ScalarPole
import Mathlib.NumberTheory.Height.NumberField

/-! The scalar product and the square-root bound on the original five-mark line. -/
open NumberField IsDedekindDomain Sun28.Scalar Sun28.Ordinary Height
open scoped NumberField
namespace Sun28.ScalarHeight

/-- A computable upper bound on the nonunit places, also allowing q=0. -/
def support (q : ℚ) : Finset ℕ := q.num.natAbs.primeFactors ∪ q.den.primeFactors

def exceptional (Γ : ℚ) (M : Finset ℚ) : Finset ℕ :=
  oldCutoff ∪ support Γ ∪ M.biUnion support

theorem support_unit {p : ℕ} [hp : Fact p.Prime] {q : ℚ} (away : p∉support q) :
    padicValRat p q=0 := by
  by_cases z : q=0
  · simp [z]
  have qn : q.num.natAbs≠0 := by simpa using z
  have n : ¬p∣q.num.natAbs := fun d => away (Finset.mem_union_left _ (Nat.mem_primeFactors.mpr ⟨hp.out,d,qn⟩))
  have d : ¬p∣q.den := fun d => away (Finset.mem_union_right _ (Nat.mem_primeFactors.mpr ⟨hp.out,d,q.den_nz⟩))
  simp only [padicValRat_def,padicValInt,padicValNat.eq_zero_of_not_dvd n,padicValNat.eq_zero_of_not_dvd d,
    Nat.cast_zero,sub_self]

theorem exceptional_outside {Γ : ℚ} {M : Finset ℚ} {p : ℕ} [hp : Fact p.Prime]
    (away : p∉exceptional Γ M) : 76176<p ∧ padicValRat p Γ=0 ∧ ∀ μ∈M,padicValRat p μ=0 := by
  have co : p∉oldCutoff := fun h => away (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have big : 76176<p := by
    by_contra! small
    exact co (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hp.out⟩)
  refine ⟨big,support_unit (fun h => away (Finset.mem_union_left _ (Finset.mem_union_right _ h))),?_⟩
  intro μ hm
  exact support_unit (fun h => away (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨μ,hm,h⟩)))

def oldRadical (S : Finset ℕ) (t : ℚ) : ℕ := ∏ p ∈ oldContactPrimes S t.num t.den, p

noncomputable def scalarConstant (Γ : ℚ) (M : Finset ℚ) : ℝ :=
  glazerConstant24*(∏ p ∈ extraPrimes oldCutoff (exceptional Γ M),(p:ℝ))^24

variable {K : Type*} [Field K] [NumberField K] [DecidableEq K] [Algebra.IsQuadraticExtension ℚ K]

def LocalCharts (S : Finset ℕ) (K : Type*) [Field K] [NumberField K] : Prop :=
  ∀ (p : ℕ) [hp : Fact p.Prime], p∉S → ∀ (w : HeightOneSpectrum (𝓞 K)),
    w.asIdeal.LiesOver ((Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,hp.out⟩).asIdeal →
    MinimalFormalGroupTheorems p w

theorem scalar_product48 {ρ : K} (root : ρ^2=2) (h s : ℤ) (x Γ : ℚ) (D : ℕ) (M : Finset ℚ)
    (hh : h≠0) (gn : Γ≠0) (classicalInputs : LocalCharts (exceptional Γ M) K)
    (accept : TreeCertificate root h s (scalarRadicand (beta x)) Γ D M ∨
      TraceCertificate root h s (scalarRadicand (beta x)) Γ D M) :
    ((oldRadical (exceptional Γ M) (beta x):ℤ)^48) ∣ s-1 := by
  unfold oldRadical
  rw [Nat.cast_prod]
  apply product_prime_powers (fun p mem => (mem_oldContactPrimes.mp mem).1)
  intro p mem
  obtain ⟨prime,away,_⟩ := mem_oldContactPrimes.mp mem
  let : Fact p.Prime := ⟨prime⟩
  obtain ⟨big,gu,multipliers⟩ := exceptional_outside away
  obtain ⟨pos,odd⟩ := old_scalar_contact big x _ mem
  let v := (Rat.HeightOneSpectrum.primesEquiv (R:=𝓞 ℚ)).symm ⟨p,prime⟩
  obtain ⟨P,maximal,lie⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S:=𝓞 K) v.asIdeal
  let w : HeightOneSpectrum (𝓞 K) := ⟨P,maximal.isPrime,Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨maximal.isPrime,lie⟩⟩
  let : w.asIdeal.LiesOver v.asIdeal := lie
  have charts := classicalInputs p away w lie
  rcases accept with cert|cert
  · exact tree_prime48 (by omega) w root charts hh D M pos odd gn gu multipliers cert
  · exact trace_prime48 (by omega) w root charts hh D M pos odd gn gu multipliers cert

theorem old_radical_enlargement (S E : Finset ℕ) (t : ℚ) :
    oldRadical S t ≤ (∏ p ∈ extraPrimes S E,p)*oldRadical E t := by
  classical
  let P (T : Finset ℕ) := oldContactPrimes T t.num t.den
  have subset : P S ⊆ extraPrimes S E ∪ P E := by
    intro p hp
    obtain ⟨prime,away,contact⟩ := mem_oldContactPrimes.mp hp
    by_cases inside : p∈E
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨inside,away⟩,prime⟩)
    · exact Finset.mem_union_right _ (mem_oldContactPrimes.mpr ⟨prime,inside,contact⟩)
  have disjoint : Disjoint (extraPrimes S E) (P E) := by
    apply Finset.disjoint_left.mpr
    intro p hp he
    exact (mem_oldContactPrimes.mp he).2.1 (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
  have pos (p : ℕ) (hp : p∈extraPrimes S E ∪ P E) : 1≤p := by
    rcases Finset.mem_union.mp hp with e|c
    · exact (Finset.mem_filter.mp e).2.one_lt.le
    · exact (mem_oldContactPrimes.mp c).1.one_lt.le
  have h := Finset.prod_le_prod_of_subset_of_one_le (f:=fun p:ℕ => p) subset (fun p hp _ => pos p hp)
  simpa only [Finset.prod_union disjoint,oldRadical,P] using h

theorem sqrt_of_power_dvd {m : ℕ} {a : ℤ} (nonzero : a≠0) (dvd : (m:ℤ)^48 ∣ a) :
    (m:ℝ)^24 ≤ Real.sqrt |(a:ℝ)| := by
  have nd : m^48∣a.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr dvd
  have nat := Nat.le_of_dvd (Int.natAbs_pos.mpr nonzero) nd
  have lifted : (m:ℝ)^48≤(a.natAbs:ℝ) := by exact_mod_cast nat
  have real : (m:ℝ)^48≤|(a:ℝ)| := by simpa only [Nat.cast_natAbs,Int.cast_abs] using lifted
  have h := Real.sqrt_le_sqrt real
  rwa [show (m:ℝ)^48=((m:ℝ)^24)^2 by ring,Real.sqrt_sq (by positivity)] at h

theorem scalar_sqrt_height {ρ : K} (root : ρ^2=2) (h s : ℤ) (x Γ : ℚ) (D : ℕ) (M : Finset ℚ)
    (hh : h≠0) (gn : Γ≠0) (classicalInputs : LocalCharts (exceptional Γ M) K)
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff)
    (guard : (s-1) • paperGenerator root≠0)
    (accept : TreeCertificate root h s (scalarRadicand (beta x)) Γ D M ∨
      TraceCertificate root h s (scalarRadicand (beta x)) Γ D M) :
    logHeight₁ (beta x) ≤ scalarConstant Γ M*Real.sqrt |((s-1:ℤ):ℝ)| := by
  let t:=beta x
  let E:=exceptional Γ M
  have nz : s-1≠0 := fun z => guard (by rw [z,zero_zsmul])
  have dv := scalar_product48 root h s x Γ D M hh gn classicalInputs accept
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
    _ = scalarConstant Γ M*(oldRadical E t:ℝ)^24 := by unfold scalarConstant; dsimp [E]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left bound (by unfold scalarConstant; positivity)

theorem scalarConstant_eq_of_small {Γ : ℚ} {M : Finset ℚ}
    (smallΓ : support Γ ⊆ oldCutoff) (smallM : ∀ μ∈M,support μ ⊆ oldCutoff) :
    scalarConstant Γ M=glazerConstant24 := by
  have eq : exceptional Γ M=oldCutoff := by
    apply Finset.Subset.antisymm
    · intro p hp
      rcases Finset.mem_union.mp hp with h|h
      · rcases Finset.mem_union.mp h with old|g
        · exact old
        · exact smallΓ g
      · obtain ⟨μ,hm,hp⟩ := Finset.mem_biUnion.mp h
        exact smallM μ hm hp
    · exact fun p h => Finset.mem_union_left _ (Finset.mem_union_left _ h)
  simp [scalarConstant,extraPrimes,eq]

end Sun28.ScalarHeight
#print axioms Sun28.ScalarHeight.exceptional_outside
#print axioms Sun28.ScalarHeight.scalar_product48
#print axioms Sun28.ScalarHeight.old_radical_enlargement
#print axioms Sun28.ScalarHeight.sqrt_of_power_dvd
#print axioms Sun28.ScalarHeight.scalar_sqrt_height
#print axioms Sun28.ScalarHeight.scalarConstant_eq_of_small
