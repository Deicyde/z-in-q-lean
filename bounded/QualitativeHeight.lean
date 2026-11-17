import ZInQKernel.Assembly.Local.TestDivisibility
import ZInQKernel.Hypotheses.HeightMin
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Multiplication.Completeness.PoleValuationsAux
import ZInQKernel.Multiplication.Soundness.RationalHeights

/-!
# Transfer of a cofinite Picard-family height estimate

The six branch values on the Picard parameter line are the zeros of a binary
sextic. At primes outside the multiplication prime set its odd valuations in
primitive coordinates detect exactly the primes in Glazer's contact support.
This gives a single coefficient for all parameters from a bad-prime product
bound on any cofinite open of the Picard line.
-/

namespace ZInQ.QualitativeHeight

open scoped BigOperators

/-- The Picard-family coordinate of a nonzero rational parameter. -/
noncomputable def picardParameter (t : ℚ) : ℚ := 5 + 120 / t

/-- The six projective branch points are infinity, zero, ±1 and ±3. -/
noncomputable def branchForm (x y : ℚ) : ℚ := x * y * (x - y) * (x + y) * (x - 3*y) * (x + 3*y)

/-- Evaluate the homogeneous branch form on primitive numerator-denominator coordinates. -/
noncomputable def primitiveBranch (s : ℚ) : ℚ := branchForm s.num s.den

private theorem nonzero_parameter {t : ℚ} (ht : t ∉ contactSet) : t ≠ 0 := by
  intro h
  apply ht
  rw [h]
  decide

theorem branchForm_change {t : ℚ} (ht : t ≠ 0) (y : ℚ) :
    branchForm (picardParameter t * y) y =
      (y / t)^6 * (1920 * Mult.contactPoly t) := by
  unfold branchForm picardParameter Mult.contactPoly
  field_simp [ht]
  ring

theorem primitiveBranch_change {t : ℚ} (ht : t ∉ contactSet) :
    primitiveBranch (picardParameter t) =
      (((picardParameter t).den : ℚ) / t)^6 * (1920 * Mult.contactPoly t) := by
  unfold primitiveBranch
  rw [← Rat.mul_den_eq_num (picardParameter t)]
  exact branchForm_change (nonzero_parameter ht) _

theorem primitiveBranch_ne_zero {t : ℚ} (ht : t ∉ contactSet) :
    primitiveBranch (picardParameter t) ≠ 0 := by
  rw [primitiveBranch_change ht]
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (by exact_mod_cast (picardParameter t).den_nz)
    (nonzero_parameter ht))) (mul_ne_zero (by norm_num) (Mult.contactPoly_ne_zero ht))

private theorem valuation_1920 {p : ℕ} (hp : p.Prime) (large : 61 < p) :
    padicValRat p 1920 = 0 := by
  have nd : ¬ p ∣ 1920 := by
    intro hd
    rw [show (1920 : ℕ) = 32 * 60 by decide] at hd
    rcases hp.dvd_mul.mp hd with h | h
    · have := Nat.le_of_dvd (by decide : 0 < 32) h
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 60) h
      omega
  rw [show (1920 : ℚ) = ((1920 : ℕ) : ℚ) by norm_num,
    padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd nd]
  rfl

private theorem odd_contactPoly_iff {p : ℕ} (hp : p.Prime) (large : 61 < p)
    {t : ℚ} (ht : t ∉ contactSet) :
    Odd (padicValRat p (Mult.contactPoly t)) ↔ Mult.IsOddContactPrime t p := by
  let : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hodd
    by_cases h1 : t = 1
    · subst t
      have units (c : ℚ) (hc : c ∈ contactSet) :
          (1 : ℚ) - c ≠ 0 ∧ padicValRat p (1 - c) = 0 := by
        have hne : (1 : ℚ) ≠ c := by intro e; apply ht; rwa [e]
        exact ⟨sub_ne_zero.mpr hne, Mult.padicValRat_contact_diff large
          (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hc) hne⟩
      have hv := (Mult.padicValRat_prod_eq_zero (p := p) contactSet
        (fun c : ℚ => 1 - c) units).2
      rw [Mult.contactPoly_eq_prod, hv] at hodd
      obtain ⟨k, hk⟩ := hodd
      omega
    · by_contra hn
      have he := Mult.even_padicValRat_contactQuot hp ht h1 hn
      rw [padicValRat.div (Mult.contactPoly_ne_zero ht) (pow_ne_zero 8 (sub_ne_zero.mpr h1)),
        padicValRat.pow] at he
      obtain ⟨a, ha⟩ := he
      obtain ⟨b, hb⟩ := hodd
      omega
  · rintro ⟨_, c, hc, hpos, hodd⟩
    rwa [Assembly.contact_val (by omega) hc ht hpos]

/-- A change of homogeneous coordinates contributes a sixth power, including
at denominator primes. Off the fixed small primes, odd branch valuation is
equivalent to a positive odd valuation at a finite contact of the original parameter. -/
theorem primitiveBranch_odd_iff {p : ℕ} (hp : p.Prime) (large : 61 < p)
    {t : ℚ} (ht : t ∉ contactSet) :
    Odd (padicValRat p (primitiveBranch (picardParameter t))) ↔ Mult.IsOddContactPrime t p := by
  let : Fact p.Prime := ⟨hp⟩
  have hq : ((picardParameter t).den : ℚ) / t ≠ 0 :=
    div_ne_zero (by exact_mod_cast (picardParameter t).den_nz) (nonzero_parameter ht)
  have hf := Mult.contactPoly_ne_zero ht
  rw [← odd_contactPoly_iff hp large ht, primitiveBranch_change ht,
    padicValRat.mul (pow_ne_zero 6 hq) (mul_ne_zero (by norm_num) hf),
    padicValRat.pow, padicValRat.mul (by norm_num : (1920 : ℚ) ≠ 0) hf, valuation_1920 hp large,
    zero_add]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k - 3 * padicValRat p (((picardParameter t).den : ℚ) / t), by omega⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 3 * padicValRat p (((picardParameter t).den : ℚ) / t), by omega⟩

/-- The product accounts for the fixed primes of the family and the primes
excluded from Glazer's multiplication support. -/
noncomputable def fixedPrimeProduct (fixed : Finset ℕ) : ℕ :=
  ∏ p ∈ fixed ∪ Mult.S_mul, p

private theorem primeProduct_dvd {bad : Finset ℕ} {n : ℕ}
    (primes : ∀ p ∈ bad, p.Prime) (each : ∀ p ∈ bad, p ∣ n) :
    (∏ p ∈ bad, p) ∣ n := by
  apply Int.natCast_dvd_natCast.mp
  rw [Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hne
    exact Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes (primes p hp) (primes q hq)).mpr hne)
  · intro p hp
    exact Int.natCast_dvd_natCast.mpr (each p hp)

/-- For a finite set of bad primes supported by fixed primes and odd branch
valuations, its product divides the stated constant times Glazer's radical. -/
theorem badPrimeProduct_dvd {t : ℚ} (ht : t ∉ contactSet) (fixed bad : Finset ℕ)
    (primes : ∀ p ∈ bad, p.Prime)
    (support : ∀ p ∈ bad, p ∈ fixed ∨ Odd (padicValRat p (primitiveBranch (picardParameter t)))) :
    (∏ p ∈ bad, p) ∣ fixedPrimeProduct fixed * contactSupport Mult.S_mul t := by
  apply primeProduct_dvd primes
  intro p hp
  by_cases hx : p ∈ fixed ∪ Mult.S_mul
  · exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun q : ℕ => q) hx) _
  · have hs : p ∉ Mult.S_mul := fun h => hx (Finset.mem_union_right _ h)
    have hf : p ∉ fixed := fun h => hx (Finset.mem_union_left _ h)
    have pp := primes p hp
    have hlarge := (Mult.not_mem_S_mul pp hs).1
    have hc := (primitiveBranch_odd_iff pp (by omega) ht).mp ((support p hp).resolve_left hf)
    exact dvd_mul_of_dvd_right ((Mult.prime_dvd_contactSupport_iff' ht pp).mpr ⟨hs, hc⟩) _

noncomputable def coordinateCost : ℝ :=
  ratHeight 120 + ratHeight (-5) + ratHeight 0 + Real.log 3

theorem original_height_le (t : ℚ) :
    ratHeight t ≤ ratHeight (picardParameter t) + coordinateCost := by
  have back : (120 : ℚ) / (picardParameter t - 5) = t := by
    rw [show picardParameter t - 5 = 120 / t by unfold picardParameter; ring,
      div_div_eq_mul_div]
    ring
  have hadd : ratHeight (picardParameter t - 5) ≤
      ratHeight (picardParameter t) + ratHeight (-5) + ratHeight 0 + Real.log 3 := by
    simpa only [add_zero, sub_eq_add_neg] using Mult.ratHeight_add3_le (picardParameter t) (-5) 0
  have hdiv := Mult.ratHeight_div_le 120 (picardParameter t - 5)
  rw [back] at hdiv
  unfold coordinateCost
  linarith

/-- A height estimate for the Picard parameter on a cofinite open and good
reduction away from odd branches and fixed primes give a single positive
integer coefficient in the original six-contact inequality. -/
theorem exists_uniform_height_bound (fixed : Finset ℕ) (except : Finset ℚ) (bad : ℚ → Finset ℕ)
    {A B : ℝ} (hA : 0 ≤ A) (fixedPrimes : ∀ p ∈ fixed, p.Prime)
    (support : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ∀ p ∈ bad s, p.Prime ∧ (p ∈ fixed ∨ Odd (padicValRat p (primitiveBranch s))))
    (height : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ratHeight s ≤ A * ((∏ p ∈ bad s, p : ℕ) : ℝ)^24 + B) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ t : ℚ, t ∉ contactSet →
      ratHeight t ≤ (m : ℝ) * (contactSupport Mult.S_mul t : ℝ)^24 := by
  classical
  let Z := fixedPrimeProduct fixed
  let H := ∑ s ∈ except, ratHeight s
  let D := H + |B| + |coordinateCost|
  have hZ : 0 < Z := Finset.prod_pos fun p hp =>
    (Finset.mem_union.mp hp).elim (fun h => (fixedPrimes p h).pos)
      (fun h => (Mult.prime_of_mem_S_mul h).pos)
  have hH : 0 ≤ H := Finset.sum_nonneg fun s _ => Mult.ratHeight_nonneg s
  have hD : 0 ≤ D := add_nonneg (add_nonneg hH (abs_nonneg B)) (abs_nonneg _)
  obtain ⟨m, hm⟩ := exists_nat_ge (max (1 : ℝ) (A * (Z : ℝ)^24 + D))
  refine ⟨m, ?_, ?_⟩
  · exact_mod_cast (le_max_left (1 : ℝ) _).trans hm
  intro t ht
  let s := picardParameter t
  let M := contactSupport Mult.S_mul t
  have hM : 0 < M := contactSupport_pos _ _
  have oneM : (1 : ℝ) ≤ (M : ℝ)^24 := one_le_pow₀ (by exact_mod_cast hM)
  have hbase : ratHeight s ≤ A * (Z : ℝ)^24 * (M : ℝ)^24 + (H + |B|) := by
    by_cases hx : s ∈ except
    · have hs : ratHeight s ≤ H :=
        Finset.single_le_sum (f := ratHeight) (fun x _ => Mult.ratHeight_nonneg x) hx
      have hn : 0 ≤ A * (Z : ℝ)^24 * (M : ℝ)^24 := by positivity
      linarith [abs_nonneg B]
    · have hn : primitiveBranch s ≠ 0 := primitiveBranch_ne_zero ht
      have hd := badPrimeProduct_dvd ht fixed (bad s)
        (fun p hp => (support s hx hn p hp).1) (fun p hp => (support s hx hn p hp).2)
      have hprod : (∏ p ∈ bad s, p) ≤ Z * M := Nat.le_of_dvd (Nat.mul_pos hZ hM) hd
      have hr : ((∏ p ∈ bad s, p : ℕ) : ℝ) ≤ (Z : ℝ) * (M : ℝ) := by exact_mod_cast hprod
      have hpow := pow_le_pow_left₀ (Nat.cast_nonneg (∏ p ∈ bad s, p)) hr 24
      rw [mul_pow] at hpow
      calc
        ratHeight s ≤ A * ((∏ p ∈ bad s, p : ℕ) : ℝ)^24 + B := height s hx hn
        _ ≤ A * ((Z : ℝ)^24 * (M : ℝ)^24) + B :=
          add_le_add (mul_le_mul_of_nonneg_left hpow hA) le_rfl
        _ ≤ A * (Z : ℝ)^24 * (M : ℝ)^24 + (H + |B|) := by
          rw [mul_assoc]
          linarith [le_abs_self B]
  have horig : ratHeight t ≤ ratHeight s + coordinateCost := original_height_le t
  have hsum : ratHeight t ≤ A * (Z : ℝ)^24 * (M : ℝ)^24 + D := by
    dsimp only [D]
    linarith [le_abs_self coordinateCost]
  have absorb : D ≤ D * (M : ℝ)^24 := by
    calc D = D * 1 := (mul_one D).symm
         _ ≤ D * (M : ℝ)^24 := mul_le_mul_of_nonneg_left oneM hD
  calc
    ratHeight t ≤ A * (Z : ℝ)^24 * (M : ℝ)^24 + D := hsum
    _ ≤ (A * (Z : ℝ)^24 + D) * (M : ℝ)^24 := by rw [add_mul]; linarith
    _ ≤ (m : ℝ) * (M : ℝ)^24 :=
      mul_le_mul_of_nonneg_right ((le_max_right (1 : ℝ) _).trans hm) (by positivity)

/-- The integer `v₀` in von Känel's equation (6.7). Its small-prime exponent
counts just those excluded primes at most `2g+1`. -/
def vonKanelParameter (g : ℕ) (bad : Finset ℕ) : ℕ :=
  (2*g + 1)^(6 * (bad.filter (fun p => p ≤ 2*g + 1)).card) * (∏ p ∈ bad, p)^2

/-- The right hand side of von Känel, Theorem 6.2, equation (6.7). -/
noncomputable def vonKanelBound (g : ℕ) (bad : Finset ℕ) : ℝ :=
  let v := (vonKanelParameter g bad : ℝ)
  (g : ℝ) * (18000 * v^12 + (8*(g : ℝ))^6 * Real.log v)

noncomputable def dimensionCoefficient (g : ℕ) : ℝ :=
  (g : ℝ) * (18000 + (8*(g : ℝ))^6) * (((2*g + 1)^(6*(2*g + 1)) : ℕ) : ℝ)^12

/-- Equation (6.7) grows at most as the twenty-fourth power of the product of
bad primes, uniformly in their number when the dimension is fixed. -/
theorem vonKanelBound_le (g : ℕ) (bad : Finset ℕ) (primes : ∀ p ∈ bad, p.Prime) :
    vonKanelBound g bad ≤ dimensionCoefficient g * ((∏ p ∈ bad, p : ℕ) : ℝ)^24 := by
  let N := ∏ p ∈ bad, p
  let r := (bad.filter fun p => p ≤ 2*g + 1).card
  let scale := (2*g + 1)^(6*(2*g + 1))
  let v := vonKanelParameter g bad
  have count : r ≤ 2*g + 1 := by
    have hsub : (bad.filter fun p => p ≤ 2*g + 1) ⊆ Finset.Icc 1 (2*g + 1) := by
      intro p hp
      obtain ⟨hm, hle⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_Icc.mpr ⟨(primes p hm).one_lt.le, hle⟩
    have h := Finset.card_le_card hsub
    rwa [Nat.card_Icc, Nat.add_sub_cancel] at h
  have hN : 0 < N := Finset.prod_pos fun p hp => (primes p hp).pos
  have vpos : 0 < v :=
    Nat.mul_pos (pow_pos (by omega : 0 < 2*g + 1) _) (pow_pos hN 2)
  have vbound : v ≤ scale * N^2 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right
    (by omega : 0 < 2*g + 1) (show 6*r ≤ 6*(2*g + 1) by omega))
  have hr : (v : ℝ) ≤ (scale : ℝ) * (N : ℝ)^2 := by exact_mod_cast vbound
  have h12 : (v : ℝ)^12 ≤ (scale : ℝ)^12 * (N : ℝ)^24 := by
    calc
      (v : ℝ)^12 ≤ ((scale : ℝ) * (N : ℝ)^2)^12 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hr 12
      _ = (scale : ℝ)^12 * (N : ℝ)^24 := by rw [mul_pow, ← pow_mul]
  have hlog : Real.log (v : ℝ) ≤ (v : ℝ)^12 := by
    have pos : (0 : ℝ) < v := by exact_mod_cast vpos
    have one : (1 : ℝ) ≤ v := by exact_mod_cast vpos
    have power : (v : ℝ) ≤ (v : ℝ)^12 := le_self_pow₀ one (by norm_num)
    linarith [Real.log_le_sub_one_of_pos pos]
  change (g : ℝ) * (18000 * (v : ℝ)^12 + (8*(g : ℝ))^6 * Real.log (v : ℝ)) ≤
    (g : ℝ) * (18000 + (8*(g : ℝ))^6) * (scale : ℝ)^12 * (N : ℝ)^24
  calc
    _ ≤ (g : ℝ) * (18000 * ((scale : ℝ)^12 * (N : ℝ)^24) +
        (8*(g : ℝ))^6 * ((scale : ℝ)^12 * (N : ℝ)^24)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h12 (by norm_num))
        (mul_le_mul_of_nonneg_left (hlog.trans h12) (by positivity))) (Nat.cast_nonneg g)
    _ = _ := by ring

/-- Apply the preceding estimates to a fixed-dimensional family once its
bad-reduction support, the numerical bound (6.7) for its fibre heights, and
the comparison with the rational Picard parameter have been established. -/
theorem exists_uniform_height_of_vonKanel (g : ℕ) (fixed : Finset ℕ) (except : Finset ℚ)
    (bad : ℚ → Finset ℕ) (fibreHeight : ℚ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (fixedPrimes : ∀ p ∈ fixed, p.Prime)
    (support : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ∀ p ∈ bad s, p.Prime ∧ (p ∈ fixed ∨ Odd (padicValRat p (primitiveBranch s))))
    (effective : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      fibreHeight s ≤ vonKanelBound g (bad s))
    (comparison : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ratHeight s ≤ a * max 1 (fibreHeight s) + b) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ t : ℚ, t ∉ contactSet →
      ratHeight t ≤ (m : ℝ) * (contactSupport Mult.S_mul t : ℝ)^24 := by
  have hK : 0 ≤ dimensionCoefficient g := by unfold dimensionCoefficient; positivity
  apply exists_uniform_height_bound fixed except bad (A := a * dimensionCoefficient g)
    (B := a + b) (mul_nonneg ha hK) fixedPrimes support
  intro s hx hn
  let N := ∏ p ∈ bad s, p
  have hF : fibreHeight s ≤ dimensionCoefficient g * (N : ℝ)^24 :=
    (effective s hx hn).trans (vonKanelBound_le g (bad s) (fun p hp => (support s hx hn p hp).1))
  have hnonneg : 0 ≤ dimensionCoefficient g * (N : ℝ)^24 := mul_nonneg hK (by positivity)
  have hmax : max 1 (fibreHeight s) ≤ dimensionCoefficient g * (N : ℝ)^24 + 1 :=
    max_le (by linarith) (by linarith)
  calc
    ratHeight s ≤ a * max 1 (fibreHeight s) + b := comparison s hx hn
    _ ≤ a * (dimensionCoefficient g * (N : ℝ)^24 + 1) + b :=
      add_le_add (mul_le_mul_of_nonneg_left hmax ha) le_rfl
    _ = a * dimensionCoefficient g * (N : ℝ)^24 + (a + b) := by ring

end ZInQ.QualitativeHeight

#print axioms ZInQ.QualitativeHeight.primitiveBranch_odd_iff
#print axioms ZInQ.QualitativeHeight.badPrimeProduct_dvd
#print axioms ZInQ.QualitativeHeight.exists_uniform_height_bound
#print axioms ZInQ.QualitativeHeight.vonKanelBound_le
#print axioms ZInQ.QualitativeHeight.exists_uniform_height_of_vonKanel
