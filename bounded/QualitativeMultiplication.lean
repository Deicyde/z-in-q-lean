import ZInQKernel.RouteK.RankVariants

/-! Multiplication on the elliptic model with a guard determined by a uniform
six-contact height estimate. The slope primes and the unguarded certificate
are the ones in Glazer's construction. -/

namespace ZOverQ.Qualitative

open ZInQ ZInQ.Syntax

/-- A height estimate at the multiplication prime set with coefficient `C`. -/
def UniformHeight (C : ℝ) : Prop :=
  ∀ t : ℚ, t ∉ contactSet → ratHeight t ≤ C * (contactSupport Mult.S_mul t : ℝ) ^ 24

/-- The integer radius of the box containing any accepted false triple. -/
def guardCutoff (m : ℕ) : ℤ := (48 * (m : ℤ)) ^ 13

theorem exists_integer_height {C : ℝ} (height : UniformHeight C) :
    ∃ m : ℕ, 1 ≤ m ∧ UniformHeight (m : ℝ) := by
  obtain ⟨m, hm⟩ := exists_nat_ge (max (1 : ℝ) C)
  refine ⟨m, ?_, fun t ht => (height t ht).trans ?_⟩
  · exact_mod_cast (le_max_left (1 : ℝ) C).trans hm
  · exact mul_le_mul_of_nonneg_right ((le_max_right (1 : ℝ) C).trans hm) (by positivity)

/-- The local congruences give a height bound for each slope in a false triple. -/
private theorem slope_bound {m : ℕ} (height : UniformHeight (m : ℝ)) (n : Fin 3 → ℤ)
    (hf : n 0 * n 1 - n 2 ≠ 0) {t : ℚ}
    (slope : Mult.SlopePred t (Syntax.ell : ℚ) (Mult.certShifts n)) :
    ratHeight t ≤ (m : ℝ) * |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25) := by
  have outside (p : ℕ) (hp : p.Prime) (hs : p ∉ Mult.S_mul) :
      324 < p ∧ ¬ (p : ℤ) ∣ (Syntax.cstar : ℤ) ∧ padicValRat p (Syntax.ell : ℚ) = 0 := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨h324, hc, _, _⟩ := Mult.not_mem_S_mul hp hs
    exact ⟨h324, by exact_mod_cast hc,
      Mult.padicValRat_ell_of_not_mem fun hb => hs (Mult.S_b_subset_S_mul hb)⟩
  exact (Mult.slope_height_le_of (Nat.cast_nonneg m) height outside n hf slope).2

/-- Apply the finite-box inequality to the nine entries of the height certificate. -/
private theorem finite_box {m : ℕ} (hm : 1 ≤ m) (height : UniformHeight (m : ℝ))
    (n : Fin 3 → ℤ) (hf : n 0 * n 1 ≠ n 2)
    (cert : Mult.HeightCert (fun i => iota (n i)) (Syntax.ell : ℚ) (Mult.certShifts n)) :
    ∀ i, |n i| < guardCutoff m := by
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  obtain ⟨A, b, hb, hQ⟩ := cert
  have entries (k : Fin 9) : ∃ t₁ t₂ t₃ : ℚ, t₁ + t₂ + t₃ = Mult.nineQ A b k ∧
      ∀ t ∈ ({t₁, t₂, t₃} : Set ℚ),
        ratHeight t ≤ (m : ℝ) * |((n 0 * n 1 - n 2 : ℤ) : ℝ)| ^ ((24 : ℝ) / 25) := by
    obtain ⟨s, hsum, hs⟩ := hQ k
    refine ⟨s 0, s 1, s 2, hsum, fun t ht => ?_⟩
    rcases ht with rfl | rfl | rfl
    · exact slope_bound height n (sub_ne_zero.mpr hf) (hs 0)
    · exact slope_bound height n (sub_ne_zero.mpr hf) (hs 1)
    · exact slope_bound height n (sub_ne_zero.mpr hf) (hs 2)
  have box := Mult.finite_box_of_heights hm' n (sub_ne_zero.mpr hf) fun i => by
    obtain ⟨hb0, e₀, e₁⟩ := hb i
    refine ⟨A i 0, A i 1, b i, hb0, e₀, e₁, ?_⟩
    obtain ⟨⟨k₀, h₀⟩, ⟨k₁, h₁⟩, ⟨k₂, h₂⟩⟩ := Mult.nineQ_surj A b i
    intro Q hQm
    rcases hQm with rfl | rfl | rfl
    · rw [← h₀]; exact entries k₀
    · rw [← h₁]; exact entries k₁
    · rw [← h₂]; exact entries k₂
  intro i
  have hi := box i
  have hcut : (guardCutoff m : ℝ) = (48 * (m : ℝ)) ^ 13 := by simp [guardCutoff]
  rw [← hcut] at hi
  exact_mod_cast hi

/-- The class-sum rank implication supplies the pole witnesses on both selected twists. -/
theorem pole_of_class_sum (rank : RouteK.Rank.CertifiedRankTYZClRk) : PoleCompleteness := by
  have htyz := RouteK.Redei.certifiedRankTYZ_iff'.mp
    (RouteK.Rank.certifiedRankTYZCl_of_certifiedRankTYZClRk' rank)
  have hsel := RouteK.Rank5b.certifiedRankSel_of_certifiedRank5b
    (RouteK.Rank5b.certifiedRank5b_of_certifiedRankTYZ htyz)
  exact poleCompleteness_of_certifiedRank (RouteK.Selmer.certifiedRank_of_certifiedRankSel hsel)

/-- The multiplication template with the chosen guard is exact on all rational point codes. -/
theorem multiplication_exact {m : ℕ} (hm : 1 ≤ m) (height : UniformHeight (m : ℝ))
    (pole : PoleCompleteness) :
    Translation.MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value
      (guardCutoff m) := by
  intro P Q R
  change (multiplyTemplate specConstructors _ _ (guardCutoff m)).Rel (codes3 P Q R) ↔ _
  rw [FixedConst.value_cstar, FixedConst.value_ell,
    Mult.multiply_rel_iff_cert specConstructors _ Mult.spec_scalar_cstar_rel_iff]
  constructor
  · rintro ⟨n, rfl, rfl, rfl, cert, guard⟩
    by_cases hf : n 0 * n 1 = n 2
    · exact ⟨n 0, n 1, rfl, rfl, by rw [hf]⟩
    have codes : (![iota (n 0), iota (n 1), iota (n 2)] : Fin 3 → Fin 5 → ℚ) =
        fun i => iota (n i) := by funext i; fin_cases i <;> rfl
    rw [codes] at cert
    exact False.elim (Mult.guard_false_triple specConstructors _ rfl n
      (fun i => (finite_box hm height n hf cert i).le) hf guard)
  · rintro ⟨a, b, rfl, rfl, rfl⟩
    -- True triples already have a height certificate independent of the guard.
    have slopes := Mult.slopeRepresentationAP_of_goodPrimeAP
      (Density.goodPrimeAP_of_greenTaoDense' greenTaoDense)
    have original := Mult.multiply_complete_AP pole slopes a b
    rw [FixedConst.value_cstar, FixedConst.value_ell,
      Mult.multiply_rel_iff_cert specConstructors _ Mult.spec_scalar_cstar_rel_iff] at original
    obtain ⟨n, e₀, e₁, e₂, cert, _⟩ := original
    exact ⟨n, e₀, e₁, e₂, cert, Mult.guard_true_triple specConstructors _ rfl a b⟩

end ZOverQ.Qualitative

#print axioms ZOverQ.Qualitative.exists_integer_height
#print axioms ZOverQ.Qualitative.pole_of_class_sum
#print axioms ZOverQ.Qualitative.multiplication_exact
