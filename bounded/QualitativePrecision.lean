import ZInQKernel.Assembly.Close
import ZInQKernel.Assembly.Local.TestCompleteness
import ZInQKernel.Assembly.Top.MainBranch
import ZInQKernel.Syntax.Recipes.FixedScalar

/-!
# Recovering an integer from a uniform height estimate

The local tests use a shift `κ`. The precision polynomial uses the shift
`m * κ`, where one fixed positive integer `m` dominates the height constant.
The guard `T` enters only through correctness of multiplication.

The precision and window proofs specialize Glazer's
`Assembly/Close/{Relation,Soundness,Completeness}` at an arbitrary exact guard.
-/

namespace ZOverQ.Qualitative

open ZInQ ZInQ.Syntax ZInQ.Assembly ZInQ.Translation
open ZInQ.Compiler.Precision ZInQ.Compiler.Natural
open ZInQ.Compiler.Universal (precisionCircuitOf)

noncomputable abbrev precisionLibrary (T : ℤ) : List ExPoly :=
  specLib specConstructors FixedConst.cstar.value FixedConst.ell.value T
    (Compiler.Universal.c3 : ℤ) (precisionCircuitOf (Compiler.Universal.c3 : ℤ))

/-- The original precision program and rational window with multiplication guard `T`. -/
def CloseAt (T : ℤ) (N K : Fin 5 → ℚ) (t : ℚ) : Prop :=
  ValRel (getEx (precisionLibrary T) 2) (List.ofFn N ++ (List.ofFn K ++ [t]))

theorem closeParams (T : ℤ) : (getEx (precisionLibrary T) 2).params = 11 := by
  rw [precisionLibrary, getEx_specLib _ _ _ _ _ _ (i := 2) (by decide)]
  rfl

theorem closeAt_iff_rel (T : ℤ) (N K : Fin 5 → ℚ) (t : ℚ) :
    CloseAt T N K t ↔ (getEx (precisionLibrary T) 2).Rel
      (fun i => Fin.append (Fin.append N K) ![t] (Fin.cast (closeParams T) i)) := by
  rw [CloseAt, ← List.append_assoc, show [t] = List.ofFn ![t] from rfl,
    ← List.ofFn_fin_append, ← List.ofFn_fin_append]
  exact valRel_ofFn_iff _ (closeParams T) _

variable {T : ℤ}

private theorem precision_iff
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value T)
    (E₀ E₁ E₂ E₃ E₄ : Fin 5 → ℚ) :
    ValRel (getEx (precisionLibrary T) 1)
        (List.ofFn E₀ ++ List.ofFn E₁ ++ List.ofFn E₂ ++ List.ofFn E₃ ++ List.ofFn E₄) ↔
      ∃ c : Fin 5 → ℕ, (∀ i, (![E₀, E₁, E₂, E₃, E₄] : Fin 5 → Fin 5 → ℚ) i = iota (c i)) ∧
        accepts c := by
  rw [precisionLibrary, getEx_specLib _ _ _ _ _ _ (i := 1) (by decide), ofFn_rows]
  refine (valRel_ofFn_iff _ rfl _).trans ?_
  exact precision_rel_iff_accepts_of specConstructors _ _ _ rfl hM
    Compiler.natural_polynomial_semantics' _
    ⟨_, (getEx_specLib_take _ _ _ _ _ _ (i := 1) (j := 0) (by decide) (by decide)).trans
      (getEx_specLib _ _ _ _ _ _ (i := 0) (by decide))⟩ _

/-- Exact semantics of the window and precision computation at guard `T`. -/
theorem closeAt_iff
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value T)
    (N K : Fin 5 → ℚ) (t : ℚ) :
    CloseAt T N K t ↔
      ∃ n κ a l : ℤ, N = iota n ∧ K = iota κ ∧
        accepts ![enc n, enc κ, enc a, enc l, enc (n * a)] ∧
        |t - rRatio a (n * a)| < epsIdx l := by
  rw [CloseAt, precisionLibrary, spec_close_rel_iff]
  simp only [signedEncode_rel_iff hM, closeCoordinates_rel_iff]
  simp only [precision_iff hM]
  constructor
  · rintro ⟨A, L, J, E₀, E₁, E₂, E₃, E₄, ⟨m₀, rfl, rfl⟩, ⟨m₁, rfl, rfl⟩, ⟨m₂, rfl, rfl⟩,
      ⟨m₃, rfl, rfl⟩, ⟨m₄, rfl, rfl⟩, ⟨c, hc, hacc⟩, ⟨a, l, j, ha, hl, hj, -, -, hw⟩⟩
    have hci : ∀ (i : Fin 5) (m : ℤ),
        (![iota (enc m₀ : ℤ), iota (enc m₁ : ℤ), iota (enc m₂ : ℤ), iota (enc m₃ : ℤ),
          iota (enc m₄ : ℤ)] : Fin 5 → Fin 5 → ℚ) i = iota (enc m : ℤ) → c i = enc m :=
      fun i m h => by
        have := iota_injective ((hc i).symm.trans h)
        exact_mod_cast this
    have hc' : c = ![enc m₀, enc m₁, enc m₂, enc m₃, enc m₄] := by
      funext i
      fin_cases i
      · exact hci 0 m₀ rfl
      · exact hci 1 m₁ rfl
      · exact hci 2 m₂ rfl
      · exact hci 3 m₃ rfl
      · exact hci 4 m₄ rfl
    rw [hc', accepts_enc_iff] at hacc
    rw [← iota_injective ha, ← iota_injective hl, ← iota_injective hj] at hw
    have h4 : m₄ = m₀ * m₂ := hacc.1.2.2.2.2
    subst h4
    exact ⟨m₀, m₁, m₂, m₃, rfl, rfl, (accepts_enc_iff _ _ _ _ _).2 hacc, hw⟩
  · rintro ⟨n, κ, a, l, rfl, rfl, hacc, hw⟩
    have hacc' := (accepts_enc_iff _ _ _ _ _).1 hacc
    obtain ⟨⟨-, -, ha, hl, -⟩, -⟩ := hacc'
    refine ⟨iota a, iota l, iota (n * a), iota (enc n : ℤ), iota (enc κ : ℤ), iota (enc a : ℤ),
      iota (enc l : ℤ), iota (enc (n * a) : ℤ), ⟨n, rfl, rfl⟩, ⟨κ, rfl, rfl⟩, ⟨a, rfl, rfl⟩,
      ⟨l, rfl, rfl⟩, ⟨n * a, rfl, rfl⟩, ⟨![enc n, enc κ, enc a, enc l, enc (n * a)], ?_, hacc⟩,
      ⟨a, l, n * a, rfl, rfl, rfl, by omega, by omega, hw⟩⟩
    intro i
    fin_cases i <;> rfl

theorem closeAt_sound
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value T)
    {n κ : ℤ} {t : ℚ} (h : CloseAt T (iota n) (iota κ) t) :
    (n : ℚ) ∉ contactSet ∧ κ ≠ 0 ∧ |(t : ℝ) - n| < Real.exp (-(bound n κ : ℝ)) := by
  obtain ⟨n', κ', a, l, hn, hκ, accepted, window⟩ := (closeAt_iff hM _ _ _).1 h
  obtain rfl := iota_injective hn
  obtain rfl := iota_injective hκ
  obtain ⟨⟨hn, hκ, -⟩, -, close, prec⟩ := (accepts_enc_iff _ _ _ _ _).1 accepted
  exact ⟨(cast_mem_contactSet_iff n).not.2 hn, hκ, abs_sub_lt_exp_of_tests close prec window⟩

/-- At an ordinary integer the same precision program accepts every nonzero shift. -/
theorem closeAt_complete
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value T)
    (n κ : ℤ) (hn : (n : ℚ) ∉ contactSet) (hκ : κ ≠ 0) :
    CloseAt T (iota n) (iota κ) (n : ℚ) := by
  have hnC : n ∉ contacts := (cast_mem_contactSet_iff n).not.1 hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hnC (by decide)
  set B := bound n κ
  have h4 : (0 : ℝ) < 4 ^ B := by positivity
  obtain ⟨l, hl, hεl⟩ := exists_epsIdx_lt (θ := ((4 : ℝ) ^ B)⁻¹ / 4) (by positivity)
  have hladm : Admissible (l : ℤ) := admissible_of_ne_zero (by omega)
  have hε : (0 : ℝ) < epsIdx l := by exact_mod_cast epsIdx_pos hladm
  obtain ⟨a, ha, hr⟩ := exists_rRatio_close hn0 hε
  have hclose : |rRatio a (n * a) - n| < epsIdx l := by exact_mod_cast hr
  have hprec : 4 * epsIdx l * 4 ^ B < 1 := by
    have : 4 * (epsIdx l : ℝ) * 4 ^ B < 1 := by
      calc 4 * (epsIdx l : ℝ) * 4 ^ B < 4 * (((4 : ℝ) ^ B)⁻¹ / 4) * 4 ^ B := by gcongr
        _ = 1 := by field_simp
    exact_mod_cast this
  refine (closeAt_iff hM _ _ _).2 ⟨n, κ, a, l, rfl, rfl,
    (accepts_enc_iff _ _ _ _ _).2 ⟨⟨hnC, hκ, by omega, by omega, rfl⟩,
      ⟨hladm, admissible_of_ne_zero (by omega), admissible_of_ne_zero (mul_ne_zero hn0 (by omega))⟩,
      hclose, hprec⟩, by rw [abs_sub_comm]; exact hclose⟩

/-- The divisibility at shift `κ` bounds the height at the precision shift `m * κ`. -/
theorem height_le_scaled_bound {m : ℕ}
    (height : ∀ t : ℚ, t ∉ contactSet →
      ratHeight t ≤ (m : ℝ) * (contactSupport Mult.S_mul t : ℝ) ^ 24)
    {n κ : ℤ} {t : ℚ} (hn : (n : ℚ) ∉ contactSet) (localTest : Test n κ t) :
    ratHeight t ≤ (bound n ((m : ℤ) * κ) : ℝ) := by
  have hF : sixF n ≠ 0 := fun h =>
    hn ((cast_mem_contactSet_iff n).2 ((sixF_eq_zero_iff n).1 h))
  have hpos := Int.natAbs_pos.mpr (mul_ne_zero localTest.1 hF)
  have hs : contactSupport Mult.S_mul t ≤ (κ * sixF n).natAbs :=
    Nat.le_of_dvd hpos ((contactSupport_dvd_of_subset Mult.heightPrimes_subset_S_mul t).trans
      (test_dvd localTest))
  have hA : 1 ≤ A0 := A0_pos
  have hm : m ≤ A0 * m ^ 24 := calc
    m ≤ m ^ 24 := Nat.le_self_pow (by decide) m
    _ = 1 * m ^ 24 := (one_mul _).symm
    _ ≤ A0 * m ^ 24 := Nat.mul_le_mul_right _ hA
  have hbound : m * (contactSupport Mult.S_mul t) ^ 24 ≤ bound n ((m : ℤ) * κ) := by
    rw [bound, mul_assoc (m : ℤ) κ, Int.natAbs_mul, Int.natAbs_natCast, mul_pow, ← Nat.mul_assoc]
    exact Nat.mul_le_mul hm (Nat.pow_le_pow_left hs _)
  exact (height t localTest.2.1).trans (by exact_mod_cast hbound)

/-- The two shifts `κ` and `m * κ` are related by fixed scalar multiplication on the point
codes. Their joint relation recovers all integers outside the six exceptional constants. -/
theorem main_iff
    (hM : MultiplicationExact specConstructors FixedConst.cstar.value FixedConst.ell.value T)
    (hPC : PoleCompleteness) {m : ℕ} (hm : 1 ≤ m)
    (height : ∀ t : ℚ, t ∉ contactSet →
      ratHeight t ≤ (m : ℝ) * (contactSupport Mult.S_mul t : ℝ) ^ 24)
    (N : Fin 5 → ℚ) (t : ℚ) :
    (∃ K K' : Fin 5 → ℚ,
      (valueTestTemplate specConstructors FixedConst.cstar.value FixedConst.ell.value T).Rel
        (Fin.append (Fin.append N K) ![t]) ∧
      (scalarTemplate specConstructors (m : ℤ)).Rel (Fin.append K K') ∧
      CloseAt T N K' t) ↔
    ∃ n : ℤ, N = iota n ∧ t = (n : ℚ) ∧ (n : ℚ) ∉ contactSet := by
  have hm' : 1 ≤ (m : ℤ) := by exact_mod_cast hm
  constructor
  · rintro ⟨K, K', tested, scaled, close⟩
    obtain ⟨n, κ, rfl, rfl, localTest⟩ := (valueTest_rel_iff hM _ _ _).1 tested
    obtain rfl := (scalarTemplate_rel_iff_iota specConstructors rfl hm' κ K').1 scaled
    obtain ⟨hn, -, dist⟩ := closeAt_sound hM close
    have height' := height_le_scaled_bound height hn localTest
    exact ⟨n, rfl, eq_int_of_real_abs_sub_lt_exp_neg_of_height_le t n _ height' dist, hn⟩
  · rintro ⟨n, rfl, rfl, hn⟩
    obtain ⟨κ, hκ, localTest⟩ := test_complete hPC n hn
    refine ⟨iota κ, iota ((m : ℤ) * κ), (valueTest_rel_iff hM _ _ _).2 ?_,
      (scalarTemplate_rel_iff_iota specConstructors rfl hm' κ _).2 rfl,
      closeAt_complete hM _ _ hn (mul_ne_zero (by omega) hκ)⟩
    exact ⟨n, κ, rfl, rfl, localTest⟩

end ZOverQ.Qualitative

#print axioms ZOverQ.Qualitative.closeAt_iff
#print axioms ZOverQ.Qualitative.height_le_scaled_bound
#print axioms ZOverQ.Qualitative.main_iff
