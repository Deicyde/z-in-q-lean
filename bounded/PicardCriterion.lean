import IntegerPolynomial
import ModuliHeight
import PicardSextic

/-! The remaining height and reduction statements for the Picard family imply
the integer-polynomial theorem. The same fibre height occurs in both bounds. -/

namespace ZOverQ.Qualitative.Picard

open ZInQ ZInQ.QualitativeHeight
open ZInQBlueprint.OriginalRank.PublishedGenusRows

/-- The rational coordinate of the Picard line in terms of its branch form. -/
noncomputable def chart (s : ℚ) : ℚ :=
  -64 * (branchForm s 1)^2 / (s^2+3)^6

theorem chart_change {t : ℚ} (ht : t ≠ 0) : chart (picardParameter t) = JHeight.Jmap t := by
  calc
    chart (picardParameter t) =
        (4/27) * (-432*(branchForm (picardParameter t) 1)^2 / ((picardParameter t)^2+3)^6) := by
      unfold chart; ring
    _ = _ := by rw [rational_shape ht]; ring

private theorem preimage_off_contacts {s : ℚ} (hs : s ≠ 5) (hb : primitiveBranch s ≠ 0) :
    let t := 120 / (s-5)
    t ∉ contactSet ∧ picardParameter t = s := by
  dsimp only
  have hd : s - 5 ≠ 0 := sub_ne_zero.mpr hs
  have hn : (120 / (s-5) : ℚ) ≠ 0 := div_ne_zero (by norm_num) hd
  have back : picardParameter (120 / (s-5)) = s := by unfold picardParameter; field_simp; ring
  refine ⟨?_, back⟩
  intro hc
  have z : Mult.contactPoly (120 / (s-5)) = 0 := by
    rw [Mult.contactPoly_eq_prod]
    exact Finset.prod_eq_zero hc (sub_self _)
  have eqn := branchForm_change hn (s.den : ℚ)
  rw [back, Rat.mul_den_eq_num, z, mul_zero, mul_zero] at eqn
  exact hb eqn

/-- The original degree-twelve height estimate and the quintic rational-root
bound give a comparison for this chart without a degree-sixty resultant. -/
theorem parameter_le_invariant {s : ℚ} (hs : s ≠ 5) (hb : primitiveBranch s ≠ 0) :
    ratHeight s ≤ ratHeight (igusaRatio (chart s)) +
      (450 + Real.log 1024 + ratHeight 5 + ratHeight 120 + ratHeight 0 + Real.log 3) := by
  let t := 120 / (s-5)
  obtain ⟨ht, he⟩ := preimage_off_contacts hs hb
  have hn : t ≠ 0 := div_ne_zero (by norm_num) (sub_ne_zero.mpr hs)
  have qchart : chart s = JHeight.Jmap t := he ▸ chart_change hn
  have grow : ratHeight s ≤ ratHeight 5 + (ratHeight 120 + ratHeight t) + ratHeight 0 + Real.log 3 := by
    rw [← he]
    calc
      ratHeight (picardParameter t) ≤ ratHeight 5 + ratHeight (120 / t) + ratHeight 0 + Real.log 3 := by
        simpa only [picardParameter, add_zero] using Mult.ratHeight_add3_le 5 (120 / t) 0
      _ ≤ _ := by linarith [Mult.ratHeight_div_le 120 t]
  rw [qchart]
  linarith [parameter_height_le_ratio t ht, Mult.ratHeight_nonneg t]

/-- For the rational GL₂-type factor, (6.7) of von Känel and a comparison
with the explicit sextic invariant yield the existential polynomial. Finite
exceptional parameters and all fixed bad primes are allowed. -/
theorem integer_polynomial_of_fibre_estimates (g : ℕ) (fixed : Finset ℕ) (except : Finset ℚ)
    (bad : ℚ → Finset ℕ) (fibreHeight : ℚ → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (fixedPrimes : ∀ p ∈ fixed, p.Prime)
    (support : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ∀ p ∈ bad s, p.Prime ∧ (p ∈ fixed ∨ Odd (padicValRat p (primitiveBranch s))))
    (effective : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      fibreHeight s ≤ vonKanelBound g (bad s))
    (comparison : ∀ s : ℚ, s ∉ except → primitiveBranch s ≠ 0 →
      ratHeight (igusaRatio (chart s)) ≤ a * max 1 (fibreHeight s) + b)
    (tian : PublishedTian47) (grossZagier : ZOverQ.Bounded.SimpleZeroRank) : IntegerPolynomial := by
  let D := 450 + Real.log 1024 + ratHeight 5 + ratHeight 120 + ratHeight 0 + Real.log 3
  have old {s : ℚ} (hs : s ∉ insert (5:ℚ) except) : s ∉ except := fun h => hs (Finset.mem_insert_of_mem h)
  obtain ⟨m, _, hm⟩ := exists_uniform_height_of_vonKanel g fixed (insert 5 except) bad fibreHeight
    (a := a) (b := b+D) ha fixedPrimes
    (fun s hs hb => support s (old hs) hb) (fun s hs hb => effective s (old hs) hb) (by
      intro s hs hb
      have h5 : s ≠ 5 := fun he => hs (Finset.mem_insert.mpr (Or.inl he))
      have h1 := parameter_le_invariant h5 hb
      have h2 := comparison s (old hs) hb
      dsimp only [D]
      linarith)
  exact integer_polynomial_of_uniform_height (C := (m : ℝ)) hm tian grossZagier

end ZOverQ.Qualitative.Picard

#print axioms ZOverQ.Qualitative.Picard.parameter_le_invariant
#print axioms ZOverQ.Qualitative.Picard.integer_polynomial_of_fibre_estimates
