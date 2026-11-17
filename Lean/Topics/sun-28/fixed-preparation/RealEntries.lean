import FixedBounds
import PaperScales

/-! Real sizes of the entries in the actual scalar tree. -/
namespace Sun28.FixedPreparation
open WeierstrassCurve.Affine ZInQ ZInQ.Mult Sun28.Forward Sun28.WitnessIndices Sun28.Ordinary Sun28.Scalar Sun28.ScalarHeight
noncomputable section

theorem quadratic_components (u : K0) (p : |K0.embPlus u|≤1) (m : |K0.embMinus u|≤1) :
    |u.re|≤1 ∧ |u.im|≤1 := by
  rw [K0.embPlus_apply,abs_le] at p
  rw [K0.embMinus_apply,abs_le] at m
  have s : (1:ℝ)≤Real.sqrt 2 := by
    have := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    nlinarith [Real.sqrt_nonneg 2]
  have c : |(u.re:ℝ)|≤1 ∧ |(u.im:ℝ)|≤1 := by
    refine ⟨abs_le.mpr ⟨by linarith [p.1,m.1],by linarith [p.2,m.2]⟩,?_⟩
    apply abs_le.mpr
    constructor
    · by_contra! h
      nlinarith [mul_le_mul_of_nonpos_left s (by linarith : (u.im:ℝ)≤0)]
    · by_contra! h
      nlinarith [mul_le_mul_of_nonneg_left s (by linarith : (0:ℝ)≤u.im)]
  exact_mod_cast c

theorem inverse_abscissa (m : ℤ) (σ : K0 →+* ℝ) (e : 1≤σ delta) :
    |σ (reciprocal (m • paperGenerator sqrt2_sq))|≤1 := by
  by_cases zero : m=0
  · subst m
    simp [Point.zero_def,reciprocal]
  have id : reciprocal (m • paperGenerator sqrt2_sq)=(indexX m)⁻¹ := by
    rw [indexX_paper,inv_inv]
  rw [id,map_inv₀,abs_inv]
  exact inv_le_one_of_one_le₀ ((e.trans (generator_real_lower σ e zero)).trans (le_abs_self _))

theorem real_entries {w : NinePoints} {M : ℕ} {c : ℤ} {a : Labels} (rep : Consequences w M c a)
    (small : ∀ σ : K0 →+* ℝ, (σ=K0.embPlus ∨ σ=K0.embMinus) →
      |σ (parameter (scalarEquiv (scalarPoint w M)))|≤|σ (parameter (scalarEquiv w.H))|) :
    ∀ i, |scalarEntries w M i|≤1 := by
  classical
  let H := scalarEquiv w.H
  let R := scalarEquiv (scalarPoint w M)
  have h : H=a.h • paperGenerator sqrt2_sq := by
    dsimp [H]; rw [←rep.represented.h_point,scalar_index]
  have r : R=(a.n 1-1) • paperGenerator sqrt2_sq := by
    dsimp [R]; rw [←rep.scalar_point,scalar_index]
  have invH := quadratic_components (reciprocal H) (h ▸ inverse_abscissa a.h _ embPlus_delta_mem.1)
    (h ▸ inverse_abscissa a.h _ embMinus_delta_mem.1)
  have invR := quadratic_components (reciprocal R) (r ▸ inverse_abscissa (a.n 1-1) _ embPlus_delta_mem.1)
    (r ▸ inverse_abscissa (a.n 1-1) _ embMinus_delta_mem.1)
  have val (σ : K0 →+* ℝ) (mem : σ=K0.embPlus ∨ σ=K0.embMinus) :
      |σ (parameter R/parameter H)|≤1 := by
    rw [map_div₀,abs_div]
    exact div_le_one_of_le₀ (small σ mem) (abs_nonneg _)
  have ratio := quadratic_components (parameter R/parameter H) (val _ (by simp)) (val _ (by simp))
  intro i
  fin_cases i
  · exact invH.1
  · exact invH.2
  · exact invR.1
  · exact invR.2
  · exact ratio.1
  · exact ratio.2

theorem scalar_size_at_points {w : NinePoints} {M : ℕ} {c : ℤ} {a : Labels} (rep : Consequences w M c a)
    (r δ : ℚ) (large : 1≤|r|) (sgn : δ*r=|r|)
    (small : ∀ σ : K0 →+* ℝ, (σ=K0.embPlus ∨ σ=K0.embMinus) →
      |σ (parameter (scalarEquiv (scalarPoint w M)))|≤|σ (parameter (scalarEquiv w.H))|)
    (live : scalarTree r (scalarEntries w M)≠0) :
    0<signedValue r δ gamma denominator (scalarTree r (scalarEntries w M)) ∧
    signedValue r δ gamma denominator (scalarTree r (scalarEntries w M))<1/2 :=
  scalar_real_preparation r _ _ large sgn (real_entries rep small) live

end
end Sun28.FixedPreparation
#print axioms Sun28.FixedPreparation.quadratic_components
#print axioms Sun28.FixedPreparation.inverse_abscissa
#print axioms Sun28.FixedPreparation.real_entries
#print axioms Sun28.FixedPreparation.scalar_size_at_points
