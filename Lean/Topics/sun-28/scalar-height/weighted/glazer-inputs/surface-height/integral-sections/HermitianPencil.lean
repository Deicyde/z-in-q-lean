import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! A height inequality for two integral sections whose projective ratio is rational. -/
namespace ZInQBlueprint.IntegralSections
open Height
noncomputable section

/-- A rational projective ratio gives a simultaneous primitive factor in any integer module. -/
theorem primitive_pair_section {M:Type*} [AddCommGroup M] (y:ℚ) (a b:M)
    (ratio : (y.den:ℤ) • a = y.num • b) :
    ∃ e:M, a=y.num • e ∧ b=(y.den:ℤ) • e := by
  obtain ⟨U,V,bez⟩ := Rat.isCoprime_num_den y
  refine ⟨U • a + V • b,?_,?_⟩
  · calc
      a = (U*y.num+V*(y.den:ℤ)) • a := by rw [bez,one_smul]
      _ = (U*y.num) • a+V • ((y.den:ℤ) • a) := by rw [add_smul,smul_smul]
      _ = (U*y.num) • a+V • (y.num • b) := by rw [ratio]
      _ = y.num • (U • a+V • b) := by simp only [smul_add,smul_smul];congr 1 <;> rw [mul_comm]
  · calc
      b = (U*y.num+V*(y.den:ℤ)) • b := by rw [bez,one_smul]
      _ = U • (y.num • b)+(V*(y.den:ℤ)) • b := by rw [add_smul,smul_smul]
      _ = U • ((y.den:ℤ) • a)+(V*(y.den:ℤ)) • b := by rw [ratio]
      _ = (y.den:ℤ) • (U • a+V • b) := by simp only [smul_add,smul_smul];congr 1 <;> rw [mul_comm]

/-- The absolute norms and degree of a rank-one Hermitian lattice, in the form required
for point evaluation. The degree inequality discards its nonnegative finite divisor. -/
structure DegreeData (M σ : Type*) [AddCommGroup M] [Fintype σ] where
  normAt : σ → M → ℝ
  norm_pos : ∀ i x, x≠0 → 0<normAt i x
  int_smul : ∀ i (z:ℤ) x, normAt i (z • x)=|(z:ℝ)| * normAt i x
  height : ℝ
  integral_degree : ∀ x:M, x≠0 → -(∑ i:σ,Real.log (normAt i x)) ≤ Fintype.card σ*height

/-- Exact archimedean averaging for rationally proportional integral evaluations. -/
theorem pencil_evaluation {M σ:Type*} [AddCommGroup M] [Fintype σ] [Nonempty σ]
    (H : DegreeData M σ) (y:ℚ) (a b:M) (bn:b≠0)
    (ratio : (y.den:ℤ) • a=y.num • b) {C:ℝ}
    (arch : ∀ i, H.normAt i a≤C ∧ H.normAt i b≤C) :
    logHeight₁ y ≤ H.height+Real.log C := by
  obtain ⟨e,ha,hb⟩:=primitive_pair_section y a b ratio
  have en : e≠0 := by intro z; apply bn;rw [hb,z,smul_zero]
  let h:ℝ:=max |(y.num:ℝ)| (y.den:ℝ)
  have ypos : 0<(y.den:ℝ) := by exact_mod_cast y.den_pos
  have hp : 0<h := ypos.trans_le (le_max_right _ _)
  have single (i:σ) : Real.log h+Real.log (H.normAt i e) ≤ Real.log C := by
    obtain ⟨ba,bb⟩:=arch i
    rw [ha,H.int_smul] at ba
    rw [hb,H.int_smul,Int.cast_natCast,abs_of_pos ypos] at bb
    rw [← Real.log_mul hp.ne' (H.norm_pos i e en).ne']
    apply Real.log_le_log (mul_pos hp (H.norm_pos i e en))
    dsimp [h]
    rcases le_total |(y.num:ℝ)| (y.den:ℝ) with le | le
    · simpa [max_eq_right le] using bb
    · simpa [max_eq_left le] using ba
  have sums:=Finset.sum_le_sum (s:=Finset.univ) (fun (i:σ) _ => single i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at sums
  have card : 0<(Fintype.card σ:ℝ) := by exact_mod_cast Fintype.card_pos
  have deg:=H.integral_degree e en
  have mul : (Fintype.card σ:ℝ)*Real.log h ≤ Fintype.card σ*(H.height+Real.log C) := by
    rw [mul_add]
    linarith only [sums,deg]
  have hy : logHeight₁ y = Real.log h := by
    rw [Rat.logHeight₁_eq_log_max]
    dsimp [h]
    push_cast
    congr 2
    norm_cast
    simp
  rw [hy]
  exact (mul_le_mul_iff_right₀ card).mp mul

end
end ZInQBlueprint.IntegralSections
#print axioms ZInQBlueprint.IntegralSections.primitive_pair_section
#print axioms ZInQBlueprint.IntegralSections.pencil_evaluation
