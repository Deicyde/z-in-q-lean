import AlgebraicThetaPeriod
import Mathlib.NumberTheory.Height.Projectivization

/-! Euclidean Weil height as a function on projective space over a fixed number field. -/
namespace ZInQBlueprint.ThetaPeriod
open Height Height.AdmissibleAbsValues ThetaQuotient Real Function
noncomputable section
variable {K ι : Type*} [Field K] [NumberField K] [Fintype ι]

omit [NumberField K] in
private theorem sqrt_sum_smul (v : AbsoluteValue K ℝ) (x : ι → K) (a : K) :
    Real.sqrt (∑ i, v ((a • x) i)^2) = v a * Real.sqrt (∑ i, v (x i)^2) := by
  simp only [Pi.smul_apply,smul_eq_mul,map_mul,mul_pow,← Finset.mul_sum,
    Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (v.nonneg a)]

theorem euclideanHeight_smul (x : ι → K) {a : K} (ha : a ≠ 0) :
    euclideanHeight (a • x) = euclideanHeight x := by
  classical
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [smul_zero]
  have : Nonempty ι := (ne_iff.mp hx).nonempty
  have hax : a • x ≠ 0 := by simp [ha,hx]
  simp only [euclideanHeight,hx,hax,↓reduceIte,sqrt_sum_smul,Multiset.prod_map_mul]
  have hf (v : nonarchAbsVal (K := K)) :
      (⨆ i, v.val ((a • x) i)) = v.val a * (⨆ i, v.val (x i)) := by
    simp only [Pi.smul_apply,smul_eq_mul,map_mul]
    exact (mul_iSup_of_nonneg (v.val.nonneg a) (fun i => v.val (x i))).symm
  simp only [hf]
  rw [finprod_mul_distrib (by fun_prop) (by fun_prop),mul_mul_mul_comm,product_formula ha,one_mul]

/-- Euclidean at infinite places, ultrametric supremum at finite places. -/
def projectiveHeight (p : Projectivization K (ι → K)) : ℝ :=
  p.lift (fun r => euclideanHeight r.val) fun a b t he => by
    have ht : t ≠ 0 := by
      rintro rfl; exact a.prop (by simpa using he)
    rw [he,euclideanHeight_smul b.val ht]

theorem projectiveHeight_mk (x : ι → K) (hx : x ≠ 0) :
    projectiveHeight (Projectivization.mk K x hx) = euclideanHeight x := rfl

theorem chartHeight_eq_projectiveHeight (z : Tuple) (ha : ∀ i, IsAlgebraic ℚ (chart z i))
    (he : pct z ≠ 0) :
    letI := numberField (chart z) ha
    ∃ h : coordinates (chart z) ≠ 0, chartHeight z ha =
      projectiveHeight (Projectivization.mk (fieldOf (chart z)) (coordinates (chart z)) h) := by
  let _ := numberField (chart z) ha
  have hp : chart z (ThetaQuotient.evenIndices 0) = 1 := div_self (chart_pivot he)
  have hn : coordinates (chart z) ≠ 0 := by
    intro eq
    have h := congrArg (fun b : fieldOf (chart z) => (b:ℂ))
      (congrFun eq (ThetaQuotient.evenIndices 0))
    change chart z (ThetaQuotient.evenIndices 0) = 0 at h
    exact one_ne_zero (hp.symm.trans h)
  exact ⟨hn,rfl⟩

end
end ZInQBlueprint.ThetaPeriod
#print axioms ZInQBlueprint.ThetaPeriod.euclideanHeight_smul
#print axioms ZInQBlueprint.ThetaPeriod.projectiveHeight_mk
#print axioms ZInQBlueprint.ThetaPeriod.chartHeight_eq_projectiveHeight
