import ArchimedeanDescent
import FiniteHeightDescent
import ThetaQuotient

/-! Absolute logarithmic projective heights do not depend on the field of definition. -/
open NumberField Height
namespace ZInQBlueprint.HeightDescent
open ThetaQuotient
noncomputable section
variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
variable {ι : Type*} [Finite ι]

/-- Over rings of integers the two factors of the projective height scale by the same degree. -/
theorem mulHeight_integral (y : ι → 𝓞 K) :
    Height.mulHeight (fun i => algebraMap K L (y i)) =
      Height.mulHeight (fun i => (y i : K)) ^ Module.finrank K L := by
  by_cases h : y = 0
  · subst y
    simp
  have hx : (fun i => (y i:K)) ≠ 0 := by
    intro he
    apply h
    funext i
    exact RingOfIntegers.ext (congrFun he i)
  have hy : (fun i => algebraMap K L (y i)) ≠ 0 := by
    intro he
    apply hx
    funext i
    apply (algebraMap K L).injective
    simpa only [Pi.zero_apply,map_zero] using congrFun he i
  rw [NumberField.mulHeight_eq hy,NumberField.mulHeight_eq hx,mul_pow,archimedean_factors,finite_factors_map h]

/-- The multiplicative height before division by the field degree acquires [L:K] as exponent. -/
theorem mulHeight_algebraMap (x : ι → K) :
    Height.mulHeight (fun i => algebraMap K L (x i)) =
      Height.mulHeight x ^ Module.finrank K L := by
  classical
  obtain ⟨d,hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 K)) x
  choose y hy using hd
  let a : K := (d.val : K)
  have ha : a ≠ 0 := fun h => nonZeroDivisors.coe_ne_zero d (RingOfIntegers.ext h)
  have hal : algebraMap K L a ≠ 0 := (map_ne_zero (algebraMap K L)).mpr ha
  have hk : (fun i => (y i:K)) = a • x := by
    funext i
    exact hy i
  have hl : (fun i => algebraMap K L (y i)) = (algebraMap K L a) • (fun i => algebraMap K L (x i)) := by
    funext i
    change algebraMap K L (y i:K) = algebraMap K L a * algebraMap K L (x i)
    rw [← map_mul]
    exact congrArg _ (congrFun hk i)
  have h := mulHeight_integral (L:=L) y
  rwa [hk,hl,mulHeight_smul_eq_mulHeight _ ha,mulHeight_smul_eq_mulHeight _ hal] at h

/-- Division by the absolute degree gives the same projective height over each number field. -/
theorem normalizedHeight_algebraMap (x : ι → K) :
    normalizedHeight (fun i => algebraMap K L (x i)) = normalizedHeight x := by
  have : FiniteDimensional K L := FiniteDimensional.right ℚ K L
  have hn : (Module.finrank K L : ℝ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R:=K) (M:=L)).ne'
  unfold normalizedHeight
  rw [logHeight_eq_log_mulHeight,logHeight_eq_log_mulHeight,mulHeight_algebraMap,Real.log_pow,
    ← Module.finrank_mul_finrank ℚ K L,Nat.cast_mul]
  field_simp

omit [Algebra K L] in
/-- Transport of the normalized height along an arbitrary embedding of number fields. -/
theorem normalizedHeight_map (f : K →+* L) (x : ι → K) :
    normalizedHeight (fun i => f (x i)) = normalizedHeight x := by
  let : Algebra K L := f.toAlgebra
  exact normalizedHeight_algebraMap (L:=L) x

end
end ZInQBlueprint.HeightDescent
#print axioms ZInQBlueprint.HeightDescent.mulHeight_integral
#print axioms ZInQBlueprint.HeightDescent.mulHeight_algebraMap
#print axioms ZInQBlueprint.HeightDescent.normalizedHeight_algebraMap
#print axioms ZInQBlueprint.HeightDescent.normalizedHeight_map
