import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! The covolume change of the two geometric differentials on a sextic under
the change z=1/(x-r), w=y/(s(x-r)^3). -/
namespace ZInQBlueprint.ArchimedeanHeight
noncomputable section
open MeasureTheory
abbrev PeriodSpace := Fin 2 → ℂ

def differentialChange (r s : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![s*r, -s; -s, 0]

theorem basis_change_rows (r s x y : ℂ) (h : x ≠ r) (hs : s ≠ 0) (hy : y ≠ 0) :
    let z := (x-r)⁻¹
    let w := y/(s*(x-r)^3)
    Matrix.mulVec (differentialChange r s) ![(2*y)⁻¹,x/(2*y)] =
      ![-(x-r)⁻¹^2/(2*w), z*(-(x-r)⁻¹^2)/(2*w)] := by
  dsimp
  ext i
  fin_cases i <;>
    simp [differentialChange, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    (field_simp [sub_ne_zero.mpr h, hs,hy]; try ring)

theorem differential_det (r s : ℂ) : (differentialChange r s).det = -s^2 := by
  simp [differentialChange,Matrix.det_fin_two]
  ring

def realChange (r s : ℂ) : PeriodSpace →ₗ[ℝ] PeriodSpace :=
  ((differentialChange r s).toLin').restrictScalars ℝ

theorem real_det_change (r s : ℂ) : |LinearMap.det (realChange r s)| = ‖s‖^4 := by
  rw [realChange,LinearMap.det_restrictScalars,LinearMap.det_toLin',differential_det,
    Algebra.norm_complex_apply,abs_of_nonneg (Complex.normSq_nonneg _),Complex.normSq_eq_norm_sq,
    norm_neg,norm_pow]
  ring

/-- Covolume of two arbitrary rank-four lattices whose columns are related by
the differential coordinate change; this is Mathlib's Haar covolume. -/
theorem covolume_change (r s : ℂ) (L L' : Submodule ℤ PeriodSpace)
    [DiscreteTopology L] [DiscreteTopology L'] [IsZLattice ℝ L] [IsZLattice ℝ L']
    (b : Module.Basis (Fin 4) ℤ L) (b' : Module.Basis (Fin 4) ℤ L')
    (b₀ : Module.Basis (Fin 4) ℝ PeriodSpace)
    (μ : Measure PeriodSpace) [μ.IsAddHaarMeasure]
    (transforms : ∀ i, (b' i : PeriodSpace) = realChange r s (b i : PeriodSpace)) :
    ZLattice.covolume L' μ = ‖s‖^4*ZLattice.covolume L μ := by
  rw [ZLattice.covolume_eq_det_mul_measureReal L' μ b' b₀,
    ZLattice.covolume_eq_det_mul_measureReal L μ b b₀]
  have e : ((↑) ∘ b' : Fin 4 → PeriodSpace) =
      (realChange r s) ∘ ((↑) ∘ b : Fin 4 → PeriodSpace) := funext transforms
  rw [e,b₀.det_comp,abs_mul,real_det_change,mul_assoc]

end
end ZInQBlueprint.ArchimedeanHeight
#print axioms ZInQBlueprint.ArchimedeanHeight.basis_change_rows
#print axioms ZInQBlueprint.ArchimedeanHeight.differential_det
#print axioms ZInQBlueprint.ArchimedeanHeight.real_det_change
#print axioms ZInQBlueprint.ArchimedeanHeight.covolume_change
