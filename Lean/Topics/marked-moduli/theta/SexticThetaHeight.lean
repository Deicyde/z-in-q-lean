import SexticIgusaChart
import SexticI4
import SexticDiscriminant
import ThetaApplication

namespace ZInQBlueprint.SexticThetaHeight
open Polynomial IntegralSextic DirectCharts SexticIgusaChart SexticInvariants SixContact
noncomputable section

/-- The affine polynomial of the integral equation in the nonzero m-chart. -/
def sextic (u δ : ℚ) : ℚ[X] := C (scalar u δ) * monicSextic (parameter u)

theorem affine_equation {u : ℚ} (hu : u ∉ ZInQ.contactSet) (δ x : ℚ) :
    (sextic u δ).eval x = integralEquation δ (u.num:ℚ) (u.den:ℚ) x 1 := by
  rw [equation hu, sextic, eval_mul, eval_C, monic_eval]

theorem smooth_sextic {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) :
    (sextic u δ).natDegree = 6 ∧ (sextic u δ).discr ≠ 0 := by
  obtain ⟨ht,hs,hd,_⟩ := unmarked hu hδ
  constructor
  · exact (natDegree_C_mul hs).trans (monic_six (parameter u)).2
  · rw [sextic, discr_family _ _ hs]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hs))
      (pow_ne_zero _ ht)) (pow_ne_zero _ hd)

/-- Streng's third absolute invariant on the specified rational sextic. -/
theorem invariant {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) :
    igusaI4 (sextic u δ)^5 / (sextic u δ).discr^2 = 3779136 / J u := by
  obtain ⟨ht,hs,hd,hj⟩ := unmarked hu hδ
  rw [sextic, igusaI4_family, discr_family _ _ hs, hj]
  field_simp [ht,hs,hd]
  ring

/-- Period and height assertions for the same polarized Jacobian of the literal sextic.
The binary-form invariant on the right is determined by the coefficients. -/
structure PeriodData (K : Type) [Field K] [NumberField K] (u δ : ℚ) where
  coordinates : Fin 16 → K
  embedding : K →+* ℂ
  evenProduct : (∏ i, embedding (coordinates (ThetaQuotient.evenIndices i))) ≠ 0
  period : (∑ i, embedding (coordinates (ThetaQuotient.evenIndices i))^8)^5 /
    (∏ i, embedding (coordinates (ThetaQuotient.evenIndices i)))^4 =
    ((igusaI4 (sextic u δ)^5 / (sextic u δ).discr^2 : ℚ) : ℂ)
  stable : ℝ
  comparison : |max 1 (ThetaQuotient.euclideanHeight coordinates) - max 1 (stable + Real.log Real.pi)/2| ≤
    ThetaMetric.pazukiConstant *
      Real.log (min (max 1 (ThetaQuotient.euclideanHeight coordinates)) (max 1 (stable + Real.log Real.pi)) + 2)
  reduction : stable ≤ HeightBudget.vonKaenelBudget u

def thetaFibre {K : Type} [Field K] [NumberField K] {u δ : ℚ}
    (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) (f : PeriodData K u δ) : ThetaApplication.Fibre K u where
  coordinates := f.coordinates
  embedding := f.embedding
  evenProduct := f.evenProduct
  absoluteInvariant := by
    rw [f.period, invariant hu hδ]
    simp
  stable := f.stable
  comparison := f.comparison
  reductionBound := f.reduction

def HasSexticPeriods : Prop := ∀ u : ℚ, u ∉ ZInQ.contactSet →
  ∃ (δ : ℚ) (_ : δ ≠ 0) (K : Type) (_ : Field K) (_ : NumberField K), Nonempty (PeriodData K u δ)

theorem thetaFibres_of_periods (hp : HasSexticPeriods) : ThetaApplication.HasThetaFibres := by
  intro u hu
  obtain ⟨δ,hδ,K,_,_,⟨f⟩⟩ := hp u hu
  exact ⟨K,_,_,⟨thetaFibre hu hδ f⟩⟩

end
end ZInQBlueprint.SexticThetaHeight

#print axioms ZInQBlueprint.SexticThetaHeight.affine_equation
#print axioms ZInQBlueprint.SexticThetaHeight.smooth_sextic
#print axioms ZInQBlueprint.SexticThetaHeight.invariant
#print axioms ZInQBlueprint.SexticThetaHeight.thetaFibre
#print axioms ZInQBlueprint.SexticThetaHeight.thetaFibres_of_periods
