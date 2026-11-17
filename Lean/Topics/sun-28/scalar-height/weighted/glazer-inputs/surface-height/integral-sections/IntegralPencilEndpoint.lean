import HermitianPencil
import PencilComparison
import CMProjection
import MarkedMetric

namespace ZInQBlueprint.IntegralSections
open Height Sun28 Sun28.Ordinary Sun28.FiveMarkUnits Sun28.HeightFibres
open ZInQBlueprint.DiamondHeight ZInQBlueprint.WildLevel ZInQBlueprint.CMPeriods
noncomputable section
set_option exponentiation.threshold 350
set_option maxRecDepth 2200

/-- Both new numerators have size at most 75 times the actual archimedean mass function. -/
theorem pencil_norms (z : ℂ) :
    ‖75*z‖ ≤ 75*FiveMetric.mass z ∧ ‖32*(z+343)‖ ≤ 75*FiveMetric.mass z := by
  have bound (i : Fin 4) : FiveMetric.radius z i ≤ FiveMetric.mass z := by
    have h:=Finset.single_le_sum (f:=FiveMetric.radius z) (fun j _ => norm_nonneg _)
      (Finset.mem_univ i)
    unfold FiveMetric.mass
    linarith
  have a:= bound 0
  have b:= bound 3
  have pos : 0≤FiveMetric.mass z := (norm_nonneg _).trans a
  norm_num [FiveMetric.radius, FiveMetric.mark] at a b
  rw [norm_mul,norm_mul]
  norm_num
  constructor <;> linarith

/-- Evaluate the two specified integral sections in the same Hodge fibre that supplies the
quotient or the CM periods. The bundle comparison and its evaluation still require geometry. -/
def PencilFibres (C : ℝ) : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i, oldForm i A B≠0) →
    ∃ h : ℝ, logHeight₁ (pencilRatio ((A:ℚ)/B)) ≤
        2*h+2*Real.log Real.pi+Real.log 210+Real.log (8192*75) ∧
      (let R:=heightRadical A B
       (∃ F : QuotientFibre R h, (F.level:ℝ)≤C*(R:ℝ)^2) ∨ Nonempty (PeriodPresentation h))

theorem marked_fibres_of_pencil {C K : ℝ} (hK : 27≤K) (input : PencilFibres C) :
    MarkedFibres C K := by
  intro A B primitive off
  obtain ⟨h,metric,branch⟩:=input A B primitive off
  have nb : B≠0 := off 0
  have n4 : 32*A+343*B≠0 := off 4
  have live : 32*((A:ℚ)/B)+343≠0 := by
    intro z
    have qb : (B:ℚ)≠0 := by exact_mod_cast nb
    field_simp [qb] at z
    exact n4 (by exact_mod_cast (show 32*(A:ℚ)+343*(B:ℚ)=0 by linear_combination z))
  have slope := height_from_pencil ((A:ℚ)/B) live h metric
  rw [signed_height nb primitive] at slope
  exact ⟨h, by linarith only [slope, hK, le_max_right (0:ℝ) h],branch⟩

theorem one_sign_of_pencil (table : SmallClassDiscriminants)
    (fibres : PencilFibres (210^300)) (points : JointSelectedMenus)
    (x:ℚ) : (∃ w: Fin 28→ℚ, Sun28.eval28 Sun28.MultiplierChoice.oneSignPolynomial x w=0) ↔
      ∃ k:ℤ,x=(k:ℚ) :=
  one_sign_of_periods table (marked_fibres_of_pencil (by norm_num) fibres) points x

/-- Local realizations needed at a single slope. The line and the two sections are represented
by the lattice of their integral evaluations. -/
structure EvaluatedFibre (s:ℚ) (h:ℝ) where
  sectionModule : Type
  embeddings : Type
  additive : AddCommGroup sectionModule
  finite : Fintype embeddings
  inhabited : Nonempty embeddings
  data : letI := additive
         letI := finite
         DegreeData sectionModule embeddings
  first : sectionModule
  second : sectionModule
  second_live : letI:=additive; second ≠ 0
  ratio : letI:=additive
          (↑(pencilRatio s).den : ℤ) • first = (pencilRatio s).num • second
  kodairaSpencer : data.height = 2*h+2*Real.log Real.pi+Real.log 210
  petersson : ∀ i, data.normAt i first ≤ 8192*75 ∧ data.normAt i second ≤ 8192*75

/-- Evaluation and Kodaira–Spencer give the required marked-pencil height without a finite
height assumption for the image coordinate. -/
theorem EvaluatedFibre.comparison {s:ℚ} {h:ℝ} (F:EvaluatedFibre s h) :
    logHeight₁ (pencilRatio s) ≤ 2*h+2*Real.log Real.pi+Real.log 210+Real.log (8192*75) := by
  let := F.additive
  let := F.finite
  let := F.inhabited
  rw [← F.kodairaSpencer]
  exact pencil_evaluation F.data (pencilRatio s) F.first F.second F.second_live F.ratio F.petersson

def ActualPencilFibres (C : ℝ) : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i, oldForm i A B≠0) →
    ∃ h : ℝ, Nonempty (EvaluatedFibre ((A:ℚ)/B) h) ∧
      (let R:=heightRadical A B
       (∃ F : QuotientFibre R h, (F.level:ℝ)≤C*(R:ℝ)^2) ∨ Nonempty (PeriodPresentation h))

theorem pencil_fibres_of_evaluations {C:ℝ} (actual : ActualPencilFibres C) : PencilFibres C := by
  intro A B cop off
  obtain ⟨h,⟨F⟩,c⟩:=actual A B cop off
  exact ⟨h,F.comparison,c⟩

theorem one_sign_of_evaluations (table : SmallClassDiscriminants)
    (fibres : ActualPencilFibres (210^300)) (points : JointSelectedMenus) (x:ℚ) :
    (∃ w: Fin 28→ℚ, Sun28.eval28 Sun28.MultiplierChoice.oneSignPolynomial x w=0) ↔
      ∃ k:ℤ,x=(k:ℚ) :=
  one_sign_of_pencil table (pencil_fibres_of_evaluations fibres) points x

end
end ZInQBlueprint.IntegralSections
#print axioms ZInQBlueprint.IntegralSections.pencil_norms
#print axioms ZInQBlueprint.IntegralSections.marked_fibres_of_pencil
#print axioms ZInQBlueprint.IntegralSections.one_sign_of_pencil
#print axioms ZInQBlueprint.IntegralSections.EvaluatedFibre.comparison
#print axioms ZInQBlueprint.IntegralSections.pencil_fibres_of_evaluations
#print axioms ZInQBlueprint.IntegralSections.one_sign_of_evaluations
