import ResidualFactors
import CoarseConic
import Mathlib.Data.ZMod.Basic

/-! The homogeneous parameters of the rational sextic and their disjoint specializations. -/
namespace ZInQBlueprint.ClusterParameters
open ZInQBlueprint.ResidualFactors ZInQBlueprint.SixContact

theorem homogenize (A B : ℚ) (hB : B ≠ 0) :
    F (A/B)*B^6 = contactProduct A B ∧ G (A/B)*B^2 = poleForm A B := by
  unfold F G contactProduct poleForm
  constructor <;> field_simp

theorem rational_parameter (A B : ℚ) (hB : B ≠ 0) :
    CoarseConic.r (A/B) = 240*contactProduct A B/(poleForm A B)^3 := by
  obtain ⟨hf,hg⟩ := homogenize A B hB
  rw [← hf,← hg,CoarseConic.r]
  field_simp [hB, (positive_denominator (A/B)).ne']

variable {K : Type*} [Field K] [NeZero (2:K)] [NeZero (3:K)] [NeZero (5:K)]

private lemma coeff_ne_zero : (10800:K) ≠ 0 := by
  rw [show (10800:K) = 2^4*3^3*5^2 by norm_num]
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (NeZero.ne _)) (pow_ne_zero _ (NeZero.ne _)))
    (pow_ne_zero _ (NeZero.ne _))

/-- No projective zero of the contact polynomial is a pole in residue characteristic above five. -/
theorem separate_marks {A B : K} (hab : A ≠ 0 ∨ B ≠ 0) (hf : contactProduct A B=0) :
    poleForm A B ≠ 0 := by
  have hb : B ≠ 0 := by
    rintro rfl
    have hn : A ≠ 0 := hab.resolve_right (by simp)
    simp [contactProduct,hn] at hf
  intro g
  apply mul_ne_zero (coeff_ne_zero (K:=K)) (pow_ne_zero 2 hb)
  unfold poleForm at g
  simp only [contactProduct,mul_eq_zero] at hf
  rcases hf with (((((h|h)|h)|h)|h)|h)
  · rw [h] at g
    linear_combination 3*g
  · have ha : A = -15*B := by linear_combination h
    rw [ha] at g
    linear_combination 16*g
  · have ha : A = -20*B := by linear_combination h
    rw [ha] at g
    linear_combination 27*g
  · have ha : A = -24*B := by linear_combination h
    rw [ha] at g
    linear_combination 25*g
  · have ha : A = -30*B := by linear_combination h
    rw [ha] at g
    linear_combination 12*g
  · have ha : A = -60*B := by linear_combination h
    rw [ha] at g
    linear_combination 1*g

/-- For primes other than 7 a projective pole lies in the affine chart, away from all six marks. -/
theorem pole_units [NeZero (7:K)] {A B : K} (hab : A ≠ 0 ∨ B ≠ 0) (hg : poleForm A B=0) :
    B ≠ 0 ∧ contactProduct A B ≠ 0 := by
  refine ⟨?_,fun hf => separate_marks hab hf hg⟩
  rintro rfl
  have hn : A ≠ 0 := hab.resolve_right (by simp)
  simp [poleForm,hn,NeZero.ne (7:K)] at hg

theorem seven_pole : ∀ A B : ZMod 7, (A ≠ 0 ∨ B ≠ 0) → poleForm A B=0 →
    contactProduct A B = 1 ∨ contactProduct A B = -1 := by decide

theorem seven_cube : ∀ A B : ZMod 7, (A ≠ 0 ∨ B ≠ 0) → poleForm A B=0 →
    ∃ w : ZMod 7, w^3 = -3240*contactProduct A B ∧ w ≠ 0 := by decide

theorem seven_unity : (2:ZMod 7)^2+2+1=0 := by decide

end ZInQBlueprint.ClusterParameters
#print axioms ZInQBlueprint.ClusterParameters.homogenize
#print axioms ZInQBlueprint.ClusterParameters.rational_parameter
#print axioms ZInQBlueprint.ClusterParameters.separate_marks
#print axioms ZInQBlueprint.ClusterParameters.pole_units
#print axioms ZInQBlueprint.ClusterParameters.seven_pole
#print axioms ZInQBlueprint.ClusterParameters.seven_cube
#print axioms ZInQBlueprint.ClusterParameters.seven_unity
