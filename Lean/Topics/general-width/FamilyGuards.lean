import Mathlib.Tactic

/-! The two nonconstant leading coefficients used throughout the 222-coordinate
family. Coordinate numbers and residual numbers follow the one-based V15 table. -/
namespace FamilyWidth222

theorem detector_pivot (x x78 x79 x80 x81 x121 : ℚ)
    (r30 : x^2 - x78 = 0) (r31 : x78^2 - x79 = 0) (r72 : x*x79 - x121 = 0)
    (r32 : 7626746323592 - 76267463235920*x - 628059618995128*x*x78 +
      732473028362323*x*x121 + 307309842082151*x78 - 583791423311868*x78*x121 +
      718967979842546*x79 + 162308064100032*x79*x79 - 38129835686440*x79*x121 -
      7626746323592*x80 - 3813373161796*x80*x81 - 646146742577308*x121 +
      3813373161796*x121*x121 = 0)
    (r33 : 1 - 10*x - 120*x*x78 + 210*x*x121 + 45*x78 - 120*x78*x121 +
      210*x79 + 45*x79*x79 - 10*x79*x121 - x80 - x80*x81 - 252*x121 +
      x121*x121 = 0) : x80 ≠ 0 := by
  have e78 : x78 = x^2 := by linarith
  have e79 : x79 = x^4 := by rw [e78] at r31; linear_combination -r31
  have e121 : x121 = x^5 := by rw [e79] at r72; linear_combination -r72
  intro hz
  have power : (1-x)^10 = 0 := by
    rw [e78,e79,e121,hz] at r33
    linear_combination r33
  have hx : x = 1 := by
    have h : 1-x = 0 := by simpa using power
    linarith
  rw [e78,e79,e121,hx,hz] at r32
  norm_num at r32

def contact (x : ℚ) : ℚ := 51948354689656 + 28892074377045*x^2 +
  1634130961866*x^4 + 32365650141*x^6 + 216486432*x^8

theorem input_pivot (x x55 x107 x108 : ℚ)
    (r9 : 2501 + 51*x^2 - 51*x55 = 0)
    (r56 : 2601*x55*x55 - 4*x107 = 0)
    (r57 : 6316332 + 291790992*x55 + 15531948*x55*x107 + 5736060*x107 -
      512*x107*x107 + x108 = 0) : x108 = contact x ∧ 0 < 22201*x108+1 := by
  have e55 : x55 = x^2+2501/51 := by linarith
  have e107 : x107 = 2601*x55^2/4 := by linear_combination -r56/4
  have e108 : x108 = contact x := by
    rw [e107,e55] at r57
    unfold contact
    linear_combination r57
  refine ⟨e108, ?_⟩
  rw [e108]
  unfold contact
  positivity

end FamilyWidth222
#print axioms FamilyWidth222.detector_pivot
#print axioms FamilyWidth222.input_pivot
