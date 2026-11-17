import SeededScalarPoint
import Mathlib.Data.Nat.Squarefree

namespace Sun28.PointConstruction
open Sun28.TwistExtension Sun28.PairedClasses
noncomputable section

def positiveSeed : ℕ := 267706460779
def curveIndex : ℕ := 526361*positiveSeed

theorem positive_factors : positiveSeed=139*353*887*6151 ∧ curveIndex%12=11 ∧
    positiveSeed.Coprime (6*526361*526681) ∧ Squarefree curveIndex := by
  refine ⟨by decide,by decide,by decide,?_⟩
  have prime139 : Nat.Prime 139 := by norm_num
  have prime353 : Nat.Prime 353 := by norm_num
  have prime887 : Nat.Prime 887 := by norm_num
  have prime6151 : Nat.Prime 6151 := by norm_num
  have prime11 : Nat.Prime 11 := by norm_num
  have prime109 : Nat.Prime 109 := by norm_num
  have prime439 : Nat.Prime 439 := by norm_num
  rw [show curveIndex=11*(109*(439*(139*(353*(887*6151))))) by decide]
  simp only [Nat.squarefree_mul_iff]
  exact ⟨by decide,prime11.squarefree,by decide,prime109.squarefree,by decide,prime439.squarefree,
    by decide,prime139.squarefree,by decide,prime353.squarefree,by decide,prime887.squarefree,prime6151.squarefree⟩

theorem positive_quartic : (1352432734855870834408:ℚ)^2 =
    (positiveSeed:ℚ)*other*quartic mark 1893221 183 := by
  norm_num [positiveSeed,other,mark,quartic]

theorem positive_second_nonzero_ordinate :
    ∃ t y:ℚ,t≠0 ∧ y≠0 ∧
      y^2=(mark*t^2)*(mark*t^2-(mark*positiveSeed*other))*(mark*t^2+3*(mark*positiveSeed*other)) := by
  let w : ℚ := (positiveSeed:ℚ)*other/1352432734855870834408
  let D : ℚ := 1893221^2+3*mark*183^2
  use D*w,4*mark^2*1893221*183*D^2*w^3
  norm_num [mark,positiveSeed,other,w,D]

theorem positive_pair_iff :
    (Point mark (mark*positiveSeed) ∧ Point mark ((mark*positiveSeed)*other)) ↔
      SignedQuartic mark positiveSeed := by
  have firstEquiv:=signed_mark_iff (b:=mark) (q:=(positiveSeed:ℚ)) (by norm_num [mark]) (by norm_num [positiveSeed])
  obtain ⟨t,y,tn,_,eq⟩:=positive_second_nonzero_ordinate
  exact ⟨fun h=>firstEquiv.mp h.1,fun h=>⟨firstEquiv.mpr h,t,y,tn,eq⟩⟩

end
end Sun28.PointConstruction
#print axioms Sun28.PointConstruction.positive_factors
#print axioms Sun28.PointConstruction.positive_quartic
#print axioms Sun28.PointConstruction.positive_second_nonzero_ordinate
#print axioms Sun28.PointConstruction.positive_pair_iff
