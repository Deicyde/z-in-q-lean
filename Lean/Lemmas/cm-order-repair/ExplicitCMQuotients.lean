import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! The elliptic curves attached to the two auxiliary even sextics. All
four j-invariants below are Mathlib Weierstrass j-invariants over ℂ. -/
namespace ZInQBlueprint.CMRepair
noncomputable section

def cubicQuotient (a b c d : ℂ) : WeierstrassCurve ℂ := ⟨0,b,0,a*c,a^2*d⟩

theorem cubic_change (a b c d x y : ℂ) (hy : y^2 = a*x^3+b*x^2+c*x+d) :
    (a*y)^2 = (a*x)^3+b*(a*x)^2+(a*c)*(a*x)+a^2*d := by linear_combination a^2*hy

theorem quartic_reciprocal (a b c d t z : ℂ) (ht : t ≠ 0)
    (hz : z^2 = t*(a*t^3+b*t^2+c*t+d)) :
    (z/t^2)^2 = d*(1/t)^3+c*(1/t)^2+b*(1/t)+a := by
  field_simp
  linear_combination hz

def elliptic19 (v : ℂ) : WeierstrassCurve ℂ :=
  cubicQuotient 2 (-3*(1+9*v)) (-3*(1-9*v)) 2

def elliptic24 (w : ℂ) : WeierstrassCurve ℂ :=
  cubicQuotient (1+w) (-3*(7-3*w)) (-3*(7+3*w)) (1-w)

structure HasEllipticJ (E : WeierstrassCurve ℂ) (j : ℂ) : Prop where
  elliptic : E.IsElliptic
  value : @WeierstrassCurve.j ℂ _ E elliptic = j

private theorem value_of_invariants (E : WeierstrassCurve ℂ) (j : ℂ) (d : E.Δ ≠ 0)
    (h : E.c₄^3 = E.Δ*j) : HasEllipticJ E j := by
  let _ : E.IsElliptic := ⟨isUnit_iff_ne_zero.mpr d⟩
  refine ⟨inferInstance, ?_⟩
  rw [WeierstrassCurve.j_eq, h]
  field_simp

theorem quotient19_j (v : ℂ) (hv : v^2 = -19) : HasEllipticJ (elliptic19 v) (-(96^3)) := by
  have delta : (elliptic19 v).Δ = 12230590464 := by
    unfold elliptic19 cubicQuotient WeierstrassCurve.Δ WeierstrassCurve.b₂
      WeierstrassCurve.b₄ WeierstrassCurve.b₆ WeierstrassCurve.b₈
    linear_combination (34012224*v^2-643712832)*hv
  have c4 : (elliptic19 v).c₄ = -221184 := by
    unfold elliptic19 cubicQuotient WeierstrassCurve.c₄ WeierstrassCurve.b₂ WeierstrassCurve.b₄
    linear_combination 11664*hv
  apply value_of_invariants
  · rw [delta]
    norm_num
  · rw [delta,c4]
    norm_num

theorem quotient24_j (w : ℂ) (hw : w^2 = 2) :
    HasEllipticJ (elliptic24 w) (1728*(1399-988*w)) := by
  have delta : (elliptic24 w).Δ = 14155776*w+21233664 := by
    unfold elliptic24 cubicQuotient WeierstrassCurve.Δ WeierstrassCurve.b₂
      WeierstrassCurve.b₄ WeierstrassCurve.b₆ WeierstrassCurve.b₈
    linear_combination (221184*w^4+442368*w^3+1548288*w^2+2654208*w+8404992)*hw
  have c4 : (elliptic24 w).c₄ = 11520-4608*w := by
    unfold elliptic24 cubicQuotient WeierstrassCurve.c₄ WeierstrassCurve.b₂ WeierstrassCurve.b₄
    linear_combination 1728*hw
  apply value_of_invariants
  · rw [delta]
    intro z
    have root : w = -(3:ℂ)/2 := by linear_combination z/14155776
    rw [root] at hw
    norm_num at hw
  · rw [delta,c4]
    linear_combination (24901482184704-97844723712*w)*hw

/-- Reversing each quotient cubic conjugates its coefficients by v↦−v or w↦−w. -/
theorem four_elliptic_quotients (v w : ℂ) (hv : v^2 = -19) (hw : w^2 = 2) :
    HasEllipticJ (elliptic19 v) (-(96^3)) ∧ HasEllipticJ (elliptic19 (-v)) (-(96^3)) ∧
    HasEllipticJ (elliptic24 w) (1728*(1399-988*w)) ∧
    HasEllipticJ (elliptic24 (-w)) (1728*(1399+988*w)) := by
  refine ⟨quotient19_j v hv, quotient19_j (-v) (by simpa using hv), quotient24_j w hw, ?_⟩
  simpa using quotient24_j (-w) (by simpa using hw)

end
end ZInQBlueprint.CMRepair
#print axioms ZInQBlueprint.CMRepair.cubic_change
#print axioms ZInQBlueprint.CMRepair.quartic_reciprocal
#print axioms ZInQBlueprint.CMRepair.four_elliptic_quotients
