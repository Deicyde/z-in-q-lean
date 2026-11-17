import QuotientElliptic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

namespace Sun28.GlobalSections
noncomputable section

theorem affine_equation_iff (r x y : ℚ) : (curve r).toAffine.Equation x y ↔ equation r x y := by
  rw [WeierstrassCurve.Affine.equation_iff]
  simp only [curve, zero_mul, add_zero]
  unfold equation
  ring_nf

theorem elliptic_of_regular {r : ℚ} (hp:0<r) (hs:r<1) : (curve r).IsElliptic := by
  constructor
  rw [curve_discriminant,isUnit_iff_ne_zero]
  have b:0<rightRoot r:=by unfold rightRoot;positivity
  have c:0<leftRoot r:=by unfold leftRoot;positivity [sq_pos_of_ne_zero (sub_ne_zero.mpr hs.ne)]
  positivity

def sectionX (r:ℚ) := lead r
def sectionY (r:ℚ) := 4*r*lead r
def twiceX (r:ℚ) := (r-1)^2
def twiceY (r:ℚ) := 4*(r+1)*(r-1)^2
def fourX (r:ℚ) := ((r^2+4*r+1)/(r+1))^2

theorem section_on_curve (r:ℚ) : equation r (sectionX r) (sectionY r) := by
  unfold equation sectionX sectionY lead rightRoot leftRoot;ring

theorem twice_on_curve (r:ℚ) : equation r (twiceX r) (twiceY r) := by
  unfold equation twiceX twiceY rightRoot leftRoot;ring

def doubleX (r x y:ℚ) :=
  ((3*x^2+2*(rightRoot r+leftRoot r)*x+rightRoot r*leftRoot r)/(2*y))^2
    -(rightRoot r+leftRoot r)-2*x

theorem mathlib_doubleX {r x y:ℚ} (hn:y≠0) :
    (curve r).toAffine.addX x x ((curve r).toAffine.slope x x y y)=doubleX r x y := by
  rw [WeierstrassCurve.Affine.slope_of_Y_ne' (by change ¬ y = -y-0*x-0; intro h; apply hn;linarith)]
  unfold WeierstrassCurve.Affine.addX doubleX
  change _^2+0*_- (rightRoot r+leftRoot r)-x-x=_
  simp only [curve,zero_mul,sub_zero,add_zero,sub_neg_eq_add]
  rw [show y+y=2*y by ring]
  ring

theorem double_section {r:ℚ} (hp:0<r) (hs:r<1) :
    doubleX r (sectionX r) (sectionY r)=twiceX r := by
  have h1 : r-1≠0 := sub_ne_zero.mpr hs.ne
  have h3 : r+3≠0 := by linarith
  unfold doubleX sectionX sectionY twiceX lead leftRoot rightRoot
  field_simp [hp.ne',h1,h3];ring

theorem four_section {r:ℚ} (hp:0<r) (hs:r<1) :
    doubleX r (twiceX r) (twiceY r)=fourX r := by
  have h1 : r-1≠0 := sub_ne_zero.mpr hs.ne
  have h2 : r+1≠0 := by linarith
  unfold doubleX twiceX twiceY fourX leftRoot rightRoot
  field_simp [h1,h2];ring

theorem strict_abscissae {r:ℚ} (hp:0<r) (hs:r<1) :
    sectionX r<0 ∧ 0<twiceX r ∧ twiceX r<fourX r := by
  have pos:0<r+1:=by linarith
  have abs:0<1-r:=by linarith
  have gap:1-r<(r^2+4*r+1)/(r+1):=by
    rw [lt_div_iff₀ pos]
    nlinarith [sq_nonneg r]
  refine ⟨mul_neg_of_neg_of_pos (sub_neg.mpr hs) (by linarith : 0<r+3),
    sq_pos_of_ne_zero (sub_ne_zero.mpr hs.ne),?_⟩
  unfold twiceX fourX
  rw [show (r-1)^2=(1-r)^2 by ring]
  exact pow_lt_pow_left₀ gap abs.le (by decide)

end
end Sun28.GlobalSections

#print axioms Sun28.GlobalSections.affine_equation_iff
#print axioms Sun28.GlobalSections.elliptic_of_regular
#print axioms Sun28.GlobalSections.section_on_curve
#print axioms Sun28.GlobalSections.twice_on_curve
#print axioms Sun28.GlobalSections.mathlib_doubleX
#print axioms Sun28.GlobalSections.double_section
#print axioms Sun28.GlobalSections.four_section
#print axioms Sun28.GlobalSections.strict_abscissae
