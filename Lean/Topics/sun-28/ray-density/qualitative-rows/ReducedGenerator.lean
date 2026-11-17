import SelectedReductionCounts

namespace Sun28.QualitativeRows
open ZInQ ZInQ.Mult Sun28.Scalar Sun28.ScalarTrace Sun28.Ordinary Sun28.Forward Sun28.WitnessIndices
open Sun28.SelectedTrace WeierstrassCurve WeierstrassCurve.Affine
noncomputable section
open private three_sub_nonzero from SelectedReductionCounts

def redX {p : ℕ} [Fact p.Prime] (z : ZMod p) : ZMod p := (57-28*z)/8
def redY {p : ℕ} [Fact p.Prime] (z : ZMod p) : ZMod p := (-660+417*z)/32

private theorem denominator {p : ℕ} [Fact p.Prime] (size : 65<p) (k : ℕ) (pos : 0<k) (bound : k≤32) :
    (k:ZMod p)≠0 := by
  intro h
  have h' := Nat.le_of_dvd pos ((ZMod.natCast_eq_zero_iff k p).mp h)
  omega

private theorem finite_elliptic {p : ℕ} [Fact p.Prime] (size : 65<p)
    {z : ZMod p} (sq : z^2=2) : (shortCurve (-(3-z)^2)).IsElliptic := by
  let _ : NeZero (2:ZMod p) := ⟨two_ne_zero_zmod (by omega)⟩
  exact shortCurve_isElliptic (neg_ne_zero.mpr (pow_ne_zero _ (three_sub_nonzero size sq)))

private theorem equation {p : ℕ} [Fact p.Prime] (size : 65<p) {z : ZMod p} (sq : z^2=2) :
    (shortCurve (-(3-z)^2)).toAffine.Equation (redX z) (redY z) := by
  have d8 : (8:ZMod p)≠0 := denominator size 8 (by decide) (by decide)
  have d32 : (32:ZMod p)≠0 := denominator size 32 (by decide) (by decide)
  rw [shortCurve_equation_iff]
  unfold redX redY
  field_simp [d8,d32]
  ring_nf
  simp only [show z^3=2*z by rw [pow_succ,sq],sq]
  ring

/-- Sun's actual published generator with its rational denominators reduced modulo p. -/
def reducedPoint {p : ℕ} [Fact p.Prime] (size : 65<p) {z : ZMod p} (sq : z^2=2) :
    (shortCurve (-(3-z)^2)).toAffine.Point := by
  let _ := finite_elliptic size sq
  exact Point.mk (equation size sq)

def pointPeriod {p : ℕ} [Fact p.Prime] (size : 65<p) {z : ZMod p} (sq : z^2=2) : ℕ :=
  addOrderOf (reducedPoint size sq)

theorem period_dvd {p : ℕ} [Fact p.Prime] (size : 65<p) {z : ZMod p} (sq : z^2=2) :
    pointPeriod size sq ∣ pointCount p (-(3-z)^2) := by
  let _:=finite_elliptic size sq
  rw [←card_point_shortCurve p]
  exact addOrderOf_dvd_natCard (reducedPoint size sq)

theorem period_pos {p : ℕ} [Fact p.Prime] (size : 65<p) {z : ZMod p} (sq : z^2=2) :
    0 < pointPeriod size sq := Nat.pos_of_dvd_of_pos (period_dvd size sq) (by unfold pointCount;omega)

end
end Sun28.QualitativeRows
#print axioms Sun28.QualitativeRows.reducedPoint
#print axioms Sun28.QualitativeRows.period_dvd
#print axioms Sun28.QualitativeRows.period_pos
