import GlueCover
import SixAffine

/-! The two affine schemes glue over the base field. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open ZInQBlueprint.IntegralSextic ZInQBlueprint.ResidualFactors ZInQBlueprint.GlobalTwist
open ZInQBlueprint.CurveChart

namespace ZInQBlueprint.BinaryCover

noncomputable section

private theorem map_integral {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (d a b x z : R) :
    φ (integralEquation d a b x z) = integralEquation (φ d) (φ a) (φ b) (φ x) (φ z) := by
  simp [integralEquation, form, alpha, beta, gamma, m, n, poleForm, map_ofNat]

private theorem hom_integral {R : Type*} [CommRing R] (d a b c x z : R) :
    integralEquation d a b (c*x) (c*z) = c^6 * integralEquation d a b x z := by
  rw [integralEquation, form_homogeneous, integralEquation]; ring

variable (K : Type) [Field K] [CharZero K]
local notation "L" => LaurentPolynomial K

theorem fixed_overlap (u : ℚ) : SexticOverlap K (fixed K u false) (fixed K u true) := by
  unfold SexticOverlap fixed
  simp only [Bool.false_eq_true, ite_false, ite_true, map_integral, map_one,
    toLaurent_C, toLaurent_X]
  change LaurentPolynomial.invert.toRingHom (integralEquation _ _ _ _ _) = _
  rw [map_integral]
  have HC (a : K) : LaurentPolynomial.invert.toRingHom (LaurentPolynomial.C a) =
      LaurentPolynomial.C a := LaurentPolynomial.invert_C a
  have HT : LaurentPolynomial.invert.toRingHom (LaurentPolynomial.T 1 : L) = LaurentPolynomial.T (-1) :=
    LaurentPolynomial.invert_T 1
  rw [HC, HC, HC, HT, map_one]
  let c : L := LaurentPolynomial.T (-1)
  let x : L := LaurentPolynomial.T 1
  have hcx : c*x=1 := by
    change LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 = (1 : L)
    rw [← LaurentPolynomial.T_add, neg_add_cancel, LaurentPolynomial.T_zero]
  have ht : (LaurentPolynomial.T (-3) : L)^2 = c^6 := by
    simp only [c, LaurentPolynomial.T_pow]
    norm_num
  rw [ht, ← hom_integral]
  rw [mul_one, hcx]

theorem paper_overlap (u : ℚ) : SexticOverlap K (paper K u false) (paper K u true) := by
  have hf := fixed_overlap K u
  unfold SexticOverlap at *
  rw [paper_eq, paper_eq]
  simp only [map_mul, map_pow, toLaurent_C, LaurentPolynomial.invert_C, hf]
  ring

variable (R : Type) [CommRing R]

private theorem puncture_w (f : R[X]) :
    puncture R f ≫ (SpecOver (R := R) (Cover f)).hom = (SpecOver (R := R) (Punctured R f)).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply QuadraticAlgebra.ext
  · exact Polynomial.toLaurent_C r
  · exact map_zero _

def gluedOver (f g : R[X]) (h : SexticOverlap R f g) : Over (Spec (.of R)) :=
  Over.mk (Y := glued R f g h) (WidePushout.desc (arrows := arrow R f g h)
    (SpecOver (R := R) (Punctured R f)).hom
    (fun i => (SpecOver (R := R) (Cover (if i then g else f))).hom) (by
      intro i
      cases i
      · exact puncture_w R f
      · let e : Spec (.of (Punctured R f)) ⟶ Spec (.of (Punctured R g)) :=
          (specIso (transition R h)).inv.left
        exact (Category.assoc e (puncture R g) (SpecOver (R := R) (Cover g)).hom).trans
          ((congrArg (e ≫ ·) (puncture_w R g)).trans (Over.w (specIso (transition R h)).inv))))

/-- The fixed paper model is a scheme over K glued at both 0 and infinity.
The construction is defined for every parameter, including degenerate fibres. -/
def paperModel (u : ℚ) : Over (Spec (.of K)) :=
  gluedOver K (paper K u false) (paper K u true) (paper_overlap K u)


end
end ZInQBlueprint.BinaryCover

#print axioms ZInQBlueprint.BinaryCover.fixed_overlap
#print axioms ZInQBlueprint.BinaryCover.paper_overlap
#print axioms ZInQBlueprint.BinaryCover.gluedOver
#print axioms ZInQBlueprint.BinaryCover.paperModel
