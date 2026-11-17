import SixAffine
import SexticIgusaChart
import Mathlib.Algebra.QuadraticAlgebra.IsQuadraticExtension
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.NumberField.Basic

/-! The two points over infinity on the six-contact sextic. -/
open CategoryTheory AlgebraicGeometry Polynomial
open ZInQBlueprint.BinaryCover ZInQBlueprint.SexticIgusaChart
open ZInQBlueprint.IntegralSextic ZInQBlueprint.CurveChart
open ZInQBlueprint.ResidualFactors ZInQBlueprint.GlobalTwist
namespace ZInQBlueprint.PointedSextic
noncomputable section

/-- Removing a rational square from the leading coefficient gives this radicand. -/
def radicand (u : ℚ) : ℚ := -6 * (delta u : ℚ) * homogeneousG u

theorem radicand_neg (u : ℚ) : radicand u < 0 := by
  have hb : 0 < (u.den : ℚ) := by exact_mod_cast u.den_pos
  have hG : 0 < homogeneousG u := by
    unfold homogeneousG poleForm
    nlinarith [sq_nonneg (7*(u.num:ℚ)+150*(u.den:ℚ)), sq_pos_of_pos hb]
  have hd : 0 < (delta u : ℚ) := by exact_mod_cast delta_pos u
  unfold radicand
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hd) hG

instance (u : ℚ) : Fact (¬ IsSquare (radicand u)) :=
  ⟨by rintro ⟨z,hz⟩; nlinarith [radicand_neg u, sq_nonneg z]⟩

abbrev SplittingField (u : ℚ) := QuadraticAlgebra ℚ (radicand u) 0

instance (u : ℚ) : NumberField (SplittingField u) :=
  NumberField.of_module_finite ℚ (SplittingField u)

theorem quadratic_galois (u : ℚ) :
    Module.finrank ℚ (SplittingField u) = 2 ∧ IsGalois ℚ (SplittingField u) :=
  ⟨Algebra.IsQuadraticExtension.finrank_eq_two _ _, inferInstance⟩

theorem infinity_coefficient (u : ℚ) :
    (fixed ℚ u true).eval 0 = radicand u * (left u)^2 := by
  simp [fixed, integralEquation, form, alpha, beta, gamma, radicand, left,
    homogeneousG, poleForm, m, n]

/-- The full algebra of the fibre at infinity, already a field over Q. -/
def infinityFibreIso {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    QuadraticAlgebra ℚ ((fixed ℚ u true).eval 0) 0 ≃ₐ[ℚ] SplittingField u :=
  QuadraticAlgebra.changeGeneratorEquiv (radicand u) 0 (Units.mk0 (left u) (parameters hu).1) 0
    (by rw [infinity_coefficient]; simp; ring) (by simp)

def ordinate (u : ℚ) : SplittingField u :=
  algebraMap ℚ _ (left u) * QuadraticAlgebra.omega

theorem ordinate_sq (u : ℚ) :
    (ordinate u)^2 = algebraMap ℚ (SplittingField u) ((fixed ℚ u true).eval 0) := by
  rw [ordinate, mul_pow, sq (QuadraticAlgebra.omega : SplittingField u),
    QuadraticAlgebra.omega_mul_omega_eq_algebraMap, infinity_coefficient, map_mul, map_pow]
  simp [mul_comm]

theorem ordinates {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ordinate u ≠ -ordinate u ∧ ∀ y : SplittingField u,
    y^2 = algebraMap ℚ _ ((fixed ℚ u true).eval 0) ↔ y = ordinate u ∨ y = -ordinate u := by
  have h : (fixed ℚ u true).eval 0 ≠ 0 := by
    rw [infinity_coefficient]
    exact mul_ne_zero (radicand_neg u).ne (pow_ne_zero _ (parameters hu).1)
  have hn : ordinate u ≠ 0 := by
    intro z
    have hh := ordinate_sq u
    rw [z, zero_pow (by decide : 2 ≠ 0)] at hh
    exact ((_root_.map_ne_zero (algebraMap ℚ (SplittingField u))).2 h) hh.symm
  exact ⟨by intro hz; apply hn; linear_combination (norm := ring_nf) (1/2:SplittingField u) * hz,
    fun y => by rw [← ordinate_sq, sq_eq_sq_iff_eq_or_eq_neg]⟩

/-- Evaluation on an affine double cover, including the square relation. -/
def evaluate {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (f : R)
    (y : S) (h : y^2 = φ f) : Cover f →+* S where
  toFun z := φ z.re + φ z.im * y
  map_one' := by change φ 1 + φ 0 * y = 1; simp
  map_zero' := by change φ 0 + φ 0 * y = 0; simp
  map_add' a b := by change φ (a + b).re + φ (a + b).im * y = _; simp; ring
  map_mul' a b := by change φ (a * b).re + φ (a * b).im * y = _; simp [← h]; ring

/-- A morphism over Q from the spectrum of the explicit quadratic field to the
infinity chart of the rational sextic. -/
def point (u : ℚ) : SpecOver (R := ℚ) (SplittingField u) ⟶ SpecOver (Cover (fixed ℚ u true)) := by
  let q := (algebraMap ℚ (SplittingField u)).comp (evalRingHom (0:ℚ))
  let ev := evaluate q (fixed ℚ u true) (ordinate u) (ordinate_sq u)
  refine Over.homMk (Spec.map (CommRingCat.ofHom ev)) ?_
  change Spec.map (CommRingCat.ofHom ev) ≫ Spec.map (CommRingCat.ofHom (algebraMap ℚ _)) =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (SplittingField u)))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change q (C r) + q 0 * ordinate u = algebraMap ℚ _ r
  simp [q]

end
end ZInQBlueprint.PointedSextic

#print axioms ZInQBlueprint.PointedSextic.radicand_neg
#print axioms ZInQBlueprint.PointedSextic.quadratic_galois
#print axioms ZInQBlueprint.PointedSextic.infinity_coefficient
#print axioms ZInQBlueprint.PointedSextic.infinityFibreIso
#print axioms ZInQBlueprint.PointedSextic.ordinate_sq
#print axioms ZInQBlueprint.PointedSextic.ordinates
#print axioms ZInQBlueprint.PointedSextic.evaluate
#print axioms ZInQBlueprint.PointedSextic.point
