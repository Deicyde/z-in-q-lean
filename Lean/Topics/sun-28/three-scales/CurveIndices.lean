import ZInQKernel.Multiplication.Soundness.GeneratorHeight
import MarkedHeights

namespace Sun28.Ordinary
open ZInQ ZInQ.Mult WeierstrassCurve.Affine

/-- The normalized curve in Sun is the public curve C, and its generator is twice R. -/
abbrev curveGenerator : curveC.toAffine.Point := 2 • pointR

def curveX : curveC.toAffine.Point → K0
  | .zero => 0
  | .some x _ _ => x

noncomputable def indexX (m : ℤ) : K0 := curveX (m • curveGenerator)

noncomputable def coordinateProduct (m : Fin 4 → ℤ) : K0 := ∏ i, indexX (m i)

theorem generator_coordinates :
    curveGenerator = .some twoRX twoRY twoR_nonsingular := two_smul_pointR

/-- An isomorphism identifies the literal Sun point with the public generator;
the map on (x,y) is the identity in the common field K₀. -/
theorem generator_cast :
    (Scalar.curve (-(3-sqrt2)^2) = curveC.toAffine) ∧
    HEq (Scalar.paperGenerator sqrt2_sq) curveGenerator := by
  have d : Scalar.curve (-(3-sqrt2)^2) = curveC.toAffine := by rw [curveC,delta_eq]; rfl
  refine ⟨d,?_⟩
  rw [generator_coordinates]
  -- Both point constructors agree after rewriting the public curve in the Sun normalization.
  have hx : Scalar.generatorX sqrt2 = twoRX := by
    rw [Scalar.generatorX,twoRX_eq]
    ring
  have hy : Scalar.generatorY sqrt2 = twoRY := by
    rw [Scalar.generatorY,twoRY_eq]
    ring
  have hh {A B : WeierstrassCurve.Affine K0} (e : A=B) {x x' y y' : K0}
      (ex : x=x') (ey : y=y') (p : A.Nonsingular x y) (q : B.Nonsingular x' y') :
      HEq (Point.some x y p) (Point.some x' y' q) := by subst B; subst x'; subst y'; rfl
  exact hh d hx hy _ _

theorem index_nonidentity {m : ℤ} (nz : m≠0) : m • curveGenerator ≠ 0 := by
  rw [show curveGenerator = theta genP0 from theta_genP0.symm,←map_zsmul,←map_zero theta]
  exact (theta.injective.ne (zsmul_genP0_ne_zero nz))

theorem index_affine {m : ℤ} (nz : m≠0) :
    ∃ y h, m • curveGenerator = .some (indexX m) y h := by
  have live := index_nonidentity nz
  unfold indexX
  generalize eq : m • curveGenerator = P at live ⊢
  cases P with
  | zero => exact (live rfl).elim
  | some x y h => exact ⟨y,h,rfl⟩

/-- In Sun's normalization the two scale factors ε⁴ cancel before heights enter. -/
theorem quadratic_index_height (m : ℤ) :
    (m:ℝ)^2 ≤ hK0 (indexX m) + Real.log 676 / 3 := by
  have gen : 1 < 2 * canonHeight curveGenerator := by
    simpa only [canonHeightE,theta_genP0] using two_canonHeight_genP0_gt_one
  have comp := two_canonHeight_le (m • curveGenerator)
  rw [canonHeight_zsmul] at comp
  have hsame : hx (m • curveGenerator) = hK0 (indexX m) := by
    unfold indexX
    cases m • curveGenerator with
    | zero => simp [curveX,←Point.zero_def]
    | some x y h => simp [curveX]
  rw [hsame] at comp
  nlinarith [mul_le_mul_of_nonneg_left gen.le (sq_nonneg (m:ℝ))]

end Sun28.Ordinary
#print axioms Sun28.Ordinary.generator_coordinates
#print axioms Sun28.Ordinary.generator_cast
#print axioms Sun28.Ordinary.index_nonidentity
#print axioms Sun28.Ordinary.index_affine
#print axioms Sun28.Ordinary.quadratic_index_height
