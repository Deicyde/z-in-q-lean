import SixCanonicalPeriods

/-! Gaussian points over the signed six-contact family of the discriminant-six
Shimura conic. The two real-labelled quotient points have rational coordinates.
Each of them has two lifts exchanged by complex conjugation. -/

open CategoryTheory AlgebraicGeometry

namespace ZInQBlueprint.ShimuraAtlas

open CoarseConic NormalDescent QuaternionLift

noncomputable section

private theorem gaussian_y_square (i : Qbar) (hi : i ^ 2 = -1) (u : ℚ) :
    (3 * i * (r u : Qbar)) ^ 2 = 9 * (SixContact.J u : Qbar) := by
  have hj : (SixContact.J u : Qbar) = -(r u : Qbar) ^ 2 := by exact_mod_cast first_square u
  rw [hj, mul_pow, mul_pow, hi]
  ring

private theorem gaussian_z_square (i : Qbar) (hi : i ^ 2 = -1) (u : ℚ) :
    (4 * i * (h u : Qbar)) ^ 2 = -27 * (SixContact.J u : Qbar) - 16 := by
  have hj : -27 * (SixContact.J u : Qbar) - 16 = -(4 * (h u : Qbar)) ^ 2 := by
    exact_mod_cast second_square u
  rw [hj, mul_pow, mul_pow, hi]
  ring

/-- One lift over the fixed quadratic field, for every off-contact parameter. -/
def gaussianPoint (i : Qbar) (hi : i ^ 2 = -1) {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ConicPoint where
  y := 3 * i * (r u : Qbar)
  z := 4 * i * (h u : Qbar)
  onCurve := by linear_combination 3 * gaussian_y_square i hi u + gaussian_z_square i hi u
  y_ne := by
    have hi0 : i ≠ 0 := by rintro rfl; norm_num at hi
    exact mul_ne_zero (mul_ne_zero (by norm_num) hi0) (by exact_mod_cast (radical_units hu).1)
  z_ne := by
    have hi0 : i ≠ 0 := by rintro rfl; norm_num at hi
    exact mul_ne_zero (mul_ne_zero (by norm_num) hi0) (by exact_mod_cast (radical_units hu).2)

theorem gaussianPoint_fibre (i : Qbar) (hi : i ^ 2 = -1) {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) : FibrePoint u (gaussianPoint i hi hu) :=
  ⟨gaussian_y_square i hi u, gaussian_z_square i hi u⟩

theorem gaussianPoint_quotient (i : Qbar) (hi : i ^ 2 = -1) {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) :
    (gaussianPoint i hi hu).quotientCoordinate = ((4 * h u / r u : ℚ) : Qbar) := by
  have ir : (r u : Qbar) ≠ 0 := by exact_mod_cast (radical_units hu).1
  change 3 * (4 * i * (h u : Qbar)) / (3 * i * (r u : Qbar)) = _
  have ii : i ≠ 0 := by rintro rfl; norm_num at hi
  push_cast
  field_simp

/-- Changing the second coordinate sign produces the other point on the
real-labelled quotient. -/
def otherGaussianSheet (p : ConicPoint) : ConicPoint where
  y := p.y
  z := -p.z
  onCurve := by rw [neg_sq]; exact p.onCurve
  y_ne := p.y_ne
  z_ne := neg_ne_zero.mpr p.z_ne

theorem otherGaussianSheet_quotient (p : ConicPoint) :
    (otherGaussianSheet p).quotientCoordinate = -p.quotientCoordinate := by
  change 3 * (-p.z) / p.y = -(3 * p.z / p.y)
  ring

/-- The four lifts split into two labelled fibres. All four occur over the
same copy of the Gaussian field and the signs account for every lift. -/
theorem gaussianPoint_exhausts (i : Qbar) (hi : i ^ 2 = -1) {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) {p : ConicPoint} (hp : FibrePoint u p) :
    let a := gaussianPoint i hi hu
    p = a ∨ p = a.w3 ∨ p = otherGaussianSheet a ∨ p = (otherGaussianSheet a).w3 := by
  let a := gaussianPoint i hi hu
  have hf : FibrePoint u a := gaussianPoint_fibre i hi hu
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hp.y_square.trans hf.y_square.symm) with hy | hy <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hp.z_square.trans hf.z_square.symm) with hz | hz
  · exact Or.inl (ConicPoint.ext hy hz)
  · exact Or.inr (Or.inr (Or.inl (ConicPoint.ext hy hz)))
  · exact Or.inr (Or.inr (Or.inr (ConicPoint.ext hy (by simpa [otherGaussianSheet, ConicPoint.w3] using hz))))
  · exact Or.inr (Or.inl (ConicPoint.ext hy hz))

/-- On each of the four lifts, the action on the single square root of -1
determines exactly whether Galois acts by the identity or by w₃. -/
theorem gaussian_fibre_galois (i : Qbar) (hi : i ^ 2 = -1) {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) {p : ConicPoint} (hp : FibrePoint u p) (σ : Gal) :
    (σ i = i ∧ p.conjugate σ = p) ∨ (σ i = -i ∧ p.conjugate σ = p.w3) := by
  have hs : (σ i) ^ 2 = i ^ 2 := by rw [← map_pow, hi]; simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with e | e
  · left
    refine ⟨e, ?_⟩
    rcases gaussianPoint_exhausts i hi hu hp with hp | hp | hp | hp <;>
      subst p <;> apply ConicPoint.ext <;>
      simp [ConicPoint.conjugate, ConicPoint.w3, otherGaussianSheet, gaussianPoint, map_ofNat, e]
  · right
    refine ⟨e, ?_⟩
    rcases gaussianPoint_exhausts i hi hu hp with hp | hp | hp | hp <;>
      subst p <;> apply ConicPoint.ext <;>
      simp [ConicPoint.conjugate, ConicPoint.w3, otherGaussianSheet, gaussianPoint, map_ofNat, e]

end
end ZInQBlueprint.ShimuraAtlas

#print axioms ZInQBlueprint.ShimuraAtlas.gaussianPoint
#print axioms ZInQBlueprint.ShimuraAtlas.gaussianPoint_fibre
#print axioms ZInQBlueprint.ShimuraAtlas.gaussianPoint_quotient
#print axioms ZInQBlueprint.ShimuraAtlas.otherGaussianSheet_quotient
#print axioms ZInQBlueprint.ShimuraAtlas.gaussianPoint_exhausts
#print axioms ZInQBlueprint.ShimuraAtlas.gaussian_fibre_galois
