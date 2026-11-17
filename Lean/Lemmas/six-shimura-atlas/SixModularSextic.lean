import SixShimuraChart
import PrintedSexticRegular

/-! The exact coordinate change between Baba--Granath, Theorem 3.14
and Corollary 3.15. Both polynomials are binary sextics. -/
open Polynomial
namespace ZInQBlueprint.ShimuraAtlas
open QuaternionLift NormalDescent CoarseConic PrintedModel
noncomputable section

/-- Coefficients in Corollary 3.15 are A=h₄³, B=√(−6)h₆², C=2√2 h₁₂. -/
def modularBinary {K : Type*} [CommRing K] (A B C x z : K) : K :=
  A*(x^6-21*x^4*z^2-21*x^2*z^4+z^6) +
  B*(x^6+9*x^4*z^2-9*x^2*z^4-z^6) +
  C*x*z*(3*x^4-2*x^2*z^2+3*z^4)

theorem period_binary {K : Type*} [Field K] [CharZero K] (s k x z : K)
    (hk : k^2 = 9*s^2-32) :
    SexticConjugation.binary (-s) (-k*x) z =
      -4*k^6 * modularBinary 1 (3*s/4) (k/2) x z := by
  simp only [SexticConjugation.binary,neg_sq, ← hk,modularBinary]
  ring

/-- Recover the two raw coefficients from the normalized projective point.
The formula stays homogeneous in A, Y and Z. -/
theorem periods_to_printed {K : Type*} [Field K] [CharZero K]
    (A Y Z e l s k x z : K) (hy : e*Y = A*(3*s/4))
    (hz : 2*l*Z = A*(k/2)) (hk : k^2 = 9*s^2-32) :
    A*SexticConjugation.binary (-s) (-k*x) z =
      -4*k^6 * modularBinary A (e*Y) (2*l*Z) x z := by
  rw [period_binary s k x z hk,hy,hz]
  unfold modularBinary
  ring

/-- A polynomial in one affine chart with exactly the modular coefficients. -/
def modularPolynomial {K : Type*} [Field K] (s k : K) : K[X] :=
  modularBinary 1 (C (3*s/4)) (C (k/2)) X 1

theorem eval_modular {K : Type*} [Field K] (s k x : K) :
    (modularPolynomial s k).eval x = modularBinary 1 (3*s/4) (k/2) x 1 := by
  simp [modularPolynomial,modularBinary,eval_mul,eval_add,eval_sub,eval_pow]

theorem compatible_radicals {u : ℚ} (hu : u ∉ ZInQ.contactSet) {p : ConicPoint}
    (hp : FibrePoint u p) (e l : Qbar) (he : e^2 = -6) (hl : l^2 = 2) :
    let s := e*p.y/3
    let k := l*p.z
    ∃ d : Qbar, d^2 = 6 ∧ argument u d = -s ∧ k^2 = 9*s^2-32 ∧ k ≠ 0 := by
  dsimp only
  have hr : (r u : Qbar) ≠ 0 := by exact_mod_cast (radical_units hu).1
  have hj : (SixContact.J u : Qbar) = -(r u : Qbar)^2 := by exact_mod_cast first_square u
  have hs : (e*p.y/3)^2 = -6*(SixContact.J u : Qbar) := by
    rw [div_pow,mul_pow,he,hp.y_square]
    ring
  refine ⟨-(e*p.y/3)/(r u : Qbar),?_,?_,?_,?_⟩
  · rw [div_pow,neg_sq,hs,hj]
    field_simp [hr]
  · dsimp [argument]
    field_simp [hr]
  · rw [mul_pow,hl,hp.z_square,hs]
    ring
  · exact mul_ne_zero (fun h => by rw [h] at hl; norm_num at hl) p.z_ne

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.period_binary
#print axioms ZInQBlueprint.ShimuraAtlas.periods_to_printed
#print axioms ZInQBlueprint.ShimuraAtlas.compatible_radicals
