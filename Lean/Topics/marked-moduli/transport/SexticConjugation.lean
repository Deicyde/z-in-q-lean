import CoarseConic
import SexticCalibration

/-! An explicit comparison of the Jacobian's two conjugate curves.
Coordinates X,Z,Y have weights 1,1,3. The formula also applies above XZ = 0. -/

namespace ZInQBlueprint.SexticConjugation
open ZInQBlueprint.SexticCalibration
noncomputable section
variable {R : Type*} [CommRing R]

def binary (s x z : R) : R :=
  let t := 9*s^2-32
  (-4+3*s)*x^6+6*t*x^5*z+3*t*(28+9*s)*x^4*z^2-4*t^2*x^3*z^3+
    3*t^2*(28-9*s)*x^2*z^4+6*t^3*x*z^5-t^3*(4+3*s)*z^6

theorem affine (s x : R) : binary s x 1 = (sextic s).eval x := by
  simp [binary,sextic]

theorem reversal (s x z : R) :
    binary (-s) ((9*s^2-32)*z) x = (9*s^2-32)^3 * binary s x z := by
  simp only [binary,neg_sq]
  ring

variable {K : Type*} [Field K]

structure Triple (s D : K) where
  x : K
  z : K
  y : K
  nonzero : x ≠ 0 ∨ z ≠ 0
  equation : y^2 = D*binary s x z

/-- Equivalence of weighted coordinates in the two base charts of the double cover. -/
def scalings (s D : K) : Setoid (Triple s D) where
  r a b := ∃ c : Kˣ, b.x = (c:K)*a.x ∧ b.z = (c:K)*a.z ∧ b.y = (c:K)^3*a.y
  iseqv := {
    refl a := ⟨1,by simp⟩
    symm := by
      rintro a b ⟨c,hx,hz,hy⟩
      exact ⟨c⁻¹, by simp [hx,hz,hy]⟩
    trans := by
      rintro a b d ⟨c,hx,hz,hy⟩ ⟨e,kx,kz,ky⟩
      exact ⟨e*c, by simp [kx,kz,ky,hx,hz,hy,mul_pow,mul_assoc]⟩ }

abbrev Points (s D : K) := Quotient (scalings s D)

/-- The comparison uses t = v², where v can be taken in a fixed cyclotomic extension. -/
def reverseTriple {s D v : K} (hv : v^2=9*s^2-32) (hn : v ≠ 0) (a : Triple s D) :
    Triple (-s) D where
  x := (9*s^2-32)*a.z
  z := a.x
  y := v^3*a.y
  nonzero := a.nonzero.elim Or.inr (fun hz => Or.inl (mul_ne_zero (hv ▸ pow_ne_zero 2 hn) hz))
  equation := by rw [mul_pow,a.equation,reversal,← hv]; ring

def reversePoints {s D v : K} (hv : v^2=9*s^2-32) (hn : v ≠ 0) :
    Points s D → Points (-s) D :=
  Quotient.map (reverseTriple hv hn) (by
    rintro a b ⟨c,hx,hz,hy⟩
    exact ⟨c,by simp [reverseTriple,hx,hz,hy,mul_left_comm]⟩)

/-- Reversing twice is the weighted scaling by t on every projective point. -/
def conjugateEquiv {s D v : K} (hv : v^2=9*s^2-32) (hn : v ≠ 0) :
    Points s D ≃ Points (-s) D where
  toFun := reversePoints hv hn
  invFun := Quotient.map (fun a : Triple (-s) D => ({
    x := (9*s^2-32)*a.z, z := a.x, y := v^3*a.y,
    nonzero := a.nonzero.elim Or.inr (fun h => Or.inl (mul_ne_zero (hv ▸ pow_ne_zero 2 hn) h)),
    equation := by
      have h := reversal (-s) a.x a.z
      rw [neg_neg,neg_sq] at h
      rw [mul_pow,a.equation,h,← hv]; ring } : Triple s D)) (by
        rintro a b ⟨c,hx,hz,hy⟩
        exact ⟨c,by simp [hx,hz,hy,mul_left_comm]⟩)
  left_inv := by
    intro a
    induction a using Quotient.inductionOn with
    | _ a =>
      apply Quotient.sound
      -- Relation points from the twice-reversed representative back to a.
      apply (scalings _ _).symm
      refine ⟨Units.mk0 _ (hv ▸ pow_ne_zero 2 hn),rfl,rfl,?_⟩
      change v^3*(v^3*a.y)=(9*s^2-32)^3*a.y
      rw [← hv]; ring
  right_inv := by
    intro a
    induction a using Quotient.inductionOn with
    | _ a =>
      apply Quotient.sound
      apply (scalings _ _).symm
      refine ⟨Units.mk0 _ (hv ▸ pow_ne_zero 2 hn),rfl,rfl,?_⟩
      change v^3*(v^3*a.y)=(9*s^2-32)^3*a.y
      rw [← hv]; ring

/-- A primitive cube root (z²+z+1=0) and √6 already give √(−2).
Thus adjoining the full 3-torsion supplies the comparison coefficient. -/
theorem comparison_coefficient [CharZero K] (u : ℚ) {z d : K} (hz : z^2+z+1=0) (hd : d^2=6) :
    (4*(CoarseConic.h u : K)*d*(2*z+1)/3)^2 =
      9*(d*(CoarseConic.r u : K))^2-32 := by
  rw [(CoarseConic.sextic_parameters u hd).2]
  field_simp
  linear_combination (norm := ring) (4*(CoarseConic.h u : K))^2*(2*z+1)^2*(hd) +
    24*(4*(CoarseConic.h u : K))^2*hz

end
end ZInQBlueprint.SexticConjugation

#print axioms ZInQBlueprint.SexticConjugation.affine
#print axioms ZInQBlueprint.SexticConjugation.reversal
#print axioms ZInQBlueprint.SexticConjugation.conjugateEquiv
#print axioms ZInQBlueprint.SexticConjugation.comparison_coefficient
