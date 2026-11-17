import SymmetricNumerator
import Mathlib.Algebra.Divisibility.Hom
import Mathlib.Data.Int.Basic

namespace EllipticHeight.NormBounds
open EllipticHeight.Symmetric

variable {R : Type*} [CommRing R]

/-- In a real quadratic order the two homomorphisms give the signed integral norm. -/
structure NormData (R : Type*) [CommRing R] where
  norm : R →* ℤ
  plus : R →+* ℝ
  minus : R →+* ℝ
  factor : ∀ x : R, (norm x : ℝ) = plus x * minus x

def mass (data : NormData R) (a : R) := (data.norm a).natAbs

private theorem mass_power (data : NormData R) (a : R) (n : ℕ) :
    mass data (a^n) = (mass data a)^n := by simp [mass, Int.natAbs_pow]

theorem mass_divides_bound (data : NormData R) (a b : R) (dvd : a ∣ b) (nz : data.norm b ≠ 0) :
    mass data a ≤ mass data b := Int.natAbs_le_of_dvd_ne_zero (map_dvd data.norm dvd) nz

/-- The archimedean contribution to the square biform is an integer comparison
after taking the two real embeddings. -/
theorem sum_square_upper (d : NormData R) (x y : R)
    (plus : |d.plus y| ≤ |d.plus x|) (minus : |d.minus y| ≤ |d.minus x|) :
    mass d ((x+y)^2) ≤ 16 * (mass d x)^2 := by
  have p := real_numerator _ _ plus
  have q := real_numerator _ _ minus
  have both := mul_le_mul p q (sq_nonneg _) (by positivity)
  have re : (d.norm (x+y) : ℝ)^2 ≤ 16*(d.norm x:ℝ)^2 := by
    rw [d.factor, d.factor]
    simp only [map_add]
    nlinarith only [both]
  have unsigned : ((d.norm (x+y)).natAbs:ℝ)^2 ≤ 16*((d.norm x).natAbs:ℝ)^2 := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, sq_abs] using re
  rw [mass_power]
  exact_mod_cast unsigned

theorem sum_square_lower (d : NormData R) (x y : R)
    (plusX : 0 ≤ d.plus x) (minusX : 0 ≤ d.minus x)
    (plusY : 0 ≤ d.plus y) (minusY : 0 ≤ d.minus y) :
    (mass d x)^2 ≤ mass d ((x+y)^2) := by
  have pp : d.plus x ≤ d.plus (x+y) := by rw [map_add]; linarith
  have qq : d.minus x ≤ d.minus (x+y) := by rw [map_add]; linarith
  have both := mul_le_mul pp qq minusX (plusX.trans pp)
  have rb := pow_le_pow_left₀ (mul_nonneg plusX minusX) both 2
  rw [← d.factor, ← d.factor] at rb
  have unsigned : ((d.norm x).natAbs:ℝ)^2 ≤ ((d.norm (x+y)).natAbs:ℝ)^2 := by
    simpa only [Nat.cast_natAbs, Int.cast_abs, sq_abs] using rb
  rw [mass_power]
  exact_mod_cast unsigned

/-- The primitive output requirement enters through two pure divisibility identities.
The normalizing scalar need not be found, even at bad primes. -/
theorem paired_numerator (d : NormData R) (D a b c e A B C E : R)
    (left : ∃ u v, u*A+v*B=1) (right : ∃ u v, u*C+v*E=1)
    (middle : (a*c+D*b*e)^2*(A*E+B*C) = (2*(a*e+b*c)*(a*c-D*b*e))*(A*C))
    (bottom : (a*c+D*b*e)^2*(B*E) = (a*e-b*c)^2*(A*C))
    (live : d.norm (a*c+D*b*e) ≠ 0)
    (plus : |d.plus (D*b*e)| ≤ |d.plus (a*c)|)
    (minus : |d.minus (D*b*e)| ≤ |d.minus (a*c)|) :
    mass d A * mass d C ≤ 16 * (mass d a)^2 * (mass d c)^2 := by
  have div := numerator_dvd A B C E _ _ _ left right middle bottom
  have liveSquare : d.norm ((a*c+D*b*e)^2) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ live
  have h := (mass_divides_bound d _ _ div liveSquare).trans (sum_square_upper d _ _ plus minus)
  simp only [mass, map_mul, Int.natAbs_mul, mul_pow] at h ⊢
  nlinarith only [h]

/-- The raw duplication numerator on the real expanding branches has relative
mass in [1,16] times the fourth power of the input numerator mass. -/
theorem double_raw (d : NormData R) (D a b : R)
    (dp : 0 ≤ d.plus (D*b^2)) (dm : 0 ≤ d.minus (D*b^2))
    (bp : d.plus (D*b^2) ≤ (d.plus a)^2)
    (bm : d.minus (D*b^2) ≤ (d.minus a)^2) :
    (mass d a)^4 ≤ mass d ((a^2+D*b^2)^2) ∧
      mass d ((a^2+D*b^2)^2) ≤ 16*(mass d a)^4 := by
  have pp : 0 ≤ d.plus (a^2) := by rw [map_pow]; positivity
  have mm : 0 ≤ d.minus (a^2) := by rw [map_pow]; positivity
  have lo := sum_square_lower d (a^2) (D*b^2) pp mm dp dm
  have hi := sum_square_upper d (a^2) (D*b^2)
    (by rwa [abs_of_nonneg dp, abs_of_nonneg pp, map_pow])
    (by rwa [abs_of_nonneg dm, abs_of_nonneg mm, map_pow])
  simp only [mass_power d a 2, ← pow_mul] at lo hi
  exact ⟨lo,hi⟩

#print axioms mass_divides_bound
#print axioms sum_square_upper
#print axioms sum_square_lower
#print axioms paired_numerator
#print axioms double_raw
end EllipticHeight.NormBounds
