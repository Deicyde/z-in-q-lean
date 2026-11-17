import CanonicalOrbit
import Mathlib.Tactic.LinearCombination

namespace EllipticHeight.Symmetric
open EllipticHeight.Canonical

/-- The three coefficients of the product of two primitive binary linear forms
satisfy an explicit Bézout identity in any commutative ring. -/
theorem primitive_symmetric {R : Type*} [CommRing R] (a b c d : R)
    (p : ∃ u v, u*a+v*b=1) (q : ∃ u v, u*c+v*d=1) :
    ∃ i j k, i*(a*c) + j*(a*d+b*c) + k*(b*d) = 1 := by
  obtain ⟨u,v,hu⟩ := p
  obtain ⟨w,z,hw⟩ := q
  let A := u*w
  let B := u*z
  let C := v*w
  let D := v*z
  let r := A*(a*c)+D*(b*d)
  let t := B*(a*d)+C*(b*c)
  refine ⟨A*(r+2*t)-(B-C)^2*(b*d), (B+C)*t-B*C*(a*d+b*c), D*(r+2*t), ?_⟩
  calc
    _ = ((u*a+v*b)*(w*c+z*d))^2 := by dsimp [r,t,A,B,C,D]; ring
    _ = 1 := by rw [hu, hw]; ring

/-- The two cross identities are exactly projective proportionality with
the numerator coefficient distinguished. No fraction field or unit choice is needed. -/
theorem numerator_dvd {R : Type*} [CommRing R] (a b c d top mid bot : R)
    (p : ∃ u v, u*a+v*b=1) (q : ∃ u v, u*c+v*d=1)
    (crossMid : top*(a*d+b*c) = mid*(a*c))
    (crossBot : top*(b*d) = bot*(a*c)) : a*c ∣ top := by
  obtain ⟨i,j,k,h⟩ := primitive_symmetric a b c d p q
  refine ⟨i*top+j*mid+k*bot, ?_⟩
  calc
    top = top*(i*(a*c)+j*(a*d+b*c)+k*(b*d)) := by rw [h, mul_one]
    _ = i*top*(a*c)+j*(top*(a*d+b*c))+k*(top*(b*d)) := by ring
    _ = _ := by rw [crossMid, crossBot]; ring

/-- Affine group-law calculation before division, valid over every commutative ring. -/
theorem chord_numerators {R : Type*} [CommRing R] (D x y u v : R)
    (p : y^2 = x^3-D*x) (q : v^2 = u^3-D*u) :
    let A := (y-v)^2-(x+u)*(x-u)^2
    let B := (y+v)^2-(x+u)*(x-u)^2
    A+B = 2*(x+u)*(x*u-D) ∧ A*B = (x-u)^2*(x*u+D)^2 := by
  dsimp only
  have plus : (y-v)^2-(x+u)*(x-u)^2 = (x+u)*(x*u-D)-2*y*v := by linear_combination p+q
  have minus : (y+v)^2-(x+u)*(x-u)^2 = (x+u)*(x*u-D)+2*y*v := by linear_combination p+q
  rw [plus, minus]
  constructor
  · ring
  · linear_combination (-4*v^2)*p + (-4*(x^3-D*x))*q

/-- For the diagonal, the symmetric output consists of the double and infinity. -/
theorem diagonal {R : Type*} [CommRing R] (D a b : R) :
    (a*b-b*a)^2 = 0 ∧
    2*(a*b+b*a)*(a*a-D*b*b) = 4*a*b*(a^2-D*b^2) ∧
    (a*a+D*b*b)^2 = (a^2+D*b^2)^2 := by
  constructor
  · ring
  constructor <;> ring

/-- When the first input is infinity the two output abscissae coincide. -/
theorem infinity_input {R : Type*} [CommRing R] (D c d : R) :
    ((1:R)*d-0*c)^2 = d^2 ∧
    2*(1*d+0*c)*(1*c-D*0*d) = 2*d*c ∧
    (1*c+D*0*d)^2 = c^2 := by simp

/-- On two real expanding inputs the numerator biform costs a factor four. -/
theorem real_numerator (A B : ℝ) (bound : |B| ≤ |A|) : (A+B)^2 ≤ 4*A^2 := by
  have t : |A+B| ≤ 2*|A| := (abs_add_le ..).trans (by linarith)
  have s := pow_le_pow_left₀ (abs_nonneg _) t 2
  rw [sq_abs, mul_pow, sq_abs] at s
  nlinarith only [s]

/-- Reverse the upper parallelogram by applying it to U+V,U−V.
The bounds are allowed to include the identity. -/
theorem degree_of_upper (h : ℕ → ℝ) (origin : h 0=0) (L U : ℝ)
    (double : ∀ i, 4*h i - L ≤ h (2*i))
    (upper : ∀ i j : ℕ, j ≤ i → h (i+j)+h (i-j) ≤ 2*h i+2*h j+U)
    (n : ℕ) : MultiplicationBound h n := by
  apply multiplication_of_parallelogram h origin (L+U/2)
  intro k j
  let p : ℕ := 2^k
  have hB : p*j ≤ p*(j+2) := Nat.mul_le_mul_left p (by omega)
  have um := upper (p*(j+2)) (p*j) hB
  have add : p*(j+2)+p*j=2*(p*(j+1)) := by ring
  have sub : p*(j+2)-p*j=2*p := by
    rw [show p*(j+2)=p*j+2*p by ring]
    omega
  rw [add,sub] at um
  change 2*h (p*(j+1))+2*h p-(L+U/2) ≤ h (p*(j+2))+h (p*j)
  linarith only [um, double (p*(j+1)), double p]

/-- The physical multiplicative-height input only concerns multiplication of
two numerators and the size of one double. It yields the sharp index estimate. -/
theorem index_of_numerators (H : ℕ → ℝ) (pos : ∀ i, 0 < H i) (origin : H 0=1)
    (base : H 1=41) (firstDouble : H 2=4905889)
    (lower : ∀ i, (H i)^4 ≤ H (2*i))
    (upper : ∀ i, H (2*i) ≤ 4*(H i)^4)
    (pair : ∀ i j : ℕ, j ≤ i → H (i+j)*H (i-j) ≤ 4*(H i)^2*(H j)^2)
    (n : ℕ) (nonzero : n ≠ 0) : (41:ℝ)^(n^2) ≤ H n := by
  let h (i : ℕ) := Real.log (H i)
  have down (i : ℕ) : 4*h i ≤ h (2*i) := by
    have e := Real.log_le_log (pow_pos (pos i) 4) (lower i)
    rw [Real.log_pow] at e
    norm_num1 at e
    exact e
  have up (i : ℕ) : h (2*i) ≤ 4*h i+Real.log 4 := by
    have e := Real.log_le_log (pos _) (upper i)
    rw [Real.log_mul (by norm_num) (pow_ne_zero _ (pos i).ne'), Real.log_pow] at e
    norm_num1 at e
    dsimp [h]
    linarith
  have degree : MultiplicationBound h n := by
    apply degree_of_upper h (by simp [h, origin]) 0 (Real.log 4) (by simpa using down)
    intro i j ji
    have e := Real.log_le_log (mul_pos (pos _) (pos _)) (pair i j ji)
    rw [Real.log_mul (pos _).ne' (pos _).ne',
      Real.log_mul (mul_ne_zero (by norm_num) (pow_ne_zero _ (pos i).ne')) (pow_ne_zero _ (pos j).ne'),
      Real.log_mul (by norm_num) (pow_ne_zero _ (pos i).ne'), Real.log_pow, Real.log_pow] at e
    norm_num1 at e
    dsimp [h]
    linarith
  have bound := sharp_index h n nonzero (by simp [h,base]) (by simp [h,firstDouble])
    (fun k => by simpa only [pow_succ' (2:ℕ) (k+1)] using down (2^(k+1)))
    (fun k => by simpa only [pow_succ', Nat.mul_assoc] using up (2^k*n)) degree
  simpa only [h, Real.exp_log (pos n)] using multiplicative_index h n bound

#print axioms primitive_symmetric
#print axioms numerator_dvd
#print axioms chord_numerators
#print axioms diagonal
#print axioms infinity_input
#print axioms real_numerator
#print axioms degree_of_upper
#print axioms index_of_numerators
end EllipticHeight.Symmetric
