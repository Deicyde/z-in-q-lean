import ParameterLocus

namespace Sun28.ConicArithmetic
open Sun28.FactorHeights Sun28.ConicCovers Sun28.ScalarHeight

/-- Omit square factors independent of the abscissa from the two genus-two quotient equations. -/
def quintic {R : Type*} [CommRing R] (positive:Bool) (s:R) :=
  if positive then s*(s-4)*(16*s-15)*(1372*s^2-1396*s+439)
  else 5*s*(5*s+8)*(8*s+3)*(-600*s^2+11765*s+19184)

def num {R:Type*} [CommRing R] (pos:Bool) (a b:R) :=
  if pos then 343*(2*a-b)^2 else 2401*(5*a+8*b)*b

def den {R:Type*} [CommRing R] (pos:Bool) (a b:R) :=
  if pos then 8*(a-4*b)*b else 8*(5*a+b)^2

/-- Every positive scalar parameter maps to the odd quotient with its original beta coordinate. -/
theorem positive_point {x:ℚ} (hc:positiveParameter x) :
    ∃s y:ℚ, 4<s ∧ ratSquare s ∧ ratSquare (7*(s-4)) ∧ ratSquare (16*s-15) ∧ y≠0 ∧ y^2=quintic true s ∧
      beta x*den true s 1=num true s 1 := by
  obtain ⟨r,gt,⟨A,eA⟩,⟨B,eB⟩,⟨Z,eZ⟩,ex⟩:=positive_parameter ((positive_iff_parameter x).mpr hc)
  let s:=r^2
  have pp:0<1372*s^2-1396*s+439 := by
    have h0:0<s*(s-4):=mul_pos (show 0<s by dsimp [s];linarith) (by dsimp [s];linarith)
    nlinarith only [h0,gt,(show s=r^2 by rfl)]
  change 7*(1372*r^4-1396*r^2+439)=Z^2 at eZ
  have pz:Z≠0 := by intro z;rw [z] at eZ;dsimp [s] at pp;nlinarith
  have pa:A≠0 := by intro z;rw [z] at eA;nlinarith
  have pb:B≠0 := by intro z;rw [z] at eB;nlinarith
  have pr:r≠0 := by intro z;rw[z] at gt;norm_num at gt
  refine ⟨s,r*A*B*Z/7,gt,⟨r,rfl⟩,⟨A,eA⟩,⟨B,eB⟩,div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero pr pa) pb) pz) (by norm_num),?_,?_⟩
  · dsimp [s,quintic];rw [div_pow,mul_pow,mul_pow,mul_pow,←eA,←eB,←eZ];ring
  · dsimp [num,den,beta,s] at ex ⊢;linear_combination -2*ex/21

/-- The other quotient has a rational point off the branch divisor and a fixed marked map. -/
theorem negative_point {x:ℚ} (hc:negativeParameter x) (nonzero:x≠0) :
    ∃s y:ℚ, 0<s ∧ ratSquare s ∧ y≠0 ∧ y^2=quintic false s ∧
      beta x*den false s 1=num false s 1 := by
  obtain ⟨r,rn,⟨A,eA⟩,⟨B,eB⟩,ex⟩:=hc
  let s:=r^2
  let D:=1+5*s
  have d:0<D := by dsimp [D,s];positivity
  have h:-600*s^2+11765*s+19184=(4*x*D)^2 := by
    dsimp [D,s];linear_combination ex/4
  have ap:A≠0 := by intro z;rw [z] at eA;nlinarith only [eA,sq_nonneg r]
  have bp:B≠0 := by intro z;rw [z] at eB;nlinarith only [eB,sq_nonneg r]
  refine ⟨s,r*A*B*(4*x*D)/7,sq_pos_of_ne_zero rn,⟨r,rfl⟩,
    div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero rn ap) bp) (mul_ne_zero (mul_ne_zero (by norm_num) nonzero) d.ne')) (by norm_num),?_,?_⟩
  · dsimp only [quintic,Bool.false_eq_true,ite_false];rw [div_pow,mul_pow,mul_pow,mul_pow,←eA,←eB,←h];dsimp [s];ring
  · dsimp [num,den,beta,s];linear_combination -ex/4

end Sun28.ConicArithmetic
#print axioms Sun28.ConicArithmetic.positive_point
#print axioms Sun28.ConicArithmetic.negative_point
