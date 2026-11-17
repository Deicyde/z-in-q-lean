import DiagonalCover
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace ZInQBlueprint.Diagonal210
open WeierstrassCurve
noncomputable section

/-- After forgetting one coordinate, the remaining equations in projective
coordinates (w,u,v,z) are u²/A-v²/B+(a-b)w² and u²/A-z²/C+(a-c)w².
This is the Hessian of their pencil with parameters x and y. -/
def hessian (a b c A B C x y : ℚ) : Matrix (Fin 4) (Fin 4) ℚ :=
  Matrix.diagonal ![2*((a-b)*x+(a-c)*y), 2*(x+y)/A, -2*x/B, -2*y/C]

def pencilRow (a b c d : ℚ) : Fin 5 → ℚ :=
  ![0,16*(a-b)/d,16*(2*a-b-c)/d,16*(a-c)/d,0]

def evalQuartic (v : Fin 5 → ℚ) (x y : ℚ) :=
  v 0*x^4+v 1*x^3*y+v 2*x^2*y^2+v 3*x*y^3+v 4*y^4

theorem determinant_quartic (a b c A B C x y : ℚ) :
    (hessian a b c A B C x y).det = evalQuartic (pencilRow a b c (A*B*C)) x y := by
  rw [hessian, Matrix.det_diagonal, Fin.prod_univ_four]
  simp [evalQuartic,pencilRow,div_eq_mul_inv]
  ring

/-- Cremona--Fisher--Stoll, Definition 2.4, gives c4=I(det) and c6=J(det)/2
for two quadrics. Their Theorem 2.8(iii), scaled by 6, gives this short model. -/
def pencilJacobian (a b c d : ℚ) : WeierstrassCurve ℚ :=
  ⟨0,0,0,-quarticI (pencilRow a b c d)/48,-quarticJ (pencilRow a b c d)/1728⟩

/-- The elliptic quotient of the triple of radicals has the rational Jacobian
given by the determinant of the two quadrics, with its full twist parameter. -/
theorem pencil_jacobian_iso (a b c d : ℚ) (hd : d≠0) :
    ∃ W : VariableChange ℚ, W • rootCubic d a b c=pencilJacobian a b c d := by
  let W : VariableChange ℚ := ⟨Units.mk0 (d/2) (div_ne_zero hd (by norm_num)),d*(a+b+c)/3,0,0⟩
  refine ⟨W,?_⟩
  rw [variableChange_def]
  congr 1 <;> simp [W,rootCubic,quarticI,quarticJ,pencilRow,hd] <;> field_simp [hd] <;> ring

/-- Four explicit admissible transformations identify the recovered model with
the four published binary-quartic Jacobians in the specified order. -/
theorem canonical_matches (i : Fin 4) :
    ∃ W : VariableChange ℚ, W • model i (triple coefficient i)=publishedJacobian i := by
  let M := model i (triple coefficient i)
  let W : VariableChange ℚ := ⟨Units.mk0 (comparisonRoot i) (coefficient_scales i).2.1,-M.a₂/3,0,0⟩
  refine ⟨W,?_⟩
  rw [variableChange_def]
  congr 1 <;> fin_cases i <;> norm_num [W,M,model,rootCubic,triple,mark,coefficient,comparisonRoot,
    publishedJacobian,dataRow,quarticI,quarticJ]

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.determinant_quartic
#print axioms ZInQBlueprint.Diagonal210.pencil_jacobian_iso
#print axioms ZInQBlueprint.Diagonal210.canonical_matches
