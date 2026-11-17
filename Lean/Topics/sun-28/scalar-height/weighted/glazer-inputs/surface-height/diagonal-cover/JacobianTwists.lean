import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic

namespace ZInQBlueprint.Diagonal210
open WeierstrassCurve
noncomputable section

/-- The finite branch labels are 105, 70, 42 and 30 in this order. -/
def mark : Fin 4 → ℚ := ![0,1,2401,-343/32]
def coefficient : Fin 4 → ℚ := ![-7,-3,21,-42]

/-- Product of the other three entries. The corresponding quadratic
subcover is ramified at the other three finite marks and at infinity. -/
def triple {K : Type*} [CommMonoid K] (v : Fin 4 → K) : Fin 4 → K :=
  ![v 1*v 2*v 3,v 0*v 2*v 3,v 0*v 1*v 3,v 0*v 1*v 2]

def dataRow : Fin 4 → Fin 5 → ℚ :=
  ![![-43,2,505,12,-1548],![-43,256,-130,-768,-387],
    ![-43,600,-986,-600,-43],![-43,-686,-2915,-1372,-172]]

def quarticI (v : Fin 5 → ℚ) := 12*v 0*v 4-3*v 1*v 3+(v 2)^2
def quarticJ (v : Fin 5 → ℚ) :=
  72*v 0*v 2*v 4+9*v 1*v 2*v 3-27*v 0*(v 3)^2-27*(v 1)^2*v 4-2*(v 2)^3

/-- A short model of the Jacobian of a binary quartic in the original table. -/
def publishedJacobian (i : Fin 4) : WeierstrassCurve ℚ :=
  ⟨0,0,0,-(quarticI (dataRow i))/3,-(quarticJ (dataRow i))/27⟩

def rootCubic (d a b c : ℚ) : WeierstrassCurve ℚ :=
  ⟨0,-d*(a+b+c),0,d^2*(a*b+a*c+b*c),-d^3*a*b*c⟩

def model (i : Fin 4) (d : ℚ) : WeierstrassCurve ℚ :=
  ![rootCubic d (mark 1) (mark 2) (mark 3),
    rootCubic d (mark 0) (mark 2) (mark 3),
    rootCubic d (mark 0) (mark 1) (mark 3),
    rootCubic d (mark 0) (mark 1) (mark 2)] i

/-- Twist parameter associated to the short quartic model, before removing square factors. -/
def scale : Fin 4 → ℚ := ![32/75,128/343,-128,1]

theorem model_invariants (i : Fin 4) (d : ℚ) :
    (model i d).c₄ = d^2*(model i 1).c₄ ∧ (model i d).c₆ = d^3*(model i 1).c₆ := by
  fin_cases i <;> constructor <;> norm_num [model,rootCubic,mark,c₄,c₆,b₂,b₄,b₆] <;> ring

theorem published_invariants (i : Fin 4) :
    (publishedJacobian i).c₄ = (scale i)^2*(model i 1).c₄ ∧
    (publishedJacobian i).c₆ = (scale i)^3*(model i 1).c₆ ∧
    (model i 1).c₄≠0 ∧ (model i 1).c₆≠0 ∧ (publishedJacobian i).Δ≠0 := by
  fin_cases i <;> norm_num [publishedJacobian,dataRow,quarticI,quarticJ,model,rootCubic,
    mark,scale,c₄,c₆,Δ,b₂,b₄,b₆,b₈]

private theorem scale_ne (i : Fin 4) : scale i ≠ 0 := by fin_cases i <;> norm_num [scale]

/-- Two Weierstrass invariants recover the rational squareclass, even after an
arbitrary rational admissible change of Weierstrass coordinates. -/
theorem class_from_jacobian {i : Fin 4} {d : ℚ}
    (C : VariableChange ℚ) (eqn : C • model i d = publishedJacobian i) :
    ∃ v : ℚ, v≠0 ∧ d=scale i*v^2 := by
  obtain ⟨p4,p6,n4,n6,_⟩ := published_invariants i
  obtain ⟨m4,m6⟩ := model_invariants i d
  have h4 := congrArg WeierstrassCurve.c₄ eqn
  have h6 := congrArg WeierstrassCurve.c₆ eqn
  rw [variableChange_c₄,m4,p4] at h4
  rw [variableChange_c₆,m6,p6] at h6
  let w : ℚ := ((C.u⁻¹ : ℚˣ) : ℚ)
  have a : w^4*d^2=(scale i)^2 := mul_right_cancel₀ n4 (by simpa only [mul_assoc,w] using h4)
  have b : w^6*d^3=(scale i)^3 := mul_right_cancel₀ n6 (by simpa only [mul_assoc,w] using h6)
  have h : w^2*d=scale i := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (scale_ne i))
    calc (scale i)^2*(w^2*d) = (w^4*d^2)*(w^2*d) := by rw [a]
         _ = w^6*d^3 := by ring
         _ = (scale i)^3 := b
         _ = (scale i)^2 * scale i := by ring
  have wn : w≠0 := Units.ne_zero _
  exact ⟨w⁻¹,inv_ne_zero wn,by rw [← h]; field_simp [wn]⟩

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.model_invariants
#print axioms ZInQBlueprint.Diagonal210.published_invariants
#print axioms ZInQBlueprint.Diagonal210.class_from_jacobian
