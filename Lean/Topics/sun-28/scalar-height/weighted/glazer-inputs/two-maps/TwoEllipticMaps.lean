import GenusTwoHeight
import QuotientGroup

/-! The two elliptic images of the genus-two curve defined by a pair of squareclasses. -/
namespace ZInQBlueprint.TwoEllipticMaps
open Sun28.FiveDescent Sun28.Ordinary ZInQ.RouteK WeierstrassCurve.Affine.Point
noncomputable section

/-- The second cubic is obtained from the quartic by taking the reciprocal coordinate. -/
def reversed (t : ℚ) := (t-1)*(2401-2400*t)*(375*t-343)
def form (j : Bool) (t : ℚ) := if j then reversed t else cubic t

def lead (j : Bool) : ℚ := if j then -900000 else 823543
def coeff2 (j : Bool) : ℚ := if j then 2623575 else -2547118
def coeff1 (j : Bool) : ℚ := if j then -2547118 else 2623575
def coeff0 (j : Bool) : ℚ := if j then 823543 else -900000

theorem reciprocal {t : ℚ} (ht : t≠0) : reversed t⁻¹ = cubic t/t^3 := by
  unfold reversed cubic;field_simp

def model (j : Bool) (c : ℚ) : WeierstrassCurve ℚ :=
  ⟨0,c*coeff2 j,0,c^2*lead j*coeff1 j,c^3*(lead j)^2*coeff0 j⟩

theorem cubic_coefficients (j : Bool) (t : ℚ) :
    form j t=lead j*t^3+coeff2 j*t^2+coeff1 j*t+coeff0 j := by
  cases j <;> dsimp [form,reversed,cubic,lead,coeff2,coeff1,coeff0] <;> ring

private theorem smooth (j : Bool) {c : ℚ} (hc : c≠0) : (model j c).Δ≠0 := by
  cases j <;> dsimp [model,lead,coeff2,coeff1,coeff0,WeierstrassCurve.Δ,WeierstrassCurve.b₂,
    WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈] <;> ring_nf <;> positivity

/-- Monic coordinates on the split cubic, including the scalar in its leading coefficient. -/
theorem cubic_point (j : Bool) {t v c : ℚ} (hc : c≠0) (eqn : v^2=c*form j t) :
    ∃ P:(model j c).toAffine.Point, P.xRep 0=c*lead j*t ∧ P≠0 := by
  let X:=c*lead j*t
  let Y:=c*lead j*v
  have eq : (model j c).toAffine.Equation X Y := by
    rw [WeierstrassCurve.Affine.equation_iff]
    rw [cubic_coefficients] at eqn
    dsimp [model,X,Y]
    linear_combination (c*lead j)^2*eqn
  have ns:=(WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero (smooth j hc)).mp eq
  exact ⟨some X Y ns,rfl,some_ne_zero _⟩

/-- Each nonbranch rational lift yields points on the two twists with parameters e and de. -/
theorem two_images {d e : ℤ} {x y : ℚ} (nd : d≠0) (ne : e≠0) (nx : x≠0)
    (curve : (e:ℚ)*y^2=sextic d x) :
    let t:ℚ:=(d:ℚ)*x^2
    ∃ P:(model false (e:ℚ)).toAffine.Point, ∃ Q:(model true ((d:ℚ)*e)).toAffine.Point,
      P.xRep 0=(e:ℚ)*lead false*t ∧ Q.xRep 0=((d:ℚ)*e)*lead true*t⁻¹ ∧ P≠0 ∧ Q≠0 := by
  let t:ℚ:=(d:ℚ)*x^2
  have hd:(d:ℚ)≠0:=by exact_mod_cast nd
  have he:(e:ℚ)≠0:=by exact_mod_cast ne
  have ht:t≠0:=mul_ne_zero hd (pow_ne_zero _ nx)
  change (e:ℚ)*y^2=cubic t at curve
  have one : ((e:ℚ)*y)^2=(e:ℚ)*form false t := by
    change _=(e:ℚ)*cubic t
    rw [←curve];ring
  have two : ((d:ℚ)*e*x*y/t^2)^2=((d:ℚ)*e)*form true t⁻¹ := by
    change _=((d:ℚ)*e)*reversed t⁻¹
    rw [reciprocal ht,←curve]
    field_simp
    dsimp [t]
    ring
  obtain ⟨P,px,pn⟩:=cubic_point false he one
  obtain ⟨Q,qx,qn⟩:=cubic_point true (mul_ne_zero hd he) two
  exact ⟨P,Q,px,qx,pn,qn⟩

/-- On the first quotient, requiring one rational square is exactly the lift condition. -/
theorem lift_iff {d e : ℤ} {t v : ℚ} (he : (e:ℚ)≠0) (ht : t≠0) (hv : v≠0)
    (onCubic : v^2=(e:ℚ)*cubic t) :
    (∃ x y : ℚ, x≠0 ∧ y≠0 ∧ t=(d:ℚ)*x^2 ∧ v=(e:ℚ)*y ∧ (e:ℚ)*y^2=sextic d x) ↔
      ∃ x : ℚ, t=(d:ℚ)*x^2 := by
  constructor
  · rintro ⟨x,_,_,_,eq,_,_⟩; exact ⟨x,eq⟩
  · rintro ⟨x,eq⟩
    have nx:x≠0:=by rintro rfl;simp at eq;exact ht eq
    refine ⟨x,v/e,nx,div_ne_zero hv he,eq,?_,?_⟩
    · field_simp
    · unfold sextic
      rw [←eq]
      field_simp
      linear_combination onCubic

/-- The five homogeneous marked rows select the actual pair of twists in these maps. -/
theorem images_of_slope {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    ∃ x y : ℚ, x≠0 ∧ y≠0 ∧ parameter (D A B) x=(A:ℚ)/B ∧
      let t:ℚ:=(D A B:ℚ)*x^2
      ∃ P:(model false (E A B:ℚ)).toAffine.Point, ∃ Q:(model true ((D A B:ℚ)*E A B)).toAffine.Point,
        P.xRep 0=(E A B:ℚ)*lead false*t ∧ Q.xRep 0=((D A B:ℚ)*E A B)*lead true*t⁻¹ ∧ P≠0 ∧ Q≠0 := by
  obtain ⟨sd,se,x,y,nx,ny,point,back⟩:=forward off
  exact ⟨x,y,nx,ny,back,two_images sd.ne_zero se.ne_zero nx point⟩

end
end ZInQBlueprint.TwoEllipticMaps
#print axioms ZInQBlueprint.TwoEllipticMaps.reciprocal
#print axioms ZInQBlueprint.TwoEllipticMaps.cubic_coefficients
#print axioms ZInQBlueprint.TwoEllipticMaps.cubic_point
#print axioms ZInQBlueprint.TwoEllipticMaps.two_images
#print axioms ZInQBlueprint.TwoEllipticMaps.lift_iff
#print axioms ZInQBlueprint.TwoEllipticMaps.images_of_slope
