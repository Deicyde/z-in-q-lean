import AnchorBase23
import ActualGenerator

namespace Prime23.ActualBase
open EllipticOrbit.Field
open WeierstrassCurve.Affine

/-- Total reciprocal abscissa, expressed using the physical field coordinates. -/
def fromCoordinates (S : Point) : K :=
  match coordinates S with
  | none => 0
  | some (x,_) => x⁻¹

private theorem reciprocal_of_product {a b : K} (h : a*b=1) : a⁻¹=b := by
  have nz : a≠0 := by intro z; rw [z,zero_mul] at h; exact zero_ne_one h
  calc a⁻¹=a⁻¹*1 := (mul_one _).symm
       _ = _ := by rw [←h,←mul_assoc,inv_mul_cancel₀ nz,one_mul]

theorem point_coordinates : coordinates P=some (ofPair Base.xP,ofPair Base.yP) := P_pair

private theorem point_nonsingular : E.toAffine.Nonsingular (ofPair Base.xP) (ofPair Base.yP) :=
  (equation_iff_nonsingular (W:=E)).mp ((equation ..).mpr (by decide +kernel))

private theorem point_as_affine : P=(WeierstrassCurve.Affine.Point.some point_nonsingular : Point) :=
  coordinates_injective point_coordinates

private theorem tangent_pair :
    E.toAffine.slope (ofPair Base.xP) (ofPair Base.xP) (ofPair Base.yP) (ofPair Base.yP)=
      ofPair Base.tangent := by
  have ny : ofPair Base.yP≠0 := by decide +kernel
  rw [tangent ny]
  apply (div_eq_iff (mul_ne_zero (by norm_num) ny)).mpr
  decide +kernel

theorem double_pair : coordinates ((2:ℕ) • P)=
    some (ofPair Base.xDouble,doubleY (ofPair Base.xP) (ofPair Base.yP)) := by
  rw [point_as_affine,double_coordinates point_nonsingular (by decide +kernel)]
  rw [doubleX,tangent_pair]
  apply congrArg some
  apply Prod.ext
  · change E.toAffine.addX (ofPair Base.xP) (ofPair Base.xP) (ofPair Base.tangent)=ofPair Base.xDouble
    decide +kernel
  · rfl

theorem actual_qP : fromCoordinates P=ofPair Base.qP := by
  unfold fromCoordinates
  rw [point_coordinates]
  apply reciprocal_of_product
  rw [←ofPair_mul,Base.reciprocal_values.2.2.2.1]
  rfl

theorem actual_qDouble : fromCoordinates ((2:ℕ) • P)=ofPair Base.qDouble := by
  unfold fromCoordinates
  rw [double_pair]
  apply reciprocal_of_product
  rw [←ofPair_mul,Base.reciprocal_values.2.2.2.2.1]
  rfl

/-- The reciprocal square-root sign used at the doubled point. -/
theorem actual_gStar :
    2*ofPair Base.yP/((ofPair Base.xP)^2+D)=ofPair Base.doubleRoot := by
  apply (div_eq_iff (square_plus_D_ne_zero _)).mpr
  decide +kernel

#print axioms double_pair
#print axioms actual_qP
#print axioms actual_qDouble
#print axioms actual_gStar
end Prime23.ActualBase
