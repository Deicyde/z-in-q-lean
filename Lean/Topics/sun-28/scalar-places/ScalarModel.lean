import ScalarCoordinates

/-! Coordinates under the integral unit change between the two short models. -/
namespace Sun28.ScalarPlaces
open ZInQ ZInQ.Mult ZInQ.Syntax Sun28.Scalar Sun28.WitnessIndices WeierstrassCurve.Affine
noncomputable section

private def transport {a b : K0} (e : a=b) : (curve a).Point ≃+ (curve b).Point := by
  subst b
  exact AddEquiv.refl _

private theorem transport_coordinates {a b : K0} (e : a=b) (Q : (curve a).Point) :
    reciprocal (transport e Q)=reciprocal Q ∧ parameter (transport e Q)=parameter Q := by
  subst b
  exact ⟨rfl,rfl⟩

theorem scalar_coordinates (Q : CPoint) :
    reciprocal (scalarEquiv Q)=reciprocal (b:= -delta^2) Q ∧
    parameter (scalarEquiv Q)=parameter (b:= -delta^2) Q :=
  transport_coordinates (b:= -(3-sqrt2)^2) (by rw [delta_eq]) Q

theorem scaled_coordinates (Q : genCurve.toAffine.Point) :
    reciprocal (scalarEquiv (theta Q))=xi Q/(epsilon^4) ∧
    parameter (scalarEquiv (theta Q))=zCoord (A:= -genD^2) Q/(epsilon^2) := by
  rw [(scalar_coordinates _).1,(scalar_coordinates _).2]
  cases Q with
  | zero => change (0:K0)=0/_ ∧ 0=0/_; simp
  | some x y h =>
    rw [theta_some]
    change (epsilon^4*x)⁻¹=x⁻¹/epsilon^4 ∧
      -(epsilon^4*x)/(epsilon^6*y)=(-x/y)/epsilon^2
    constructor
    · simp [div_eq_mul_inv]
    · by_cases e : y=0
      · simp [e]
      field_simp [e,epsilon_ne_zero]

theorem scaled_multiple (n : ℤ) :
    reciprocal (scalarEquiv (n • P))=xi (n • genP0)/epsilon^4 ∧
    parameter (scalarEquiv (n • P))=zCoord (A:= -genD^2) (n • genP0)/epsilon^2 := by
  have h : theta (n • genP0)=n • P := by rw [←normalized_index,theta.apply_symm_apply]
  simpa only [h] using scaled_coordinates (n • genP0)

theorem unit_epsilon {π : Zs} (hπ : Prime π) : vP π hπ epsilon=0 := by
  rw [vP_apply hπ epsilon_ne_zero,←toK0_epsilonZ,←epsUnit_val,vp_unit hπ]
  rfl

end
end Sun28.ScalarPlaces
#print axioms Sun28.ScalarPlaces.scalar_coordinates
#print axioms Sun28.ScalarPlaces.scaled_coordinates
#print axioms Sun28.ScalarPlaces.scaled_multiple
#print axioms Sun28.ScalarPlaces.unit_epsilon
