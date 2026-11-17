import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Tactic

/-! The parameter −X/Y on the Y-chart of the ordinary real projective plane. -/
namespace Sun28.RealCharts
open WeierstrassCurve
open scoped WeierstrassCurve.Projective
noncomputable section

abbrev Plane := Projective.PointClass ℝ

def homogeneousParameter : Plane → ℝ :=
  Quotient.lift (fun v : Fin 3 → ℝ => -(v 0)/v 1) (by
    rintro x y ⟨u,rfl⟩
    change -(↑u*y 0)/(↑u*y 1) = -(y 0)/y 1
    by_cases zero : y 1=0
    · simp [zero]
    · field_simp [u.ne_zero,zero])

theorem homogeneous_continuousAt (v : Fin 3 → ℝ) (nonzero : v 1≠0) :
    ContinuousAt homogeneousParameter (Quotient.mk (MulAction.orbitRel ℝˣ (Fin 3→ℝ)) v) := by
  have quotient : IsOpenQuotientMap (Quotient.mk (MulAction.orbitRel ℝˣ (Fin 3→ℝ))) :=
    MulAction.isOpenQuotientMap_quotientMk
  apply quotient.continuousAt_comp_iff.mp
  change ContinuousAt (fun x : Fin 3→ℝ => -(x 0)/x 1) v
  exact (continuous_apply 0).continuousAt.neg.div (continuous_apply 1).continuousAt nonzero

/-- The pullback of the homogeneous-coordinate quotient topology on real points. -/
@[instance_reducible] def ellipticTopology (W : WeierstrassCurve.Affine ℝ) : TopologicalSpace W.Point :=
  TopologicalSpace.induced (fun Q : W.Point => Q.toProjective.point) inferInstance

/-- This scoped instance always gives the projective real topology. -/
scoped instance topologyOnPoints (W : WeierstrassCurve.Affine ℝ) : TopologicalSpace W.Point :=
  ellipticTopology W

open scoped Sun28.RealCharts

theorem projective_continuous (W : WeierstrassCurve.Affine ℝ) :
    Continuous (fun Q : W.Point => Q.toProjective.point) :=
  continuous_induced_dom

def parameterOn (W : WeierstrassCurve.Affine ℝ) : W.Point → ℝ :=
  fun Q => homogeneousParameter Q.toProjective.point

theorem at_infinity (W : WeierstrassCurve.Affine ℝ) :
    parameterOn W 0=0 ∧ ContinuousAt (parameterOn W) 0 := by
  refine ⟨?_,?_⟩
  · change -(0:ℝ)/1=0
    norm_num
  · have h : ContinuousAt homogeneousParameter (0 : W.Point).toProjective.point :=
      homogeneous_continuousAt ![0,1,0] (by change (1:ℝ)≠0; norm_num)
    exact ContinuousAt.comp (f := fun Q : W.Point => Q.toProjective.point) h (projective_continuous W).continuousAt

theorem at_affine (W : WeierstrassCurve.Affine ℝ) (x y : ℝ) (on : W.Nonsingular x y) :
    parameterOn W (.some _ _ on) = -x/y ∧ (y≠0 → ContinuousAt (parameterOn W) (.some _ _ on)) := by
  refine ⟨rfl,fun yn => ?_⟩
  have h : ContinuousAt homogeneousParameter (Affine.Point.some x y on : W.Point).toProjective.point :=
    homogeneous_continuousAt ![x,y,1] yn
  exact ContinuousAt.comp (f := fun Q : W.Point => Q.toProjective.point) h (projective_continuous W).continuousAt

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.homogeneous_continuousAt
#print axioms Sun28.RealCharts.projective_continuous
#print axioms Sun28.RealCharts.at_infinity
#print axioms Sun28.RealCharts.at_affine
