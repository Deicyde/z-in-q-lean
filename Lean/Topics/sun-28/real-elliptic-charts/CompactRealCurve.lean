import ProjectiveParameter
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.MetricSpace.ProperSpace

/-! Compactness of the nonsingular real Weierstrass cubic with its projective topology. -/
namespace Sun28.RealCharts
open WeierstrassCurve Set
open scoped WeierstrassCurve.Projective Sun28.RealCharts
noncomputable section

private abbrev V := Fin 3 → ℝ

/-- Every point of a smooth projective real Weierstrass cubic on a nonzero line is nonsingular. -/
theorem nonsingular_of_nonzero (W : WeierstrassCurve ℝ) [W.IsElliptic] {v : V}
    (live : v≠0) (eq : W.toProjective.Equation v) : W.toProjective.Nonsingular v := by
  by_cases z : v 2=0
  · have x : v 0=0 := Projective.X_eq_zero_of_Z_eq_zero eq z
    have y : v 1≠0 := by
      intro ey
      apply live
      funext i
      fin_cases i
      · exact x
      · exact ey
      · exact z
    apply (Projective.nonsingular_of_Z_eq_zero z).2
    refine ⟨eq, Or.inr ?_⟩
    simpa [x] using pow_ne_zero 2 y
  · exact (Projective.nonsingular_of_Z_ne_zero z).2
      (Affine.equation_iff_nonsingular.mp ((Projective.equation_of_Z_ne_zero z).1 eq))

private def classOf (v : V) : Plane := Quotient.mk (MulAction.orbitRel ℝˣ V) v

private def unitCubic (W : WeierstrassCurve ℝ) := Metric.sphere (0:V) 1 ∩ {v : V | W.toProjective.Equation v}

private theorem unitCubic_compact (W : WeierstrassCurve ℝ) : IsCompact (unitCubic W) := by
  apply (isCompact_sphere (0:V) 1).inter_right
  exact isClosed_eq (MvPolynomial.continuous_eval _) continuous_const

private theorem unitCubic_image (W : WeierstrassCurve ℝ) [W.IsElliptic] :
    classOf '' unitCubic W = Set.range (fun Q : W.toAffine.Point => Q.toProjective.point) := by
  ext q
  constructor
  · rintro ⟨v,⟨unit,eq⟩,rfl⟩
    have norm : ‖v‖ = 1 := by simpa [Metric.mem_sphere,dist_zero_right] using unit
    have live : v≠0 := by rintro rfl; simp at norm
    let Q : W.toProjective.Point := { point := classOf v, nonsingular := nonsingular_of_nonzero W live eq }
    let E := Projective.Point.toAffineAddEquiv W
    refine ⟨E Q,?_⟩
    exact congrArg Projective.Point.point (E.symm_apply_apply Q)
  · rintro ⟨Q,rfl⟩
    have representative (v : V) (live : v≠0) (eq : W.toProjective.Equation v) :
        classOf v ∈ classOf '' unitCubic W := by
      let a := ‖v‖⁻¹
      have nonzero : a≠0 := inv_ne_zero (norm_ne_zero_iff.mpr live)
      refine ⟨NormedSpace.normalize v,⟨?_,?_⟩,?_⟩
      · simpa [Metric.mem_sphere,dist_zero_right] using NormedSpace.norm_normalize live
      · exact (Projective.equation_smul v (isUnit_iff_ne_zero.mpr nonzero)).2 eq
      · exact Projective.smul_eq v (isUnit_iff_ne_zero.mpr nonzero)
    cases Q with
    | zero =>
      apply representative ![0,1,0] _ Projective.equation_zero
      intro zero
      have y:=congrFun zero (1:Fin 3)
      norm_num at y
    | some x y on =>
      apply representative ![x,y,1] _ ((Projective.equation_some x y).2 on.1)
      intro zero
      have z:=congrFun zero (2:Fin 3)
      norm_num at z

/-- The regular projective topology on a real elliptic curve is compact. -/
theorem elliptic_compactSpace (W : WeierstrassCurve ℝ) [W.IsElliptic] : CompactSpace W.toAffine.Point := by
  constructor
  have induced : Topology.IsInducing (fun Q : W.toAffine.Point => Q.toProjective.point) := ⟨rfl⟩
  rw [induced.isCompact_iff,Set.image_univ,←unitCubic_image W]
  exact (unitCubic_compact W).image continuous_quotient_mk'

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.nonsingular_of_nonzero
#print axioms Sun28.RealCharts.elliptic_compactSpace
