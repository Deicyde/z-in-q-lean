import RealPairTopology

/-! On homogeneous coordinates the inverse of a real Weierstrass point is a linear map. -/
namespace Sun28.RealCharts
open WeierstrassCurve
open scoped WeierstrassCurve.Projective Sun28.RealCharts
noncomputable section

theorem continuous_projective_negation (W : WeierstrassCurve ℝ) : Continuous W.toProjective.negMap := by
  have linear : Continuous W.toProjective.neg := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_apply 0
    · change Continuous (fun v : Fin 3→ℝ => -v 1 - W.a₁*v 0-W.a₃*v 2)
      fun_prop
    · exact continuous_apply 2
  exact linear.quotient_map' (fun _ _ => Projective.neg_equiv)

theorem continuous_curve_negation (W : WeierstrassCurve ℝ) : ContinuousNeg W.toAffine.Point := by
  refine ⟨?_⟩
  have inducing : Topology.IsInducing (fun Q : W.toAffine.Point => Q.toProjective.point) := ⟨rfl⟩
  apply inducing.continuous_iff.mpr
  apply ((continuous_projective_negation W).comp (projective_continuous W)).congr
  intro Q
  change W.toProjective.negMap Q.toProjective.point = (-Q).toProjective.point
  have eq : (-Q).toProjective = -Q.toProjective :=
    (Projective.Point.toAffineAddEquiv W).symm.map_neg Q
  rw [eq,Projective.Point.neg_point]

theorem continuous_neg_pair : ContinuousNeg RealPair := by
  let _ := continuous_curve_negation ((Sun28.Scalar.curve (-(3-ZInQ.sqrt2)^2)).map (Sun28.RealRatio.place false))
  let _ := continuous_curve_negation ((Sun28.Scalar.curve (-(3-ZInQ.sqrt2)^2)).map (Sun28.RealRatio.place true))
  infer_instance

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.continuous_projective_negation
#print axioms Sun28.RealCharts.continuous_curve_negation
#print axioms Sun28.RealCharts.continuous_neg_pair
