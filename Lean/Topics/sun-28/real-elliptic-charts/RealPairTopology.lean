import EllipticParameterModel
import HausdorffRealCurve

/-! Compactness and separation for both embeddings of Sun's exact curve. -/
namespace Sun28.RealCharts
open ZInQ WeierstrassCurve Sun28.Scalar Sun28.RealRatio
open scoped Sun28.RealCharts
noncomputable section

private theorem paper_smooth : (curve (-(3-sqrt2)^2)).IsElliptic := by
  have n : (3:K0)-sqrt2≠0 := by
    intro h
    have e : sqrt2 = (3:K0) := (sub_eq_zero.mp h).symm
    have q := sqrt2_sq
    rw [e] at q
    norm_num at q
  rw [WeierstrassCurve.isElliptic_iff,isUnit_iff_ne_zero]
  have discriminant : (curve (-(3-sqrt2)^2)).Δ = 64*(3-sqrt2)^6 := by
    simp [curve,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    ring
  rw [discriminant]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ n)

theorem compact_factor (σ : K0 →+* ℝ) : CompactSpace (EmbeddedPoint σ) := by
  let _ := paper_smooth
  exact elliptic_compactSpace ((curve (-(3-sqrt2)^2)).map σ)

theorem hausdorff_factor (σ : K0 →+* ℝ) : T2Space (EmbeddedPoint σ) :=
  elliptic_t2Space _

theorem compact_pair : CompactSpace RealPair := by
  let _ := compact_factor (place false)
  let _ := compact_factor (place true)
  infer_instance

theorem hausdorff_pair : T2Space RealPair := by
  let _ := hausdorff_factor (place false)
  let _ := hausdorff_factor (place true)
  infer_instance

end
end Sun28.RealCharts
#print axioms Sun28.RealCharts.compact_factor
#print axioms Sun28.RealCharts.hausdorff_factor
#print axioms Sun28.RealCharts.compact_pair
#print axioms Sun28.RealCharts.hausdorff_pair
