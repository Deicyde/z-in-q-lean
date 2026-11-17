import ThreeScales

namespace Sun28.Ordinary
open ZInQ ZInQ.Mult WeierstrassCurve.Affine Height
noncomputable section

/-- Product evaluated using the reciprocal coordinate in Sun's actual pole tests. -/
def paperProduct (n : Fin 4 → ℤ) : K0 :=
  ∏ i, (Scalar.reciprocal (n i • Scalar.paperGenerator sqrt2_sq))⁻¹

private def affineX {A : WeierstrassCurve.Affine K0} : A.Point → K0
  | .zero => 0
  | .some x _ _ => x

theorem indexX_paper (m : ℤ) :
    indexX m = (Scalar.reciprocal (m • Scalar.paperGenerator sqrt2_sq))⁻¹ := by
  have map_eq {A B : WeierstrassCurve.Affine K0} (e : A=B)
      (p : A.Point) (q : B.Point) (same : HEq p q) :
      affineX (m • p) = affineX (m • q) := by
    subst B
    rw [eq_of_heq same]
  have eq := map_eq generator_cast.1 _ _ generator_cast.2
  have xeq (Q : curveC.toAffine.Point) : affineX Q = curveX Q := by cases Q <;> rfl
  have seq (Q : (Scalar.curve (-(3-sqrt2)^2)).Point) :
      affineX Q = (Scalar.reciprocal Q)⁻¹ := by
    cases Q <;> simp [affineX,Scalar.reciprocal]
  rw [xeq,seq] at eq
  exact eq.symm

theorem coordinateProduct_paper (n : Fin 4 → ℤ) : coordinateProduct n=paperProduct n := by
  unfold coordinateProduct paperProduct
  exact Finset.prod_congr rfl (fun i _ => indexX_paper (n i))

theorem paper_three_scales (n : Fin 4 → ℤ) (odd : ∀ j, Odd (n j)) (η : ℚ) (nonzero : η≠0) :
    ∀ H : ℝ, 1 ≤ H → (∀ j, logHeight₁ ((scaleRoot (paperProduct n).re (paperProduct n).im j)^2*η) ≤ H) →
      indexSize n ^ 2 ≤ (3/2)*H+10 := by
  rw [←coordinateProduct_paper]
  exact three_scales n odd η nonzero

end
end Sun28.Ordinary
#print axioms Sun28.Ordinary.indexX_paper
#print axioms Sun28.Ordinary.coordinateProduct_paper
#print axioms Sun28.Ordinary.paper_three_scales
