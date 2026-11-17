import SmoothCharts
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! Smoothness of the structural morphism for the actual rational two-chart sextic. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section

theorem smooth_chart {u : ℚ} (hu : u ∉ ZInQ.contactSet) (i : Bool) :
    Smooth (SpecOver (R := ℚ) (Cover (paper ℚ u i))).hom :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr (smooth_chart_algebra hu i))

/-- A binary double cover is smooth if both of its affine charts are smooth. -/
theorem smooth_glued {R : Type} [CommRing R] (f g : R[X]) (h : SexticOverlap R f g)
    (hf : Smooth (SpecOver (R := R) (Cover f)).hom)
    (hg : Smooth (SpecOver (R := R) (Cover g)).hom) :
    Smooth (gluedOver R f g h).hom := by
  let : IsZariskiLocalAtSource (@Smooth.{0}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth.{0}) (Q := @RingHom.Smooth)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @Smooth.{0}) (openCover R f g h)).mpr
  intro j
  change Smooth (colimit.ι (diagram R f g h) j ≫ (gluedOver R f g h).hom)
  cases j with
  | none =>
    have H := colimit.w (diagram R f g h) (WidePushoutShape.Hom.init false)
    change puncture R f ≫ (chartInclusion R f g h false).left = _ at H
    let v := (gluedOver R f g h).hom
    let c := chartInclusion R f g h false
    have e : colimit.ι (diagram R f g h) none ≫ v = puncture R f ≫ (SpecOver (R:=R) (Cover f)).hom :=
      (congrArg (fun k => k ≫ v) H.symm).trans
        ((Category.assoc (puncture R f) c.left v).trans
          (congrArg (fun k => puncture R f ≫ k) c.w))
    have ho : Smooth (puncture R f ≫ (SpecOver (R:=R) (Cover f)).hom) :=
      @IsZariskiLocalAtSource.comp (@Smooth.{0})
        (inferInstanceAs (IsZariskiLocalAtSource (@Smooth.{0}))) _ _ _ _ hf (puncture R f)
        (inferInstanceAs (IsOpenImmersion (puncture R f)))
    exact e.symm ▸ ho
  | some i =>
    change Smooth ((chartInclusion R f g h i).left ≫ (gluedOver R f g h).hom)
    rw [(chartInclusion R f g h i).w]
    cases i
    · exact hf
    · exact hg

theorem smooth_paperModel {u : ℚ} (hu : u ∉ ZInQ.contactSet) : Smooth (paperModel ℚ u).hom :=
  smooth_glued _ _ _ (smooth_chart hu false) (smooth_chart hu true)

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.smooth_chart
#print axioms ZInQBlueprint.BinaryCover.smooth_glued
#print axioms ZInQBlueprint.BinaryCover.smooth_paperModel
