import GluedCurvePoints

/-! The scheme automorphism obtained by conjugation in the quadratic algebras
of both affine charts and the Laurent overlap. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial LaurentPolynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K]

def starSpec (A : Type) [CommRing A] [StarRing A] : Spec (.of A) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (starRingEnd A))

theorem starSpec_sq (A : Type) [CommRing A] [StarRing A] : starSpec A ≫ starSpec A = 𝟙 _ := by
  change Spec.map _ ≫ Spec.map _ = 𝟙 _
  rw [←Spec.map_comp,← Spec.map_id]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext (starRingEnd_self_apply))

theorem puncture_star (f : K[X]) :
    puncture K f ≫ starSpec (Cover f) = starSpec (Punctured K f) ≫ puncture K f := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact QuadraticAlgebra.mapRingHom_star _ _ _ p

theorem transition_star (f g : K[X]) (h : SexticOverlap K f g) :
    (specIso (transition K h)).hom.left ≫ starSpec (Punctured K f) =
      starSpec (Punctured K g) ≫ (specIso (transition K h)).hom.left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change transition K h (star p) = star (transition K h p)
  apply QuadraticAlgebra.ext
  · change invert (p.re + (toLaurent (0 : K[X])) * p.im) = invert p.re + toLaurent (0 : K[X]) * _
    have trivialPart (w p : LaurentPolynomial K) : w + toLaurent (0 : K[X]) * p = w := by simp
    rw [trivialPart,trivialPart]
  · change _ * invert (-p.im) = -(_ * invert p.im)
    rw [map_neg,mul_neg]

theorem arrow_star (f g : K[X]) (h : SexticOverlap K f g) (i : Bool) :
    arrow K f g h i ≫ starSpec (Cover (if i then g else f)) =
      starSpec (Punctured K f) ≫ arrow K f g h i := by
  cases i
  · exact puncture_star f
  · let e : Spec (.of (Punctured K g)) ≅ Spec (.of (Punctured K f)) := (Over.forget _).mapIso (specIso (transition K h))
    change (e.inv ≫ puncture K g) ≫ starSpec (Cover g) = starSpec (Punctured K f) ≫ e.inv ≫ puncture K g
    have he : e.inv ≫ starSpec (Punctured K g) = starSpec (Punctured K f) ≫ e.inv := by
      apply e.eq_comp_inv.mpr
      rw [Category.assoc]
      apply e.inv_comp_eq.mpr
      exact (transition_star f g h).symm
    rw [Category.assoc,puncture_star,← Category.assoc,he,Category.assoc]

def starComponent (f g : K[X]) (h : SexticOverlap K f g) :
    (i : WidePushoutShape Bool) → (diagram K f g h).obj i ⟶ (diagram K f g h).obj i
  | none => starSpec (Punctured K f)
  | some i => starSpec (Cover (if i then g else f))

def starDiagram (f g : K[X]) (h : SexticOverlap K f g) : diagram K f g h ⟶ diagram K f g h where
  app := starComponent f g h
  naturality := by
    intro i j a
    change WidePushoutShape.Hom i j at a
    cases a with
    | id i => exact (Category.id_comp _).trans (Category.comp_id _).symm
    | init i => exact arrow_star f g h i

def deck (f g : K[X]) (h : SexticOverlap K f g) : glued K f g h ⟶ glued K f g h :=
  colimMap (starDiagram f g h)

theorem deck_chart (f g : K[X]) (h : SexticOverlap K f g) (i : Bool) :
    (chartInclusion K f g h i).left ≫ deck f g h =
      starSpec (Cover (if i then g else f)) ≫ (chartInclusion K f g h i).left :=
  ι_colimMap _ _

theorem deck_sq (f g : K[X]) (h : SexticOverlap K f g) : deck f g h ≫ deck f g h = 𝟙 _ := by
  apply colimit.hom_ext
  intro i
  change colimit.ι _ i ≫ colimMap _ ≫ colimMap _ = colimit.ι _ i ≫ 𝟙 (colimit (diagram K f g h))
  rw [ι_colimMap_assoc,ι_colimMap,← Category.assoc,Category.comp_id]
  have e : (starDiagram f g h).app i ≫ (starDiagram f g h).app i = 𝟙 _ := by
    cases i <;> apply starSpec_sq
  rw [e,Category.id_comp]
end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.arrow_star
#print axioms ZInQBlueprint.WeightedCurvePoints.deck_chart
#print axioms ZInQBlueprint.WeightedCurvePoints.deck_sq
