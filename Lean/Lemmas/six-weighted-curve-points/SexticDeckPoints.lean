import SexticDeck
/-! The deck involution over the line and its action on every geometric point. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.WeightedCurvePoints
open BinaryCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem star_scalar {R : Type} [CommRing R] (a b : R) :
    starSpec (QuadraticAlgebra R a b) ≫ scalarMap R (QuadraticAlgebra R a b) =
      scalarMap R (QuadraticAlgebra R a b) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  change star (algebraMap R (QuadraticAlgebra R a b) r) = _
  apply QuadraticAlgebra.ext <;> simp

variable {K : Type} [Field K] (f g : K[X]) (h : SexticOverlap K f g)

theorem deck_line : deck f g h ≫ toLine K f g h = toLine K f g h := by
  apply colimit.hom_ext
  intro i
  have sq := (chart_pullback K f g h i).w
  change colimit.ι _ i ≫ colimMap _ ≫ _ = _
  rw [ι_colimMap_assoc, ←sq, ←Category.assoc]
  have e : (starDiagram f g h).app i ≫ component K f g h i = component K f g h i := by
    cases i <;> apply star_scalar
  rw [e]

def deckOver : gluedOver K f g h ≅ gluedOver K f g h := by
  let e : glued K f g h ≅ glued K f g h := ⟨deck f g h, deck f g h, deck_sq f g h, deck_sq f g h⟩
  refine Over.isoMk e ?_
  change deck f g h ≫ (gluedOver K f g h).hom = (gluedOver K f g h).hom
  rw [←curve_structure, ←Category.assoc,deck_line]

def flip (p : AffineCoords K f) : AffineCoords K f :=
  ⟨(p.1.1,-p.1.2),by simpa using p.2⟩

theorem affine_flip (p : AffineCoords K f) :
    (affineSection K f p).left ≫ starSpec (Cover f) = (affineSection K f (flip f p)).left := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro t
  change (aeval p.1.1) (t.re + 0*t.im) + (aeval p.1.1) (-t.im)*p.1.2 = (aeval p.1.1) t.re + (aeval p.1.1) t.im * (-p.1.2)
  simp

theorem chart_deck (i : Bool) (p : AffineCoords K (if i then g else f)) :
    chartSection f g h i p ≫ (deckOver f g h).hom = chartSection f g h i (flip _ p) := by
  apply Over.OverMorphism.ext
  change ((affineSection K _ p).left ≫ (chartInclusion K f g h i).left) ≫ deck f g h =
    (affineSection K _ (flip _ p)).left ≫ _
  rw [Category.assoc,deck_chart,← Category.assoc,affine_flip]

variable [CharZero K]

theorem chart_fixed_iff (i : Bool) (p : AffineCoords K (if i then g else f)) :
    chartSection f g h i p ≫ (deckOver f g h).hom = chartSection f g h i p ↔ p.1.2=0 := by
  rw [chart_deck, (chartSection_injective f g h i).eq_iff]
  constructor
  · intro e
    have he : -p.1.2 = p.1.2 := congrArg (fun z => z.1.2) e
    linear_combination -(1/2:K)*he
  · intro hp
    apply Subtype.ext
    exact Prod.ext rfl (by simp [flip,hp])

end
end ZInQBlueprint.WeightedCurvePoints
#print axioms ZInQBlueprint.WeightedCurvePoints.deck_line
#print axioms ZInQBlueprint.WeightedCurvePoints.deckOver
#print axioms ZInQBlueprint.WeightedCurvePoints.chart_deck
#print axioms ZInQBlueprint.WeightedCurvePoints.chart_fixed_iff
