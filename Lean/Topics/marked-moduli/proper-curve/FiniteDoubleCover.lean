import LineCover

/-! Relative gluing identifies the inverse images of both standard coordinate charts. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section
variable (R : Type) [CommRing R]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance : Quiver.IsThin (lineCover R).I₀ := inferInstanceAs (Quiver.IsThin (WidePushoutShape Bool))

def component (f g : R[X]) (h : SexticOverlap R f g) :
    (i : WidePushoutShape Bool) → (diagram R f g h).obj i ⟶ (lineDiagram R).obj i
  | none => puncturedProjection R f
  | some i => ordinateProjection R (if i then g else f)

/-- Forget the square-root coordinate in both charts and on their intersection. -/
def doubleCoverData (f g : R[X]) (h : SexticOverlap R f g) :
    (lineCover R).RelativeGluingData where
  functor := diagram R f g h
  natTrans := {
    app := component R f g h
    naturality := by
      intro i j a
      change WidePushoutShape.Hom i j at a
      cases a with
      | id i => exact Category.id_comp _ |>.trans (Category.comp_id _).symm
      | init i => exact (chartSquare R f g h i).w }
  equifibered := by
    intro i j a
    change WidePushoutShape.Hom i j at a
    cases a with
    | id i => exact IsPullback.of_id_fst
    | init i => exact chartSquare R f g h i

def toLine (f g : R[X]) (h : SexticOverlap R f g) : glued R f g h ⟶ projectiveLine R :=
  (doubleCoverData R f g h).toBase

theorem chart_pullback (f g : R[X]) (h : SexticOverlap R f g) (i : WidePushoutShape Bool) :
    IsPullback (component R f g h i) (colimit.ι (diagram R f g h) i)
      (colimit.ι (lineDiagram R) i) (toLine R f g h) :=
  (doubleCoverData R f g h).isPullback_natTrans_ι_toBase i

theorem finite_toLine (f g : R[X]) (h : SexticOverlap R f g) : IsFinite (toLine R f g h) := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @AlgebraicGeometry.IsFinite) (lineCover R)
  intro i
  change IsFinite (pullback.snd (toLine R f g h) (colimit.ι (lineDiagram R) i))
  have s := (chart_pullback R f g h i).flip
  have finite : IsFinite (component R f g h i) := by
    cases i with
    | none => exact finitePuncture R f
    | some j => exact finiteChart R _
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @AlgebraicGeometry.IsFinite) s.isoPullback.hom,
      s.isoPullback_hom_snd]
  exact finite

def lineStructure : projectiveLine R ⟶ Spec (.of R) :=
  WidePushout.desc (arrows := lineArrow R) (scalarMap R (LaurentPolynomial R))
    (fun _ => scalarMap R R[X]) (by
      intro i
      cases i
      · change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]
        congr 1
        exact CommRingCat.hom_ext (RingHom.ext Polynomial.toLaurent_C)
      · change (Spec.map _ ≫ Spec.map _) ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro r
        change LaurentPolynomial.invert.symm (toLaurent (Polynomial.C r)) = LaurentPolynomial.C r
        rw [Polynomial.toLaurent_C, LaurentPolynomial.invert_symm, LaurentPolynomial.invert_C])

theorem curve_structure (f g : R[X]) (h : SexticOverlap R f g) :
    toLine R f g h ≫ lineStructure R = (gluedOver R f g h).hom := by
  apply colimit.hom_ext
  intro i
  rw [← Category.assoc, (chart_pullback R f g h i).w.symm, Category.assoc]
  cases i with
  | none =>
    change puncturedProjection R f ≫ (WidePushout.head (lineArrow R) ≫ lineStructure R) =
      WidePushout.head (arrow R f g h) ≫ (gluedOver R f g h).hom
    rw [show WidePushout.head (lineArrow R) ≫ lineStructure R = scalarMap R (LaurentPolynomial R)
          from WidePushout.head_desc ..,
        show WidePushout.head (arrow R f g h) ≫ (gluedOver R f g h).hom =
          (SpecOver (R := R) (Punctured R f)).hom from WidePushout.head_desc ..]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl
  | some j =>
    change ordinateProjection R _ ≫ (WidePushout.ι (lineArrow R) j ≫ lineStructure R) =
      WidePushout.ι (arrow R f g h) j ≫ (gluedOver R f g h).hom
    rw [show WidePushout.ι (lineArrow R) j ≫ lineStructure R = scalarMap R R[X]
          from WidePushout.ι_desc .., show WidePushout.ι (arrow R f g h) j ≫ (gluedOver R f g h).hom =
        (SpecOver (R := R) (Cover (if j then g else f))).hom from WidePushout.ι_desc ..]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl

theorem paper_toLine_finite (K : Type) [Field K] [CharZero K] (u : ℚ) :
    IsFinite (toLine K _ _ (paper_overlap K u)) := finite_toLine K _ _ _

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.chart_pullback
#print axioms ZInQBlueprint.BinaryCover.finite_toLine
#print axioms ZInQBlueprint.BinaryCover.curve_structure
#print axioms ZInQBlueprint.BinaryCover.paper_toLine_finite
