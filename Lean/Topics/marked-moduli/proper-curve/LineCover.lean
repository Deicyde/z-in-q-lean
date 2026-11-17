import ChartBaseChange
import Mathlib.AlgebraicGeometry.RelativeGluing
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! The double cover as a finite morphism to the line with its two standard charts. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial LaurentPolynomial
namespace ZInQBlueprint.BinaryCover
noncomputable section
variable (R : Type) [CommRing R]
local notation "L" => LaurentPolynomial R
attribute [local instance] Polynomial.algebra QuadraticAlgebra.algebra

/-- The open immersion of the punctured affine line. -/
def linePuncture := scalarMap R[X] L

instance : IsOpenImmersion (linePuncture R) := IsOpenImmersion.of_isLocalization (X : R[X])

def reciprocal : Spec (.of L) ≅ Spec (.of L) :=
  Scheme.Spec.mapIso (invert (R := R)).toRingEquiv.toCommRingCatIso.op

def lineArrow : Bool → (Spec (.of L) ⟶ Spec (.of R[X]))
  | false => linePuncture R
  | true => (reciprocal R).inv ≫ linePuncture R

instance (i : Bool) : IsOpenImmersion (lineArrow R i) := by
  cases i
  · exact inferInstanceAs (IsOpenImmersion (linePuncture R))
  · exact inferInstanceAs (IsOpenImmersion ((reciprocal R).inv ≫ linePuncture R))

abbrev lineDiagram := WidePushoutShape.wideSpan (Spec (.of L))
  (fun _ : Bool => Spec (.of R[X])) (lineArrow R)

instance lineMap_open : ∀ {i j : WidePushoutShape Bool} (e : i ⟶ j), IsOpenImmersion ((lineDiagram R).map e) := by
  intro i j e
  change WidePushoutShape.Hom i j at e
  cases e with
  | id i => exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  | init i => exact inferInstanceAs (IsOpenImmersion (lineArrow R i))

/-- The line obtained by gluing the affine lines along the reciprocal coordinate. -/
abbrev projectiveLine := colimit (lineDiagram R)
abbrev lineCover := Scheme.IsLocallyDirected.openCover (lineDiagram R)

instance : Category (lineCover R).I₀ := inferInstanceAs (Category (WidePushoutShape Bool))

instance : (lineCover R).LocallyDirected where
  trans hij := (lineDiagram R).map hij
  trans_id i := (lineDiagram R).map_id i
  trans_comp e f := (lineDiagram R).map_comp e f
  w {i j} e := by
    exact colimit.w (lineDiagram R) (show WidePushoutShape.Hom i j from e)
  property_trans e := lineMap_open R e
  directed {i j} x := by
    have h : (colimit.ι (lineDiagram R) i) (pullback.fst ((lineCover R).f i) ((lineCover R).f j) x) =
        (colimit.ι (lineDiagram R) j) (pullback.snd ((lineCover R).f i) ((lineCover R).f j) x) :=
      congrArg (fun m : pullback ((lineCover R).f i) ((lineCover R).f j) ⟶ _ => m x)
        (pullback.condition (f := (lineCover R).f i) (g := (lineCover R).f j))
    obtain ⟨k, a, b, y, h₁,h₂⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (lineDiagram R)).mp h
    use k, a, b, y
    apply (pullback.fst ((lineCover R).f i) ((lineCover R).f j)).injective
    exact (congrArg (fun m : (lineCover R).X k ⟶ (lineCover R).X i => m y)
      (pullback.lift_fst ((lineDiagram R).map a) ((lineDiagram R).map b) _)).trans h₁

def ordinateProjection (f : R[X]) := scalarMap R[X] (Cover f)
def puncturedProjection (f : R[X]) := scalarMap L (Punctured R f)

theorem finiteChart (f : R[X]) : IsFinite (ordinateProjection R f) := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R[X] (Cover f))))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem finitePuncture (f : R[X]) : IsFinite (puncturedProjection R f) := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap L (Punctured R f))))
  rw [IsFinite.SpecMap_iff]
  exact RingHom.finite_algebraMap.mpr inferInstance

theorem punctureSquare (f : R[X]) : IsPullback (puncture R f) (puncturedProjection R f)
    (ordinateProjection R f) (linePuncture R) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R[X] L (Cover f) (Punctured R f))).flip

theorem reciprocalSquare (f g : R[X]) (h : SexticOverlap R f g) :
    IsPullback (specIso (transition R h)).inv.left (puncturedProjection R f)
        (puncturedProjection R g) (reciprocal R).inv := by
  let : IsIso (specIso (transition R h)).inv.left :=
    inferInstanceAs (IsIso (((Over.forget _).mapIso (specIso (transition R h))).inv))
  apply IsPullback.of_horiz_isIso
  constructor
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  apply QuadraticAlgebra.ext
  · rfl
  · change invert.symm ((↑(laurentUnit R (-3))⁻¹ : L) * 0) = 0
    rw [mul_zero, map_zero]

theorem chartSquare (f g : R[X]) (h : SexticOverlap R f g) (i : Bool) :
    IsPullback (arrow R f g h i) (puncturedProjection R f) (ordinateProjection R (if i then g else f))
      (lineArrow R i) := by
  cases i
  · exact punctureSquare R f
  · exact (reciprocalSquare R f g h).paste_horiz (punctureSquare R g)

end
end ZInQBlueprint.BinaryCover

#print axioms ZInQBlueprint.BinaryCover.finiteChart
#print axioms ZInQBlueprint.BinaryCover.finitePuncture
#print axioms ZInQBlueprint.BinaryCover.chartSquare
