import BinaryCover
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.QuadraticAlgebra.BaseChange
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.RingTheory.Localization.BaseChange

/-! A two-chart scheme for a binary sextic. -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial LaurentPolynomial
open scoped LaurentPolynomial

namespace ZInQBlueprint.BinaryCover

noncomputable section
variable (R : Type) [CommRing R]
local notation "L" => LaurentPolynomial R

/-- The coordinate ring on the punctured affine chart. -/
abbrev Punctured (f : R[X]) :=
  QuadraticAlgebra L (algebraMap R[X] L f) (algebraMap R[X] L 0)

attribute [local instance] QuadraticAlgebra.algebra

theorem punctured_localization (f : R[X]) :
    IsLocalization.Away (algebraMap R[X] (Cover f) X) (Punctured R f) := by
  rw [IsLocalization.Away, ← Algebra.algebraMapSubmonoid_powers]
  apply (Algebra.isLocalization_iff_isPushout (.powers X) L).mpr
  rw [Algebra.IsPushout.comm]
  exact QuadraticAlgebra.isPushout L f 0

def puncture (f : R[X]) : Spec (.of (Punctured R f)) ⟶ Spec (.of (Cover f)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (Cover f) (Punctured R f)))

instance (f : R[X]) : IsOpenImmersion (puncture R f) := by
  let := punctured_localization R f
  exact IsOpenImmersion.of_isLocalization (algebraMap R[X] (Cover f) X)

def laurentUnit (n : ℤ) : Lˣ := unitOfInvertible (T n : L)

/-- The Laurent-polynomial relation for the two standard coordinates of a
binary sextic. It states f(1/t) = t⁻⁶ g(t). -/
def SexticOverlap (f g : R[X]) : Prop :=
  invert (toLaurent f) = (T (-3) : L)^2 * toLaurent g

def transition {f g : R[X]} (h : SexticOverlap R f g) : Punctured R f ≃ₐ[R] Punctured R g := by
  dsimp only [Punctured, algebraMap_eq_toLaurent, map_zero]
  exact squareEquiv invert (laurentUnit R (-3)) h

/-- The common open maps to chart f by localization and to chart g by
the inverse of the weighted coordinate change followed by localization. -/
def arrow (f g : R[X]) (h : SexticOverlap R f g) :
    (i : Bool) → Spec (.of (Punctured R f)) ⟶ Spec (.of (Cover (if i then g else f)))
  | false => puncture R f
  | true => (specIso (transition R h)).inv.left ≫ puncture R g

instance (f g : R[X]) (h : SexticOverlap R f g) (i : Bool) :
    IsOpenImmersion (arrow R f g h i) := by
  cases i
  · exact inferInstanceAs (IsOpenImmersion (puncture R f))
  · change IsOpenImmersion ((specIso (transition R h)).inv.left ≫ puncture R g)
    let : IsIso (specIso (transition R h)).inv.left :=
      inferInstanceAs (IsIso (((Over.forget _).mapIso (specIso (transition R h))).inv))
    exact @IsOpenImmersion.comp _ _ _ (specIso (transition R h)).inv.left (puncture R g)
      (IsOpenImmersion.of_isIso _) (inferInstanceAs (IsOpenImmersion (puncture R g)))

abbrev diagram (f g : R[X]) (h : SexticOverlap R f g) :=
  WidePushoutShape.wideSpan (Spec (.of (Punctured R f)))
    (fun i : Bool => Spec (.of (Cover (if i then g else f)))) (arrow R f g h)

instance (f g : R[X]) (h : SexticOverlap R f g) :
    ∀ {i j} (a : i ⟶ j), IsOpenImmersion ((diagram R f g h).map a) := by
  intro i j a
  cases a with
  | id i => exact inferInstanceAs (IsOpenImmersion (𝟙 _))
  | init i => exact inferInstanceAs (IsOpenImmersion (arrow R f g h i))

/-- The scheme obtained by gluing the two affine double covers along the
principal opens, including points over x=0 and x=∞. -/
def glued (f g : R[X]) (h : SexticOverlap R f g) : Scheme := colimit (diagram R f g h)

def openCover (f g : R[X]) (h : SexticOverlap R f g) : (glued R f g h).OpenCover :=
  Scheme.IsLocallyDirected.openCover (diagram R f g h)

end
end ZInQBlueprint.BinaryCover

#print axioms ZInQBlueprint.BinaryCover.punctured_localization
#print axioms ZInQBlueprint.BinaryCover.transition
#print axioms ZInQBlueprint.BinaryCover.glued
#print axioms ZInQBlueprint.BinaryCover.openCover
