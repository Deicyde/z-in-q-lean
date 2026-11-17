import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_
import Mathlib.NumberTheory.Padics.PadicIntegers

/-! Abelian models over the p-adic integers. -/

open CategoryTheory AlgebraicGeometry

namespace ZInQBlueprint.AbelianModel

abbrev GroupScheme (R : Type) [CommRing R] := CommGrp (Over (Spec (.of R)))

/-- Base change of commutative group schemes along the map of spectra induced by `f`. -/
noncomputable abbrev baseChange {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) :
    GroupScheme R ⥤ GroupScheme S :=
  (Over.pullback (Spec.map (CommRingCat.ofHom f))).mapCommGrp

/-- The defining conditions on the structure morphism of an abelian scheme. -/
structure IsAbelianScheme {R : Type} [CommRing R] (G : GroupScheme R) : Prop where
  proper : IsProper G.X.hom
  smooth : Smooth G.X.hom
  geometricallyConnected : GeometricallyConnected G.X.hom

theorem finite_presentation_data {R : Type} [CommRing R] {G : GroupScheme R}
    (h : IsAbelianScheme G) :
    QuasiCompact G.X.hom ∧ QuasiSeparated G.X.hom ∧ LocallyOfFinitePresentation G.X.hom ∧
      LocallyOfFiniteType G.X.hom ∧ Flat G.X.hom := by
  let := h.proper
  let := h.smooth
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- Abelian schemes remain abelian after extension of scalars. -/
theorem isAbelianScheme_baseChange {R S : Type} [CommRing R] [CommRing S] (f : R →+* S)
    {G : GroupScheme R} (h : IsAbelianScheme G) : IsAbelianScheme ((baseChange f).obj G) := by
  let := h.proper
  let := h.smooth
  let := h.geometricallyConnected
  let g := Limits.pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom f))
  exact ⟨inferInstanceAs (IsProper g), inferInstanceAs (Smooth g),
    inferInstanceAs (GeometricallyConnected g)⟩

variable (p : ℕ) [Fact p.Prime]

/-- Good reduction of the specified group scheme over Q_p means that it is the
generic fibre of an abelian scheme over Z_p, as a group scheme over Q_p. -/
def HasGoodReduction (A : GroupScheme ℚ_[p]) : Prop :=
  ∃ M : GroupScheme ℤ_[p], IsAbelianScheme M ∧
    Nonempty ((baseChange (algebraMap ℤ_[p] ℚ_[p])).obj M ≅ A)

theorem hasGoodReduction_of_iso {A B : GroupScheme ℚ_[p]} (e : A ≅ B)
    (h : HasGoodReduction p A) : HasGoodReduction p B := by
  obtain ⟨M, hM, ⟨i⟩⟩ := h
  exact ⟨M, hM, ⟨i ≪≫ e⟩⟩

theorem hasGoodReduction_iso_iff {A B : GroupScheme ℚ_[p]} (e : A ≅ B) :
    HasGoodReduction p A ↔ HasGoodReduction p B :=
  ⟨hasGoodReduction_of_iso p e, hasGoodReduction_of_iso p e.symm⟩

abbrev GoodReductionAt (A : GroupScheme ℚ) : Prop :=
  HasGoodReduction p ((baseChange (algebraMap ℚ ℚ_[p])).obj A)

/-- An isomorphism of group schemes over Q transports good reduction at p. -/
theorem goodReductionAt_iso_iff {A B : GroupScheme ℚ} (e : A ≅ B) :
    GoodReductionAt p A ↔ GoodReductionAt p B :=
  hasGoodReduction_iso_iff p ((baseChange (algebraMap ℚ ℚ_[p])).mapIso e)

end ZInQBlueprint.AbelianModel

#print axioms ZInQBlueprint.AbelianModel.IsAbelianScheme
#print axioms ZInQBlueprint.AbelianModel.finite_presentation_data
#print axioms ZInQBlueprint.AbelianModel.isAbelianScheme_baseChange
#print axioms ZInQBlueprint.AbelianModel.HasGoodReduction
#print axioms ZInQBlueprint.AbelianModel.hasGoodReduction_of_iso
#print axioms ZInQBlueprint.AbelianModel.hasGoodReduction_iso_iff
#print axioms ZInQBlueprint.AbelianModel.goodReductionAt_iso_iff
