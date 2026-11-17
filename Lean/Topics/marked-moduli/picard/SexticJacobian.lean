import ChartOpen
import PointedDescent
import PicardBaseChange
import JacobianReduction

/-! The pointed Picard comparison for the fixed glued sextic, and good reduction
from comparison of the represented group functors. -/
open CategoryTheory AlgebraicGeometry Opposite
open ZInQBlueprint.BinaryCover ZInQBlueprint.PicardBaseChange ZInQBlueprint.AbelianModel
namespace ZInQBlueprint.PointedSextic
noncomputable section
local notation "S" => Spec (CommRingCat.of ℚ)

/-- Inclusion of the integral-model infinity chart into the paper's rational model. -/
def infinityChart {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    SpecOver (R := ℚ) (Cover (fixed ℚ u true)) ⟶ paperModel ℚ u :=
  (paperChartIso hu true).hom ≫ chartInclusion ℚ _ _ (paper_overlap ℚ u) true

/-- A quadratic point on the very curve used for the Jacobian. -/
def paperPoint {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    SpecOver (R := ℚ) (SplittingField u) ⟶ paperModel ℚ u :=
  point u ≫ infinityChart hu

/-- Pointwise comparison on pointed tests implies comparison after fppf
sheafification on all rational tests for this curve. -/
theorem paper_sheafification_iso {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    {F G : (Over S)ᵒᵖ ⥤ GrpCat.{1}} (α : F ⟶ G)
    (h : ∀ T : Over S, Nonempty (T ⟶ paperModel ℚ u) → Function.Bijective (α.app (op T))) :
    IsIso ((presheafToSheaf (Scheme.fppfTopology.over S) (Type 1)).map
      (Functor.whiskerRight α (forget GrpCat))) :=
  sheafification_iso α u (infinityChart hu) h

private abbrev Jtop := Scheme.fppfTopology.over S

/-- The underlying point functor of any commutative group scheme is an fppf sheaf. -/
def pointSheaf (A : GroupScheme ℚ) : Sheaf Jtop (Type 0) :=
  ⟨points A ⋙ forget GrpCat, (isSheaf_iff_isSheaf_of_type _ _).mpr
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj A.X))⟩

/-- If a comparison of two representing group schemes is bijective on the
pointed tests for this sextic, it already determines an isomorphism over Q. -/
def iso_of_pointed_tests {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    {A B : GroupScheme ℚ} (α : points A ⟶ points B)
    (h : ∀ T : Over S, Nonempty (T ⟶ paperModel ℚ u) → Function.Bijective (α.app (op T))) :
    A ≅ B := by
  let r : pointSheaf A ⟶ pointSheaf B := ⟨Functor.whiskerRight α (forget GrpCat)⟩
  obtain ⟨hI, hS⟩ := locally_bijective α u (infinityChart hu) h
  let : IsIso r := (Sheaf.isLocallyBijective_iff_isIso r).mp
    ⟨(Presheaf.isLocallyInjective_forget_iff Jtop α).mpr hI,
      (Presheaf.isLocallySurjective_iff_whisker_forget Jtop α).mp hS⟩
  have is : IsIso (Functor.whiskerRight α (forget GrpCat)) :=
    inferInstanceAs (IsIso ((sheafToPresheaf Jtop (Type 0)).map r))
  have app := (NatTrans.isIso_iff_isIso_app _).mp is
  let : IsIso α := (NatTrans.isIso_iff_isIso_app _).mpr (fun T => by
    let : IsIso ((forget GrpCat).map (α.app T)) := app T
    exact isIso_of_reflects_iso (α.app T) (forget GrpCat))
  exact groupIso (asIso α)

open GoodReductionCharts PrimitiveParameters RationalClusters IsDiscreteValuationRing

/-- Specializing a represented group functor supplies the group-scheme identification
in the two DDMM charts. The global and local Picard comparisons must concern the same curve. -/
theorem goodReduction_of_picard_comparison (p : ℕ) [Fact p.Prime] (u : ℚ) (hp : 17 ≤ p)
    (A : GroupScheme ℚ) (jac : Polynomial ℚ_[p] → GroupScheme ℚ_[p])
    (ddmm : DDMMCriterion p jac)
    (P : (Over S)ᵒᵖ ⥤ GrpCat) (globalRep : P ≅ points A)
    (chart : ∀ (v a : ℤ_[p]ˣ) (t : ℤ_[p]), Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p]) →
      ∃ Q : (Over (Spec (.of ℚ_[p])))ᵒᵖ ⥤ GrpCat,
        Nonempty (Q ≅ points (jac (polynomial p u v a t))) ∧ Nonempty
          (Q ≅ (Over.map (Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ_[p])))).op ⋙ P))
    (branch : (∃ k : ℕ, 0 < k ∧ addVal ℤ_[p] (F p u) = ((2*k : ℕ) : ℕ∞)) ∨
      ∃ g : ℕ, 0 < g ∧ addVal ℤ_[p] (G p u) = (g : ℕ∞)) : GoodReductionAt p A := by
  apply goodReductionAt_of_even_contact_or_pole p u hp A jac ddmm _ branch
  intro v a t c
  obtain ⟨Q, ⟨q⟩, ⟨e⟩⟩ := chart v a t c
  exact ⟨localIso _ globalRep q e⟩
end
end ZInQBlueprint.PointedSextic
#print axioms ZInQBlueprint.PointedSextic.infinityChart
#print axioms ZInQBlueprint.PointedSextic.paperPoint
#print axioms ZInQBlueprint.PointedSextic.paper_sheafification_iso
#print axioms ZInQBlueprint.PointedSextic.goodReduction_of_picard_comparison
#print axioms ZInQBlueprint.PointedSextic.pointSheaf
#print axioms ZInQBlueprint.PointedSextic.iso_of_pointed_tests
