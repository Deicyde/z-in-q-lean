import FourQuadrics
import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.ClosedImmersion
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Dehomogenization
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme

/-! The four quadrics as a closed subscheme of projective space, with their two standard affine opens. -/
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace ZInQBlueprint.SexticEmbedding
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type} [CommRing R] (c : Fin 7 → R)
abbrev CoordRing := Variables R ⧸ (equationsIdeal c).toIdeal
/-- The homogeneous quotient scheme defined by the four equations. -/
abbrev fourQuadricsProj := Proj (equationsIdeal c).quotientGrading
def coord (j : Fin 5) : CoordRing c := Ideal.Quotient.mk (equationsIdeal c).toIdeal (X j)

/-- The quotient map with its standard grading. -/
def quotientMap : homogeneousSubmodule (Fin 5) R →+*ᵍ (equationsIdeal c).quotientGrading where
  __ := Ideal.Quotient.mk (equationsIdeal c).toIdeal
  map_mem := TauCeti.GradedAlgebra.mk_mem_quotientPiece _ _

/-- The closed scheme of four quadrics in the given projective four-space. -/
def quadricsInclusion : fourQuadricsProj c ⟶ Proj (homogeneousSubmodule (Fin 5) R) :=
  Proj.map (quotientMap c) (HomogeneousIdeal.irrelevant_le_map_of_surjective _
    (Ideal.Quotient.mk_surjective (I := (equationsIdeal c).toIdeal)))

instance closed_quadricsInclusion : IsClosedImmersion (quadricsInclusion c) :=
  Proj.isClosedImmersion_map _ _ (Ideal.Quotient.mk_surjective (I := (equationsIdeal c).toIdeal))

theorem coordinate_relations :
    equations (algebraMap R (CoordRing c) ∘ c) (coord c 0) (coord c 1) (coord c 2)
      (coord c 3) (coord c 4) := by
  apply (generators_vanish _ (coord c)).mp
  intro j
  have h := Ideal.Quotient.eq_zero_iff_mem.mpr
    (show quadrics c j ∈ (equationsIdeal c).toIdeal from Ideal.subset_span (Set.mem_range_self j))
  have e := map_generators (Ideal.Quotient.mk (equationsIdeal c).toIdeal) (C ∘ c) (X : Fin 5 → Variables R) j
  exact e.symm.trans h

/-- The standard open on which a specified homogeneous coordinate is invertible. -/
abbrev coordinateOpen (i : Fin 5) := Proj.basicOpen (equationsIdeal c).quotientGrading (coord c i)

/-- At the level of the Proj scheme, D_+(A) and D_+(D) cover the entire locus. -/
theorem two_standard_opens : coordinateOpen c 0 ⊔ coordinateOpen c 3 = ⊤ := by
  apply top_le_iff.mp
  intro p _
  change coord c 0 ∉ p.asHomogeneousIdeal.toIdeal ∨ coord c 3 ∉ p.asHomogeneousIdeal.toIdeal
  by_contra! bad
  let P := p.asHomogeneousIdeal.toIdeal
  have hA : coord c 0 ∈ P := bad.1
  have hD : coord c 3 ∈ P := bad.2
  obtain ⟨eB,_,eC,eT⟩ := coordinate_relations c
  have hB : coord c 1 ∈ P := p.isPrime.mem_of_pow_mem 2 (eB ▸ P.mul_mem_right _ hA)
  have hC : coord c 2 ∈ P := p.isPrime.mem_of_pow_mem 2 (eC ▸ P.mul_mem_left _ hD)
  have hT : coord c 4 ∈ P := by
    apply p.isPrime.mem_of_pow_mem 2
    rw [eT]
    have hD₂ : coord c 3 ^ 2 ∈ P := by rw [pow_two]; exact P.mul_mem_left _ hD
    have hA₂ : coord c 0 ^ 2 ∈ P := by rw [pow_two]; exact P.mul_mem_left _ hA
    unfold quadratic
    repeat' apply Ideal.add_mem
    all_goals first
      | exact P.mul_mem_left _ hD₂
      | exact P.mul_mem_left _ hA₂
      | exact P.mul_mem_left _ hD
      | exact P.mul_mem_left _ hC
      | exact P.mul_mem_left _ hB
  apply p.not_irrelevant_le
  apply toIdeal_le_toIdeal_iff.mpr
  apply le_trans (equationsIdeal c).irrelevant_le_span_range_mk_X
  apply Ideal.span_le.mpr
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact hA
  · exact hB
  · exact hC
  · exact hD
  · exact hT

/-- The standard opens have the expected dehomogenized coordinate rings in the scheme itself. -/
def affineChartIso (j : Fin 5) :
    (coordinateOpen c j).toScheme ≅ Spec (.of (MvPolynomial (Fin 4) R ⧸
      (equationsIdeal c).toIdeal.map (TauCeti.dehomogenize j))) :=
  Proj.basicOpenIsoSpec (equationsIdeal c).quotientGrading _ ((equationsIdeal c).mk_X_mem_quotientGrading j) (by decide : 0 < 1) ≪≫
    Scheme.Spec.mapIso ((equationsIdeal c).awayEquivDehomogenize j).toRingEquiv.toCommRingCatIso.op.symm

end
end ZInQBlueprint.SexticEmbedding
#print axioms ZInQBlueprint.SexticEmbedding.closed_quadricsInclusion
#print axioms ZInQBlueprint.SexticEmbedding.coordinate_relations
#print axioms ZInQBlueprint.SexticEmbedding.two_standard_opens
#print axioms ZInQBlueprint.SexticEmbedding.affineChartIso
