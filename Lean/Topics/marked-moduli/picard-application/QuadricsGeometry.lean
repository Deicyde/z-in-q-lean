import QuadricsAffine
import DDMMCompletion
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-! A projective model for the paper sextic and for its smooth local completions. -/
open CategoryTheory AlgebraicGeometry MvPolynomial ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.SexticEmbedding
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type} [Field K] (c : Fin 7 → K)
local notation "gr" => (HomogeneousIdeal.quotientGrading (equationsIdeal c))
local notation "P" => fourQuadricsProj c

def projectiveStructure : P ⟶ Spec (.of K) :=
  Proj.toSpecZero gr ≫ Spec.map (CommRingCat.ofHom (algebraMap K (gr 0)))

instance proper_projectiveStructure : IsProper (projectiveStructure c) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap K (gr 0)))) :=
    IsClosedImmersion.spec_of_surjective _ (equationsIdeal c).surjective_algebraMap_quotientGrading_zero
  exact inferInstanceAs (IsProper (Proj.toSpecZero gr ≫ Spec.map (CommRingCat.ofHom (algebraMap K (gr 0)))))

/-- The map from a square-root chart into projective four-space's four-quadric locus. -/
def chartMap (b : Bool) : Spec (.of (SquareChart c b)) ⟶ P :=
  (projectiveChartIso c b).inv ≫ (coordinateOpen c (pivot b)).ι

instance (b : Bool) : IsOpenImmersion (chartMap c b) :=
  inferInstanceAs (IsOpenImmersion ((projectiveChartIso c b).inv ≫ (coordinateOpen c (pivot b)).ι))

private def awayChartEquiv (b : Bool) :
    HomogeneousLocalization.Away gr (coord c (pivot b)) ≃ₐ[K] SquareChart c b :=
  ((equationsIdeal c).awayEquivDehomogenize (pivot b)).trans (chartRingEquiv c b)

private theorem chartMap_formula (b : Bool) :
    chartMap c b = Spec.map (CommRingCat.ofHom (awayChartEquiv c b).toRingHom) ≫
      Proj.awayι gr _ ((equationsIdeal c).mk_X_mem_quotientGrading (pivot b)) (by decide : 0 < 1) := by
  unfold chartMap projectiveChartIso affineChartIso Proj.awayι awayChartEquiv
  simp [← Spec.map_comp,Category.assoc]

@[reassoc] theorem chartMap_over (b : Bool) :
    chartMap c b ≫ projectiveStructure c = Spec.map (CommRingCat.ofHom (algebraMap K (SquareChart c b))) := by
  rw [chartMap_formula, projectiveStructure, Category.assoc, ← Category.assoc
      (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (awayChartEquiv c b).commutes r

def chartAsOver (b : Bool) : SpecOver (R := K) (SquareChart c b) ⟶ Over.mk (projectiveStructure c) :=
  Over.homMk (chartMap c b) (chartMap_over c b)

theorem cover_projective (p : P) : ∃ b x, chartMap c b x = p := by
  have h : p ∈ coordinateOpen c 0 ⊔ coordinateOpen c 3 := by rw [two_standard_opens]; trivial
  change p ∈ coordinateOpen c 0 ∨ p ∈ coordinateOpen c 3 at h
  have member (b : Bool) (h : p ∈ coordinateOpen c (pivot b)) : ∃ x, chartMap c b x = p := by
    refine ⟨(projectiveChartIso c b).hom ⟨p,h⟩,?_⟩
    change (coordinateOpen c (pivot b)).ι ((projectiveChartIso c b).inv ((projectiveChartIso c b).hom _)) = p
    rw [Scheme.hom_inv_apply]
    rfl
  cases h with
  | inl h => exact ⟨true,member true h⟩
  | inr h => exact ⟨false,member false h⟩

/-- The point (1:1:1:1:y) is defined over an algebraic closure and lies in both opens. -/
theorem overlapping_charts : (Set.range (chartMap c true) ∩ Set.range (chartMap c false)).Nonempty := by
  let L := AlgebraicClosure K
  obtain ⟨y,hy⟩ := IsAlgClosed.exists_pow_nat_eq (sextic (algebraMap K L ∘ c) 1) (by decide : 0 < 2)
  let a : Fin 5 → L := ![1,1,1,1,y]
  have h : equations (algebraMap K L ∘ c) (a 0) (a 1) (a 2) (a 3) (a 4) :=
    (finite_chart ..).mpr ⟨by simp [a],by simp [a],by simpa [a] using hy⟩
  let e : CoordRing c →ₐ[K] L := Ideal.Quotient.liftₐ _ (aeval a) (by
    change (equationsIdeal c).toIdeal ≤ RingHom.ker (aeval a)
    apply Ideal.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact (eval_quadrics c a j).trans ((generators_vanish _ _).mpr h j))
  let Q := RingHom.ker e.toRingHom
  have hA : coord c 0 ∉ Q := by
    change (aeval a) (X 0) ≠ 0
    simp [a]
  have hD : coord c 3 ∉ Q := by
    change (aeval a) (X 3) ≠ 0
    simp [a]
  let p : P := ⟨Q.homogeneousCore gr, (RingHom.ker_isPrime e.toRingHom).homogeneousCore, by
    intro h
    exact hA (Q.toIdeal_homogeneousCore_le gr (h
      (HomogeneousIdeal.mem_irrelevant_of_mem gr (by decide : 0 < 1)
        ((equationsIdeal c).mk_X_mem_quotientGrading 0))))⟩
  have member (b : Bool) (hh : coord c (pivot b) ∉ Q) : p ∈ Set.range (chartMap c b) := by
    have hp : p ∈ coordinateOpen c (pivot b) := fun h => hh (Q.toIdeal_homogeneousCore_le gr h)
    refine ⟨(projectiveChartIso c b).hom ⟨p,hp⟩,?_⟩
    change (coordinateOpen c (pivot b)).ι ((projectiveChartIso c b).inv ((projectiveChartIso c b).hom _)) = p
    rw [Scheme.hom_inv_apply]
    rfl
  exact ⟨p,member true hA,member false hD⟩

/-- Dedekind chart rings give an integral projective curve with valuation stalks. -/
theorem projective_regular (h : ∀ b, IsDedekindDomain (SquareChart c b)) :
    AlgebraicGeometry.IsIntegral P ∧ ∀ p : P, PreValuationRing ((P).presheaf.stalk p) := by
  constructor
  · exact integral_of_two_charts (fun b => Spec (.of (SquareChart c b))) (chartMap c)
      (fun b => (affine_isIntegral_iff _).mpr (h b).toIsDomain) (cover_projective c) (overlapping_charts c)
  · intro p
    obtain ⟨b,x,rfl⟩ := cover_projective c p
    let := h b
    exact (open_stalk_prevaluation (chartMap c b) x).mpr (affine_dedekind_stalk _ x)

end
end ZInQBlueprint.SexticEmbedding
#print axioms ZInQBlueprint.SexticEmbedding.proper_projectiveStructure
#print axioms ZInQBlueprint.SexticEmbedding.chartMap_over
#print axioms ZInQBlueprint.SexticEmbedding.cover_projective
#print axioms ZInQBlueprint.SexticEmbedding.overlapping_charts
#print axioms ZInQBlueprint.SexticEmbedding.projective_regular
