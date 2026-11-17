import ChartOpen
import Mathlib.Algebra.QuadraticAlgebra.BaseChange
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! Scalar extension of both actual affine charts of the rational paper model. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open ZInQBlueprint.IntegralSextic ZInQBlueprint.ResidualFactors ZInQBlueprint.GlobalTwist
namespace ZInQBlueprint.BinaryCover
noncomputable section

abbrev scalarMap (R A : Type) [CommRing R] [CommRing A] [Algebra R A] :=
  Spec.map (CommRingCat.ofHom (algebraMap R A))

private theorem scalarMap_comp (R S A : Type) [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Algebra R A] [IsScalarTower R S A] :
    scalarMap S A ≫ scalarMap R S = scalarMap R A := by
  rw [scalarMap, scalarMap, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R S A).symm

private theorem algebraSquare (R S A B : Type) [CommRing R] [CommRing S] [CommRing A]
    [CommRing B] [Algebra R S] [Algebra S B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B] :
    IsPullback (scalarMap A B) (scalarMap S B) (scalarMap R A) (scalarMap R S) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_of_isPushout R S A B)).flip

attribute [local instance] Polynomial.algebra QuadraticAlgebra.algebra

/-- The affine double cover of a coefficientwise extended polynomial is
canonically the scheme-theoretic pullback of the affine double cover. -/
def affineBaseChange (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (f : R[X]) :
    SpecOver (R := K) (Cover (f.map (algebraMap R K))) ≅
       (Over.pullback (scalarMap R K)).obj (SpecOver (R := R) (Cover f)) := by
  let D := QuadraticAlgebra K[X] (algebraMap R[X] K[X] f) (algebraMap R[X] K[X] 0)
  have top := algebraSquare R[X] K[X] (Cover f) D
  have bot := algebraSquare R K R[X] K[X]
  have H := top.paste_vert bot
  rw [scalarMap_comp K K[X] D, scalarMap_comp R R[X] (Cover f)] at H
  let e : SpecOver (R := K) D ≅ (Over.pullback (scalarMap R K)).obj (SpecOver (R := R) (Cover f)) :=
    Over.isoMk H.isoPullback H.isoPullback_hom_snd
  have hz : (algebraMap R[X] K[X] 0) = 0 := map_zero _
  exact (eqToIso (congrArg (fun b : K[X] => SpecOver (R := K) (QuadraticAlgebra K[X]
    (algebraMap R[X] K[X] f) b)) hz)).symm ≪≫ e

/-- Specializing the *specified* rational sextic commutes with passage to
both affine coordinate systems. -/
theorem paper_baseChange (K : Type) [Field K] [CharZero K] (u : ℚ) (i : Bool) :
    (paper ℚ u i).map (algebraMap ℚ K) = paper K u i := by
  rw [paper_eq, paper_eq]
  cases i <;>
    simp [fixed, integralEquation, form, m, n, alpha, beta, gamma, poleForm]

/-- Both actual Q_p affine paper charts are the generic charts over Q pulled
back along Spec Q_p → Spec Q. -/
def paperChartBaseChange (K : Type) [Field K] [CharZero K] (u : ℚ) (i : Bool) :
    SpecOver (R := K) (Cover (paper K u i)) ≅ (Over.pullback (scalarMap ℚ K)).obj
      (SpecOver (R := ℚ) (Cover (paper ℚ u i))) :=
  (eqToIso (congrArg (fun f : K[X] => SpecOver (R := K) (Cover f)) (paper_baseChange K u i))).symm ≪≫
    affineBaseChange ℚ K (paper ℚ u i)

private theorem pullback_open {S T : Scheme} (f : T ⟶ S) {U C : Over S} (j : U ⟶ C)
    (hj : IsOpenImmersion j.left) : IsOpenImmersion ((Over.pullback f).map j).left := by
  let m : pullback U.hom f ⟶ pullback C.hom f := ((Over.pullback f).map j).left
  have h : m ≫ pullback.snd C.hom f = pullback.snd U.hom f := ((Over.pullback f).map j).w
  have sq : IsPullback (pullback.fst U.hom f) m j.left (pullback.fst C.hom f) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd C.hom f) (v₂₂ := C.hom) (h₃₁ := f)
    · rw [h, j.w]
      exact IsPullback.of_hasPullback _ _
    · symm
      exact pullback.lift_fst ..
    · exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq hj

private theorem iso_then_open {S : Scheme} {A B C : Over S} (e : A ≅ B) (j : B ⟶ C)
    (hj : IsOpenImmersion j.left) : IsOpenImmersion (e.hom ≫ j).left := by
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  exact @IsOpenImmersion.comp _ _ _ e.hom.left j.left (IsOpenImmersion.of_isIso _) hj

/-- Each local DDMM affine curve opens into the literal base change of the
fixed rational scheme. This is a map of Q_p-schemes. -/
theorem ddmm_open_baseChange {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    ∃ j : SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t)) ⟶
      (Over.pullback (scalarMap ℚ ℚ_[p])).obj (paperModel ℚ u), IsOpenImmersion j.left := by
  obtain ⟨i, ⟨e⟩⟩ := local_paper_chart_iso p hu v a t hc
  let go (i : Bool) (E : SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t)) ≅
      SpecOver (Cover (paper ℚ_[p] u i))) (c : SpecOver (R := ℚ) (Cover (paper ℚ u i)) ⟶ paperModel ℚ u)
      (h : IsOpenImmersion c.left) :=
    iso_then_open (E ≪≫ paperChartBaseChange ℚ_[p] u i) ((Over.pullback (scalarMap ℚ ℚ_[p])).map c)
      (pullback_open _ c h)
  cases i
  · exact ⟨_, go false e (chartInclusion ℚ _ _ (paper_overlap ℚ u) false) (chartInclusion_open ..)⟩
  · exact ⟨_, go true e (chartInclusion ℚ _ _ (paper_overlap ℚ u) true) (chartInclusion_open ..)⟩

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.affineBaseChange
#print axioms ZInQBlueprint.BinaryCover.paper_baseChange
#print axioms ZInQBlueprint.BinaryCover.paperChartBaseChange

#print axioms ZInQBlueprint.BinaryCover.ddmm_open_baseChange
