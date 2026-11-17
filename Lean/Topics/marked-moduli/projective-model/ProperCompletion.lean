import CommonOpen
import ValuationStalks
import LineValuation

/-! Comparing the complete paper models by a specified common affine chart. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.BinaryCover
noncomputable section

/-- Write scalar extension as an object of the category of schemes over K. -/
abbrev paperPullback (K : Type) [Field K] [CharZero K] (u : ℚ) :=
  (Over.pullback (scalarMap ℚ K)).obj (paperModel ℚ u)

private theorem pullback_open {S T : Scheme} (f : T ⟶ S) {A C : Over S}
    (j : A ⟶ C) [IsOpenImmersion j.left] : IsOpenImmersion ((Over.pullback f).map j).left := by
  let m : pullback A.hom f ⟶ pullback C.hom f := ((Over.pullback f).map j).left
  have H : m ≫ pullback.snd C.hom f = pullback.snd A.hom f := ((Over.pullback f).map j).w
  have sq : IsPullback (pullback.fst A.hom f) m j.left (pullback.fst C.hom f) := by
    apply IsPullback.of_bot (v₂₁ := pullback.snd C.hom f) (v₂₂ := C.hom) (h₃₁ := f)
    · rw [H,j.w]
      exact IsPullback.of_hasPullback _ _
    · exact (pullback.lift_fst ..).symm
    · exact IsPullback.of_hasPullback _ _
  exact MorphismProperty.of_isPullback (P := @IsOpenImmersion) sq inferInstance

private abbrev standardFiniteChart (K : Type) [Field K] [CharZero K] (u : ℚ) :=
  chartInclusion K _ _ (paper_overlap K u) false

/-- The finite affine chart of the reglued scheme, inside the literal scalar extension. -/
def baseChangedFiniteChart (K : Type) [Field K] [CharZero K] (u : ℚ) :
    SpecOver (R := K) (Cover (paper K u false)) ⟶ paperPullback K u :=
  (paperChartBaseChange K u false).hom ≫ (Over.pullback (scalarMap ℚ K)).map (standardFiniteChart ℚ u)

private instance (K : Type) [Field K] [CharZero K] (u : ℚ) :
    IsOpenImmersion (baseChangedFiniteChart K u).left := by
  let g := (Over.pullback (scalarMap ℚ K)).map (standardFiniteChart ℚ u)
  let e := paperChartBaseChange K u false
  let : IsIso e.hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso e).hom))
  exact @IsOpenImmersion.comp _ _ _ e.hom.left g.left (IsOpenImmersion.of_isIso _)
    (pullback_open _ (standardFiniteChart ℚ u))

private theorem proper_pullback (K : Type) [Field K] [CharZero K] (u : ℚ) : IsProper (paperPullback K u).hom := by
  let := paper_proper ℚ u
  exact inferInstanceAs (IsProper (pullback.snd (paperModel ℚ u).hom (scalarMap ℚ K)))

/-- Gluing the sextic after extending coefficients gives the unique isomorphism over K
with the literal base change that respects the finite affine chart. -/
theorem unique_reglued_baseChange (K : Type) [Field K] [CharZero K] {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) :
    ∃! e : paperModel K u ≅ paperPullback K u, standardFiniteChart K u ≫ e.hom = baseChangedFiniteChart K u := by
  let := paper_proper K u
  let := proper_pullback K u
  let := paper_reglued_integral K hu
  let : AlgebraicGeometry.IsIntegral (paperPullback K u).left := integral_baseChange K hu
  let : Nonempty (SpecOver (R := K) (Cover (paper K u false))).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Cover (paper K u false))))
  let U := SpecOver (R := K) (Cover (paper K u false))
  let X := paperModel K u
  let Y := paperPullback K u
  let i : U ⟶ X := standardFiniteChart K u
  let j : U ⟶ Y := baseChangedFiniteChart K u
  let hi : IsOpenImmersion i.left := chartInclusion_open ..
  let hj : IsOpenImmersion j.left := by exact inferInstanceAs (IsOpenImmersion (baseChangedFiniteChart K u).left)
  exact @CurveExtension.unique_model_iso _ inferInstance U X Y (paper_reglued_integral K hu)
    (proper_pullback K u) (inferInstanceAs (Nonempty (PrimeSpectrum (Cover (paper K u false)))))
    (integral_baseChange K hu) (paper_proper K u) i hi j hj (paper_prevaluation K hu) (baseChange_prevaluation K hu)

/-- A proper integral completion of the actual local DDMM equation, equipped with its
specified affine chart and valuation stalks, is uniquely isomorphic to the rational
paper curve over Q_p, respecting that specified chart. -/
theorem unique_ddmm_completion {p : ℕ} [Fact p.Prime] {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (v a : ℤ_[p]ˣ) (t : ℤ_[p]) (hc : PrimitiveParameters.Coordinates p u t (v : ℤ_[p]) (a : ℤ_[p])) :
    ∃ j : SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t)) ⟶ paperPullback ℚ_[p] u,
    IsOpenImmersion j.left ∧
    ∀ (D : Over (Spec (.of ℚ_[p]))) [IsProper D.hom] [AlgebraicGeometry.IsIntegral D.left]
      (k : SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t)) ⟶ D)
      [IsOpenImmersion k.left], (∀ z : D.left, PreValuationRing (D.left.presheaf.stalk z)) →
      ∃! e : paperPullback ℚ_[p] u ≅ D, j ≫ e.hom = k := by
  obtain ⟨j,hj⟩ := ddmm_open_baseChange hu v a t hc
  refine ⟨j,hj,?_⟩
  intro D _ _ k _ hD
  let : IsOpenImmersion j.left := hj
  let := proper_pullback ℚ_[p] u
  let : AlgebraicGeometry.IsIntegral (paperPullback ℚ_[p] u).left := integral_baseChange ℚ_[p] hu
  let : Nonempty (SpecOver (R := ℚ_[p]) (Cover (GoodReductionCharts.polynomial p u v a t))).left :=
    inferInstanceAs (Nonempty (PrimeSpectrum (Cover (GoodReductionCharts.polynomial p u v a t))))
  exact CurveExtension.unique_model_iso j k (baseChange_prevaluation ℚ_[p] hu) hD

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.unique_reglued_baseChange
#print axioms ZInQBlueprint.BinaryCover.unique_ddmm_completion
