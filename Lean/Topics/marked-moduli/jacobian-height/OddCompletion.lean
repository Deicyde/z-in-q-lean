import OddEquation
import DDMMCompletion

/-! Identification of Eilers' monic odd model with the complex fibre of the rational curve. -/
open CategoryTheory AlgebraicGeometry Polynomial
namespace ZInQBlueprint.OddModel
open BinaryCover ThetaPeriod SexticThetaHeight
noncomputable section

/-- The integral paper model, translated on the base and rescaled in the ordinate. -/
theorem paper_translation {u : ℚ} (hu : u ∉ ZInQ.contactSet) {r : Fin 6 → ℂ}
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u 1) = 0) :
    ∃ s : ℂˣ, s.val ^ 2 = ordinateFactor ((paper ℚ u false).leadingCoeff : ℂ) r ∧
      algEquivAevalXAddC (r (Fin.last 5)) (paper ℂ u false) = C (s.val ^ 2) * infinityChart r := by
  have hd := paper_degree hu
  have ha : ((paper ℚ u false).leadingCoeff : ℂ) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr (fun h => by simp [h] at hd)
  have hf := ordinateFactor_ne ha hr
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (ordinateFactor ((paper ℚ u false).leadingCoeff : ℂ) r) (by decide : 0 < 2)
  have hn : v ≠ 0 := fun h => hf (hv ▸ (by simp [h]))
  exact ⟨Units.mk0 v hn, hv, by
    rw [← paper_baseChange, translated_factor hd hr (roots_of_untwisted hu hz)]
    change _ = C (v^2) * _
    rw [hv]⟩

theorem infinity_degree {r : Fin 6 → ℂ} (hr : Function.Injective r) : (infinityChart r).natDegree = 6 := by
  let a (i : Fin 5) : ℂ := -finiteBranches r i
  have hn (i : Fin 5) : a i ≠ 0 := neg_ne_zero.mpr (finiteBranch_ne hr i)
  have factor (i : Fin 5) : (1 - C (finiteBranches r i) * X : ℂ[X]) =
      C (a i) * (X - C ((finiteBranches r i)⁻¹)) := by
    rw [mul_sub, ← C_mul]
    simp [a, finiteBranch_ne hr i]; ring
  unfold infinityChart
  simp_rw [factor]
  rw [Finset.prod_mul_distrib, ← map_prod, mul_left_comm,
    natDegree_C_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => hn i)),
    natDegree_X_mul (Finset.prod_ne_zero_iff.mpr (fun i _ => X_sub_C_ne_zero _)),
    natDegree_prod_of_monic _ _ (fun i _ => monic_X_sub_C _)]
  simp

/-- This proper model has quintic radicand on its reciprocal affine chart. -/
abbrev oddCurve {r : Fin 6 → ℂ} (hr : Function.Injective r) :=
  sexticCompletion (infinityChart r) (infinity_degree hr)

/-- The coordinate change on the chart t = x − r₅, y = s W. -/
def infinityChartIso {r : Fin 6 → ℂ} {f : ℂ[X]} (s : ℂˣ)
    (he : algEquivAevalXAddC (r (Fin.last 5)) f = C (s.val^2) * infinityChart r) :
    SpecOver (R := ℂ) (Cover (infinityChart r)) ≅ SpecOver (Cover f) :=
  specIso (squareEquiv (algEquivAevalXAddC (r (Fin.last 5))) (Units.map C.toMonoidHom s) (by simpa using he))

/-- The common open includes the original point (r₅,0). In its odd-model chart
this is the point at infinity. The second chart has exactly the prescribed five finite branch values. -/
theorem paper_odd_completion {u : ℚ} (hu : u ∉ ZInQ.contactSet) {r : Fin 6 → ℂ}
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u 1) = 0) :
    ∃ (s : ℂˣ) (he : algEquivAevalXAddC (r (Fin.last 5)) (paper ℂ u false) = C (s.val^2) * infinityChart r),
      s.val^2 = ordinateFactor ((paper ℚ u false).leadingCoeff : ℂ) r ∧
      ∃! e : oddCurve hr ≅ paperPullback ℂ u,
        chartInclusion ℂ _ _ (reverse_sextic_overlap (infinity_degree hr)) false ≫ e.hom =
          (infinityChartIso s he).hom ≫ baseChangedFiniteChart ℂ u := by
  obtain ⟨s,hs,he⟩ := paper_translation hu hr hz
  refine ⟨s,he,hs,?_⟩
  let e := algEquivAevalXAddC (r (Fin.last 5))
  have reg := paper_chart_regular ℂ hu false
  have hsep := (regular_image e reg.1 reg.2).2
  change (algEquivAevalXAddC (r (Fin.last 5)) (paper ℂ u false)).Separable at hsep
  rw [he] at hsep
  have hs' : (infinityChart r).Separable :=
    (associated_unit_mul_left (infinityChart r) (C (s.val^2)) (isUnit_C.mpr (pow_ne_zero 2 s.ne_zero).isUnit)).separable hsep
  have ⟨hI,hP,_,_,hV⟩ := sexticCompletion_geometry (infinity_degree hr) hs'
  let : AlgebraicGeometry.IsIntegral (oddCurve hr).left := hI
  let : IsProper (oddCurve hr).hom := hP
  let : IsProper (paperModel ℚ u).hom := paper_proper ℚ u
  let : IsProper (paperPullback ℂ u).hom := inferInstanceAs (IsProper (Limits.pullback.snd (paperModel ℚ u).hom (scalarMap ℚ ℂ)))
  let : AlgebraicGeometry.IsIntegral (paperPullback ℂ u).left := integral_baseChange ℂ hu
  let U := SpecOver (R := ℂ) (Cover (infinityChart r))
  let : Nonempty U.left := inferInstanceAs (Nonempty (PrimeSpectrum (Cover (infinityChart r))))
  let i : U ⟶ oddCurve hr := chartInclusion ℂ _ _ (reverse_sextic_overlap (infinity_degree hr)) false
  let j := (infinityChartIso s he).hom ≫ baseChangedFiniteChart ℂ u
  let : IsOpenImmersion i.left := chartInclusion_open ..
  let : IsIso (infinityChartIso s he).hom.left := inferInstanceAs (IsIso (((Over.forget _).mapIso (infinityChartIso s he)).hom))
  let : IsOpenImmersion j.left := @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso _) (inferInstanceAs (IsOpenImmersion (baseChangedFiniteChart ℂ u).left))
  exact CurveExtension.unique_model_iso (U := U) i j hV (baseChange_prevaluation ℂ hu)

end
end ZInQBlueprint.OddModel
#print axioms ZInQBlueprint.OddModel.paper_translation
#print axioms ZInQBlueprint.OddModel.infinity_degree
#print axioms ZInQBlueprint.OddModel.infinityChartIso
#print axioms ZInQBlueprint.OddModel.paper_odd_completion
