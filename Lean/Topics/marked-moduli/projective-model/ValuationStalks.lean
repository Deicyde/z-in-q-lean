import SexticAtlas

/-! Valuation stalks on the rational paper model and its literal scalar extensions. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Set
namespace ZInQBlueprint.BinaryCover
open DirectCharts
noncomputable section

/-- An affine change of the polynomial coordinate preserves positive degree and separability. -/
theorem regular_image {F : Type} [Field F] [PerfectField F] (e : F[X] ≃ₐ[F] F[X])
    {f : F[X]} (hd : 0 < f.natDegree) (hs : f.Separable) :
    0 < (e f).natDegree ∧ (e f).Separable := by
  constructor
  · by_contra! h
    have hc := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero h)
    have nz : (e f).coeff 0 ≠ 0 := by
      intro h0
      rw [h0,map_zero] at hc
      have := e.injective (hc.trans e.map_zero.symm)
      simp [this] at hd
    exact not_isUnit_of_natDegree_pos f hd
      ((isUnit_map_iff e f).mp (hc ▸ (isUnit_C.mpr nz.isUnit)))
  · apply PerfectField.separable_iff_squarefree.mpr
    intro x hx
    have H := map_dvd e.symm hx
    have h' : e.symm x * e.symm x ∣ f := by simpa only [map_mul, AlgEquiv.symm_apply_apply] using H
    exact (isUnit_map_iff e.symm x).mp (hs.squarefree _ h')

/-- Both paper charts are nonconstant and separable after any characteristic-zero scalar extension. -/
theorem paper_chart_regular (K : Type) [Field K] [CharZero K] {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (i : Bool) : 0 < (paper K u i).natDegree ∧ (paper K u i).Separable := by
  obtain ⟨s,t,e,hs,ht,he⟩ := chart_normal_form hu i
  have h6 : (C s * monicSextic t).natDegree = 6 := (natDegree_C_mul hs).trans (monic_six t).2
  obtain ⟨hd,hsep⟩ := regular_image e (by omega : 0 < (C s * monicSextic t).natDegree)
    (separable_normal_form hs ht)
  rw [he] at hd hsep
  rw [← paper_baseChange]
  constructor
  · rwa [natDegree_map_eq_of_injective (algebraMap ℚ K).injective]
  · exact hsep.map

/-- Both sextic coordinate rings are Dedekind over every field extension of Q. -/
theorem paper_chart_dedekind (K : Type) [Field K] [CharZero K] {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (i : Bool) : IsDedekindDomain (Cover (paper K u i)) := by
  let : Invertible (2:K) := invertibleOfNonzero (by norm_num)
  exact dedekind_cover (paper_chart_regular K hu i).1 (paper_chart_regular K hu i).2

private abbrev Cmodel (K : Type) [Field K] [CharZero K] (u : ℚ) := paperModel K u
private abbrev inclusion (K : Type) [Field K] [CharZero K] (u : ℚ) :=
  atlasInclusion K (paper K u) (paper_overlap K u)

private instance (K : Type) [Field K] [CharZero K] (u : ℚ) (i : Bool) : IsOpenImmersion (inclusion K u i).left :=
  inferInstanceAs (IsOpenImmersion (atlasInclusion K (paper K u) (paper_overlap K u) i).left)

variable (K : Type) [Field K] [CharZero K]

/-- The model obtained by gluing over K is integral. -/
theorem paper_reglued_integral {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    AlgebraicGeometry.IsIntegral (paperModel K u).left :=
  integral_glued_of_domains K (paper K u) _ (field_chart_domain K hu)

/-- Every stalk of the two-chart model over K has linearly ordered divisibility. -/
theorem paper_prevaluation {u : ℚ} (hu : u ∉ ZInQ.contactSet) (x : (Cmodel K u).left) :
    PreValuationRing ((Cmodel K u).left.presheaf.stalk x) :=
  prevaluation_glued_of_dedekind K (paper K u) _ (paper_chart_dedekind K hu) x

/-- Valuation stalks on the scheme-theoretic pullback, for arbitrary characteristic-zero fields. -/
theorem baseChange_prevaluation {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) (x : (pullback (Cmodel ℚ u).hom (scalarMap ℚ K) : Scheme)) :
    PreValuationRing ((pullback (Cmodel ℚ u).hom (scalarMap ℚ K)).presheaf.stalk x) := by
  let C := Cmodel ℚ u
  let h := scalarMap ℚ K
  let ℓ := pullback.fst C.hom h
  let U (i : Bool) := pullback (inclusion ℚ u i).left ℓ
  let j (i : Bool) : U i ⟶ _ := pullback.snd (inclusion ℚ u i).left ℓ
  obtain ⟨i,y,hy⟩ := atlas_cover ℚ (paper ℚ u) (paper_overlap ℚ u) (ℓ x)
  have rg : Set.range (j i) = ℓ ⁻¹' Set.range (inclusion ℚ u i).left := Scheme.Pullback.range_snd _ _
  obtain ⟨v,hv⟩ := rg.ge ⟨y,hy⟩
  rw [← hv]
  let e : U i ≅ (SpecOver (R := K) (Cover (paper K u i))).left :=
    pullbackRightPullbackFstIso C.hom h (inclusion ℚ u i).left ≪≫
    pullback.congrHom (inclusion ℚ u i).w rfl ≪≫ (Over.forget _).mapIso (paperChartBaseChange K u i).symm
  let := paper_chart_dedekind K hu i
  let hj : IsOpenImmersion (j i) := MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ ℓ
    (inferInstanceAs (IsOpenImmersion (atlasInclusion ℚ (paper ℚ u) (paper_overlap ℚ u) i).left))
  exact (open_stalk_prevaluation (j i) v).mpr ((open_stalk_prevaluation e.hom v).mp (affine_dedekind_stalk _ (e.hom v)))

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.regular_image
#print axioms ZInQBlueprint.BinaryCover.paper_chart_regular
#print axioms ZInQBlueprint.BinaryCover.paper_chart_dedekind
#print axioms ZInQBlueprint.BinaryCover.paper_reglued_integral
#print axioms ZInQBlueprint.BinaryCover.paper_prevaluation
#print axioms ZInQBlueprint.BinaryCover.baseChange_prevaluation
