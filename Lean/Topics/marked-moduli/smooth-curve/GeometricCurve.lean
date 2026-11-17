import GeometricCharts
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Integrality of the actual base change, tested on a two-chart open cover. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Set
namespace ZInQBlueprint.BinaryCover
noncomputable section

/-- Two integral open subschemes that meet and cover give an integral scheme. -/
theorem integral_of_two_charts {X : Scheme} (U : Bool → Scheme) (j : ∀ i, U i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (integral : ∀ i, AlgebraicGeometry.IsIntegral (U i))
    (cover : ∀ x : X, ∃ i y, j i y = x)
    (meet : (Set.range (j true) ∩ Set.range (j false)).Nonempty) :
    AlgebraicGeometry.IsIntegral X := by
  let atlas : X.OpenCover := Scheme.Cover.mkOfCovers Bool U j cover
  have red : AlgebraicGeometry.IsReduced X :=
    (AlgebraicGeometry.IsReduced.iff_of_openCover X atlas).mpr (fun i => by
      change AlgebraicGeometry.IsReduced (U i)
      let := integral i
      infer_instance)
  have ir (i : Bool) : IsIrreducible (Set.range (j i)) := by
    let := integral i
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (U i)).image (j i) (j i).continuous.continuousOn
  have sub := subset_closure_inter_of_isPreirreducible_of_isOpen (ir true).2
    (j false).isOpenEmbedding.isOpen_range meet
  have den : DenseRange (j false) := by
    intro x
    obtain ⟨i,p,rfl⟩ := cover x
    cases i with
    | false => exact subset_closure ⟨p,rfl⟩
    | true => exact closure_mono Set.inter_subset_right (sub ⟨p,rfl⟩)
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr (by
    change IsIrreducible (Set.univ : Set X)
    rw [← den.closure_range]
    exact isIrreducible_iff_closure.mpr (ir false))
  exact isIntegral_of_irreducibleSpace_of_isReduced _

private abbrev Cmodel (u : ℚ) := paperModel ℚ u
private abbrev Chart (u : ℚ) (i : Bool) := SpecOver (R := ℚ) (Cover (paper ℚ u i))

private def jchart (u : ℚ) (i : Bool) : Chart u i ⟶ Cmodel u := by
  cases i
  · exact chartInclusion ℚ _ _ (paper_overlap ℚ u) false
  · exact chartInclusion ℚ _ _ (paper_overlap ℚ u) true

private instance jchart_open (u : ℚ) (i : Bool) : IsOpenImmersion (jchart u i).left := by
  cases i <;> exact chartInclusion_open ..

private theorem overlap_image (u : ℚ) :
    (Set.range (jchart u true).left ∩ Set.range (jchart u false).left).Nonempty := by
  let D := diagram ℚ _ _ (paper_overlap ℚ u)
  let w : D.obj none := Classical.choice (inferInstanceAs (Nonempty (Spec (.of
    (Punctured ℚ (paper ℚ u false))))))
  refine ⟨colimit.ι D none w, ?_, ?_⟩
  · exact ⟨D.map (.init true) w, congrArg (fun f : D.obj none ⟶ colimit D => f w)
       (colimit.w D (.init true))⟩
  · exact ⟨D.map (.init false) w, congrArg (fun f : D.obj none ⟶ colimit D => f w)
       (colimit.w D (.init false))⟩

private theorem chart_cover (u : ℚ) (x : (Cmodel u).left) :
    ∃ i y, (jchart u i).left y = x := by
  let D := diagram ℚ _ _ (paper_overlap ℚ u)
  obtain ⟨i,y,rfl⟩ := (openCover ℚ _ _ (paper_overlap ℚ u)).exists_eq x
  change ∃ i y, (jchart u i).left y = colimit.ι D _ _
  cases i with
  | none =>
    exact ⟨false, D.map (.init false) y,
        congrArg (fun f : D.obj none ⟶ colimit D => f y) (colimit.w D (.init false))⟩
  | some i => cases i <;> exact ⟨_, y,rfl⟩

/-- The scalar extension of the original rational scheme is integral for every field extension. -/
theorem integral_baseChange (K : Type) [Field K] [CharZero K] {u : ℚ}
    (hu : u ∉ ZInQ.contactSet) :
    AlgebraicGeometry.IsIntegral (pullback (Cmodel u).hom (scalarMap ℚ K)) := by
  let C := Cmodel u
  let h := scalarMap ℚ K
  let ℓ := pullback.fst C.hom h
  let U (i : Bool) := pullback (jchart u i).left ℓ
  let j (i : Bool) : U i ⟶ _ := pullback.snd (jchart u i).left ℓ
  have rg (i : Bool) : Set.range (j i) = ℓ ⁻¹' Set.range (jchart u i).left :=
    Scheme.Pullback.range_snd _ _
  have sur : Surjective h := ⟨Function.surjective_to_subsingleton _⟩
  have sur' : Surjective ℓ := inferInstanceAs (Surjective (pullback.fst C.hom h))
  apply integral_of_two_charts U j
  · intro i
    let e : U i ≅ (SpecOver (R := K) (Cover (paper K u i))).left :=
      pullbackRightPullbackFstIso C.hom h (jchart u i).left ≪≫
      pullback.congrHom (jchart u i).w rfl ≪≫
      (Over.forget _).mapIso (paperChartBaseChange K u i).symm
    let := field_chart_domain K hu i
    let : AlgebraicGeometry.IsIntegral (SpecOver (R := K) (Cover (paper K u i))).left :=
      (affine_isIntegral_iff _).mpr (field_chart_domain K hu i)
    exact AlgebraicGeometry.IsIntegral.of_isIso e.inv
  · intro x
    obtain ⟨i,y,hy⟩ := chart_cover u (ℓ x)
    exact ⟨i,(rg i).ge ⟨y,hy⟩⟩
  · obtain ⟨p,hp,hq⟩ := overlap_image u
    obtain ⟨q,he⟩ := sur'.surj p
    refine ⟨q,(rg true).ge ?_,(rg false).ge ?_⟩
    · change ℓ q ∈ Set.range _
      rwa [he]
    · change ℓ q ∈ Set.range _
      rwa [he]

/-- Every unmarked rational paper curve is geometrically integral. -/
theorem geometricallyIntegral_paperModel {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    GeometricallyIntegral (paperModel ℚ u).hom := by
  let : ObjectProperty.IsClosedUnderIsomorphisms (C := Scheme) AlgebraicGeometry.IsIntegral :=
    ⟨fun e _ => AlgebraicGeometry.IsIntegral.of_isIso e.hom⟩
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := AlgebraicGeometry.IsIntegral) (R := ℚ) (f := (paperModel ℚ u).hom)).mpr
  intro K F A
  let : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  have e : algebraMap ℚ K = Rat.castHom K := Subsingleton.elim _ _
  rw [e]
  exact integral_baseChange K hu

end
end ZInQBlueprint.BinaryCover
#print axioms ZInQBlueprint.BinaryCover.integral_of_two_charts
#print axioms ZInQBlueprint.BinaryCover.integral_baseChange
#print axioms ZInQBlueprint.BinaryCover.geometricallyIntegral_paperModel
