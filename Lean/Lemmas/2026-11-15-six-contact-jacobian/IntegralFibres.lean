import DDMMCompletion
import ChartBaseChange

/-! The two affine charts and their nonempty intersection after arbitrary scalar extension. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Set
open ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.IntegralCover
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type) [CommRing R] (P : Bool → R[X]) (h : SexticOverlap R (P false) (P true))

def chartMap (i : Bool) : SpecOver (R := R) (Cover (P i)) ⟶ gluedOver R _ _ h := by
  cases i
  · exact chartInclusion R _ _ h false
  · exact chartInclusion R _ _ h true

instance (i : Bool) : IsOpenImmersion (chartMap R P h i).left := by
  cases i <;> exact chartInclusion_open ..

theorem charts_cover (x : (gluedOver R _ _ h).left) : ∃ i y, (chartMap R P h i).left y = x := by
  let D := diagram R _ _ h
  obtain ⟨i,y,rfl⟩ := (openCover R _ _ h).exists_eq x
  change ∃ i y, (chartMap R P h i).left y = colimit.ι D _ _
  cases i with
  | none => exact ⟨false,D.map (.init false) y,
      congrArg (fun f : D.obj none ⟶ colimit D => f y) (colimit.w D (.init false))⟩
  | some i => cases i <;> exact ⟨_,y,rfl⟩

variable (K : Type) [Field K] [Algebra R K]
private abbrev M := gluedOver R _ _ h

/-- A common point of the *base-changed* two charts. The algebra B over K adjoins the
ordinate above x=1, so a K-rational square root is unnecessary. -/
theorem generic_meet :
    ∃ q : (pullback (M R P h).hom (scalarMap R K) : Scheme),
      (pullback.fst (M R P h).hom (scalarMap R K)) q ∈
        Set.range (chartMap R P h true).left ∩ Set.range (chartMap R P h false).left := by
  let f := P false
  let L := LaurentPolynomial R
  let a : L →+* K := LaurentPolynomial.eval₂ (algebraMap R K) 1
  let B := QuadraticAlgebra K (a (algebraMap R[X] L f)) (a (algebraMap R[X] L 0))
  let m : Punctured R f →+* B := QuadraticAlgebra.mapRingHom a _ _
  let j : Spec (.of B) ⟶ Spec (.of (Punctured R f)) := Spec.map (CommRingCat.ofHom m)
  let D := diagram R _ _ h
  let into : Spec (.of (Punctured R f)) ⟶ (M R P h).left := colimit.ι D none
  have ew : into ≫ (M R P h).hom = (SpecOver (R := R) (Punctured R f)).hom :=
    WidePushout.head_desc (arrows := arrow R (P false) (P true) h) ..
  have base : (j ≫ into) ≫ (M R P h).hom = scalarMap K B ≫ scalarMap R K := by
    rw [Category.assoc,ew]
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp,← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    apply QuadraticAlgebra.ext
    · change a (LaurentPolynomial.C r) = algebraMap R K r
      exact LaurentPolynomial.eval₂_C _ _ _
    · change a 0 = 0
      exact map_zero _
  let j' := pullback.lift (j ≫ into) (scalarMap K B) base
  let w : Spec (.of B) := Classical.choice (inferInstanceAs (Nonempty (PrimeSpectrum B)))
  refine ⟨j' w,?_⟩
  have hw : (pullback.fst (M R P h).hom (scalarMap R K)) (j' w) = into (j w) :=
    congrArg (fun g : Spec (.of B) ⟶ (M R P h).left => g w) (pullback.lift_fst ..)
  rw [hw]
  exact ⟨⟨D.map (.init true) (j w), congrArg (fun g : D.obj none ⟶ colimit D => g (j w))
    (colimit.w D (.init true))⟩,⟨D.map (.init false) (j w),
    congrArg (fun g : D.obj none ⟶ colimit D => g (j w)) (colimit.w D (.init false))⟩⟩

/-- Evaluate each scalar extension chart before making its affine square-root cover. -/
def chartIso (i : Bool) :
    pullback (chartMap R P h i).left (pullback.fst (M R P h).hom (scalarMap R K)) ≅
      (SpecOver (R := K) (Cover ((P i).map (algebraMap R K)))).left :=
  pullbackRightPullbackFstIso (M R P h).hom (scalarMap R K) (chartMap R P h i).left ≪≫
    pullback.congrHom (chartMap R P h i).w rfl ≪≫
    (Over.forget _).mapIso (affineBaseChange R K (P i)).symm

theorem fibre_integral (H : ∀ i, IsDomain (Cover ((P i).map (algebraMap R K)))) :
    AlgebraicGeometry.IsIntegral (pullback (M R P h).hom (scalarMap R K)) := by
  let ℓ := pullback.fst (M R P h).hom (scalarMap R K)
  let U (i : Bool) := pullback (chartMap R P h i).left ℓ
  let j (i : Bool) : U i ⟶ _ := pullback.snd (chartMap R P h i).left ℓ
  have rg (i : Bool) : Set.range (j i) = ℓ ⁻¹' Set.range (chartMap R P h i).left :=
    Scheme.Pullback.range_snd _ _
  apply integral_of_two_charts U j
  · intro i
    let : AlgebraicGeometry.IsIntegral (SpecOver (R := K) (Cover ((P i).map (algebraMap R K)))).left :=
      (affine_isIntegral_iff _).mpr (H i)
    exact AlgebraicGeometry.IsIntegral.of_isIso (chartIso R P h K i).inv
  · intro x
    obtain ⟨i,y,hy⟩ := charts_cover R P h (ℓ x)
    exact ⟨i,(rg i).ge ⟨y,hy⟩⟩
  · obtain ⟨q,hq,hq'⟩ := generic_meet R P h K
    exact ⟨q,(rg true).ge hq,(rg false).ge hq'⟩

theorem fibre_prevaluation (H : ∀ i, IsDedekindDomain (Cover ((P i).map (algebraMap R K))))
    (x : (pullback (M R P h).hom (scalarMap R K) : Scheme)) :
    PreValuationRing ((pullback (M R P h).hom (scalarMap R K)).presheaf.stalk x) := by
  let ℓ := pullback.fst (M R P h).hom (scalarMap R K)
  let U (i : Bool) := pullback (chartMap R P h i).left ℓ
  let j (i : Bool) : U i ⟶ _ := pullback.snd (chartMap R P h i).left ℓ
  obtain ⟨i,y,hy⟩ := charts_cover R P h (ℓ x)
  have rg : Set.range (j i) = ℓ ⁻¹' Set.range (chartMap R P h i).left := Scheme.Pullback.range_snd _ _
  obtain ⟨v,hv⟩ := rg.ge ⟨y,hy⟩
  rw [← hv]
  let e := chartIso R P h K i
  let := H i
  let hj : IsOpenImmersion (j i) := MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ ℓ inferInstance
  exact (open_stalk_prevaluation (j i) v).mpr ((open_stalk_prevaluation e.hom v).mp
    (affine_dedekind_stalk _ (e.hom v)))

end
end ZInQBlueprint.IntegralCover
#print axioms ZInQBlueprint.IntegralCover.generic_meet
#print axioms ZInQBlueprint.IntegralCover.fibre_integral
#print axioms ZInQBlueprint.IntegralCover.fibre_prevaluation
