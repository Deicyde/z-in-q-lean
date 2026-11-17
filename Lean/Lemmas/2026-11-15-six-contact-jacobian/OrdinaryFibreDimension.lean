import IntegralFibres
import CurveDimension
import OrdinaryGeometry

/-! Every field fibre of a double cover of the projective line has dimension one. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial Set
open ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.IntegralCover
noncomputable section

theorem fibre_dimension (R : Type) [CommRing R] (P : Bool → R[X])
    (h : SexticOverlap R (P false) (P true)) (K : Type) [Field K] [Algebra R K] :
    topologicalKrullDim (pullback (gluedOver R _ _ h).hom (scalarMap R K) : Scheme) = 1 := by
  let M := gluedOver R _ _ h
  let ℓ := pullback.fst M.hom (scalarMap R K)
  let U (i : Bool) := pullback (chartMap R P h i).left ℓ
  let j (i : Bool) : U i ⟶ _ := pullback.snd (chartMap R P h i).left ℓ
  have di (i : Bool) : topologicalKrullDim (U i) = 1 := by
    let e := chartIso R P h K i
    exact (IsHomeomorph.topologicalKrullDim_eq _ (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso e)).isHomeomorph).trans
      (dimension_cover K ((P i).map (algebraMap R K)))
  have cover (x : (pullback M.hom (scalarMap R K) : Scheme)) : ∃ i y, j i y = x := by
    obtain ⟨i,y,hy⟩ := charts_cover R P h (ℓ x)
    have rg : Set.range (j i) = ℓ ⁻¹' Set.range (chartMap R P h i).left := Scheme.Pullback.range_snd _ _
    exact ⟨i,rg.ge ⟨y,hy⟩⟩
  let (i : Bool) : IsOpenImmersion (j i) := MorphismProperty.pullback_snd (P := @IsOpenImmersion) _ ℓ inferInstance
  let atlas : (pullback M.hom (scalarMap R K)).OpenCover := Scheme.Cover.mkOfCovers Bool U j cover
  exact le_antisymm (dimension_le_of_cover atlas fun i => (di i).le)
    ((di false).ge.trans (j false).isOpenEmbedding.isInducing.topologicalKrullDim_le)

end
end ZInQBlueprint.IntegralCover
#print axioms ZInQBlueprint.IntegralCover.fibre_dimension
