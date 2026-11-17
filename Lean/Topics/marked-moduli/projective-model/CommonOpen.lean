import CurveExtension

/-! Uniqueness of a proper model from a common nonempty open subscheme. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.CurveExtension
open AlgebraicGeometry.Scheme
noncomputable section
variable {S : Scheme} [Scheme.IsSeparated S] {U X Y : CategoryTheory.Over S}
variable [AlgebraicGeometry.IsIntegral X.left] [IsProper Y.hom] [Nonempty U.left]

private abbrev genericInclusion (V : Scheme) [IrreducibleSpace V] :=
  V.fromSpecStalk (genericPoint V)

/-- A morphism on a nonempty open extends uniquely over an integral valuative-stalk source
when its target is proper over the separated base. -/
theorem extend_open (i : U ⟶ X) [IsOpenImmersion i.left] (k : U ⟶ Y)
    (hX : ∀ x : X.left, PreValuationRing (X.left.presheaf.stalk x)) :
    ∃! g : X ⟶ Y, i ≫ g = k := by
  let : AlgebraicGeometry.IsIntegral U.left := isIntegral_of_isOpenImmersion i.left
  let γ := genericInclusion X.left
  let η := IsLocalRing.closedPoint X.left.functionField
  have hη : γ η = genericPoint X.left := X.left.fromSpecStalk_closedPoint
  have hι : i.left (genericPoint U.left) = genericPoint X.left := genericPoint_eq_of_isOpenImmersion i.left
  have hr : Set.range γ ⊆ Set.range i.left := by
    rintro _ ⟨x,rfl⟩
    have h : x = η := @Subsingleton.elim (PrimeSpectrum X.left.functionField) inferInstance _ _
    exact ⟨genericPoint U.left,hι.trans ((congrArg γ h).trans hη).symm⟩
  let ξ := IsOpenImmersion.lift i.left γ hr
  have hξ : ξ ≫ i.left = γ := IsOpenImmersion.lift_fac _ _ _
  have hξ' : ξ η = genericPoint U.left :=
    i.left.isOpenEmbedding.injective (((congrArg (fun f : Spec X.left.functionField ⟶ X.left => f η) hξ).trans hη).trans hι.symm)
  let : IsDominant ξ := by
    constructor
    have h : genericPoint U.left ∈ Set.range ξ := ⟨η,hξ'⟩
    intro x
    exact closure_mono (Set.singleton_subset_iff.mpr h) (genericPoint_specializes x).mem_closure
  have hb : (ξ ≫ k.left) ≫ Y.hom = γ ≫ X.hom := by
    rw [Category.assoc,k.w,← i.w,← Category.assoc,hξ]
  obtain ⟨g,⟨hg,hw⟩,_⟩ := extend_generic X.hom Y.hom (fun x => by
    let := hX x
    exact ValuationRing.mk) (ξ ≫ k.left) hb
  have hi : i.left ≫ g = k.left := by
    apply ext_of_isDominant_of_isSeparated Y.hom (by rw [Category.assoc,hw,i.w,k.w]) ξ
    rw [← Category.assoc,hξ]
    exact hg
  refine ⟨Over.homMk g hw,Over.OverMorphism.ext hi,fun t ht => ?_⟩
  apply Over.OverMorphism.ext
  let : IsDominant i.left := ⟨i.left.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  apply ext_of_isDominant_of_isSeparated Y.hom (t.w.trans hw.symm) i.left
  exact (congrArg (fun l : U ⟶ Y => l.left) ht).trans hi.symm

/-- Two integral proper models with valuation stalks are uniquely isomorphic over their
base once the identifications of the common nonempty open have been specified. -/
theorem unique_model_iso [AlgebraicGeometry.IsIntegral Y.left] [IsProper X.hom]
    (i : U ⟶ X) [IsOpenImmersion i.left] (j : U ⟶ Y) [IsOpenImmersion j.left]
    (hX : ∀ x : X.left, PreValuationRing (X.left.presheaf.stalk x))
    (hY : ∀ y : Y.left, PreValuationRing (Y.left.presheaf.stalk y)) :
    ∃! e : X ≅ Y, i ≫ e.hom = j := by
  obtain ⟨f,hf,uf⟩ := extend_open i j hX
  obtain ⟨g,hg,_⟩ := extend_open j i hY
  have ident {V : CategoryTheory.Over S} [AlgebraicGeometry.IsIntegral V.left] [IsProper V.hom]
      (k : U ⟶ V) [IsOpenImmersion k.left] (hV : ∀ v : V.left, PreValuationRing (V.left.presheaf.stalk v))
      (a : V ⟶ V) (ha : k ≫ a = k) : a = 𝟙 V := by
    obtain ⟨b,_,hb⟩ := extend_open k k hV
    exact (hb _ ha).trans (hb _ (Category.comp_id _)).symm
  have hfg : f ≫ g = 𝟙 X := ident i hX _ (by rw [← Category.assoc,hf,hg])
  have hgf : g ≫ f = 𝟙 Y := ident j hY _ (by rw [← Category.assoc,hg,hf])
  exact ⟨⟨f,g,hfg,hgf⟩,hf,fun e he => Iso.ext (uf _ he)⟩

end
end ZInQBlueprint.CurveExtension
#print axioms ZInQBlueprint.CurveExtension.extend_open
#print axioms ZInQBlueprint.CurveExtension.unique_model_iso
