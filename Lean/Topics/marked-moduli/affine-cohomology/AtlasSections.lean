import TerminalCohomology

/-! The three affine schemes in the sextic gluing form its two-open Mayer–Vietoris square. -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Polynomial
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{0}} {A B : CommRingCat.{0}}

/-- Coordinates on the image of an affine open immersion, as an isomorphism of rings. -/
def affineSections (j : Spec A ⟶ X) [IsOpenImmersion j] : Γ(X,j.opensRange) ≅ A :=
  (IsOpenImmersion.ΓIsoTop j).symm ≪≫ Scheme.ΓSpecIso A

private theorem affineSections_hom (j : Spec A ⟶ X) [IsOpenImmersion j] :
    (affineSections j).hom = j.appLE j.opensRange ⊤ (by rw [j.preimage_opensRange]) ≫
       (Scheme.ΓSpecIso A).hom := by
  simp only [affineSections, IsOpenImmersion.ΓIsoTop, Iso.trans_hom, Iso.symm_hom,
    Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Scheme.Hom.appIso_hom',
    Category.assoc, Scheme.Hom.map_appLE_assoc]

/-- On nested affine opens these coordinates identify the restriction with the specified ring map. -/
theorem affineSections_natural (a : A ⟶ B) (j : Spec A ⟶ X) (l : Spec B ⟶ X)
    [IsOpenImmersion j] [IsOpenImmersion l] (w : Spec.map a ≫ j = l)
    (incl : l.opensRange ≤ j.opensRange) :
    X.presheaf.map (homOfLE incl).op ≫ (affineSections l).hom = (affineSections j).hom ≫ a := by
  rw [affineSections_hom, affineSections_hom, Scheme.Hom.map_appLE_assoc, Category.assoc,
    ← Scheme.ΓSpecIso_naturality, ← Category.assoc]
  have ht : (Spec.map a).appTop = (Spec.map a).appLE ⊤ ⊤ (by simp) := (Spec.map a).app_eq_appLE
  rw [ht, Scheme.Hom.appLE_comp_appLE]
  subst l
  rfl

variable (k : Type) [Field k] (f g : k[X]) (h : SexticOverlap k f g)

abbrev atlasMap (i : WidePushoutShape Bool) : (diagram k f g h).obj i ⟶ glued k f g h :=
  colimit.ι (diagram k f g h) i

abbrev atlasOpen (i : WidePushoutShape Bool) : (glued k f g h).Opens := (atlasMap k f g h i).opensRange

private theorem overlap_le (i : Bool) : atlasOpen k f g h none ≤ atlasOpen k f g h (some i) := by
  rintro _ ⟨z,rfl⟩
  exact ⟨arrow k f g h i z, congrArg (fun (m : Spec (.of (Punctured k f)) ⟶ glued k f g h) => m z)
    (WidePushout.arrow_ι (arrow k f g h) i)⟩

/-- The two affine opens cover the entire glued scheme. -/
theorem atlas_union : atlasOpen k f g h (some false) ⊔ atlasOpen k f g h (some true) = ⊤ := by
  apply top_unique
  intro x _
  let 𝒰 := openCover k f g h
  have hx : ∃ j : WidePushoutShape Bool, x ∈ atlasOpen k f g h j := ⟨𝒰.idx x, 𝒰.covers x⟩
  obtain ⟨j,hj⟩ := hx
  cases j with
  | none => exact Or.inl (overlap_le k f g h false hj)
  | some i => cases i <;> first | exact Or.inl hj | exact Or.inr hj

/-- The common open is exactly the image of the Laurent chart. -/
theorem atlas_intersection : atlasOpen k f g h none =
    atlasOpen k f g h (some false) ⊓ atlasOpen k f g h (some true) := by
  apply le_antisymm (le_inf (overlap_le k f g h false) (overlap_le k f g h true))
  rintro x ⟨⟨p,hp⟩,⟨q,hq⟩⟩
  obtain ⟨t,a,b,z,ha,hb⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (diagram k f g h)
    (i := some false) (j := some true)).mp (hp.trans hq.symm)
  cases t with
  | none =>
    have ae : a = WidePushoutShape.Hom.init false := Subsingleton.elim _ _
    subst a
    refine ⟨z,?_⟩
    have ee := congrArg (fun (m : Spec (.of (Punctured k f)) ⟶ glued k f g h) => m z)
      (WidePushout.arrow_ι (arrow k f g h) false)
    exact ee.symm.trans ((congrArg (fun w => atlasMap k f g h (some false) w) ha).trans hp)
  | some t =>
    have src {i j : Bool} (w : WidePushoutShape.Hom (some i) (some j)) : i = j := by cases w; rfl
    cases (src a).symm.trans (src b)

/-- Use the actual three affine ranges and take the top open as the union. -/
def atlasSquare : (Opens.grothendieckTopology (glued k f g h)).MayerVietorisSquare :=
  Opens.mayerVietorisSquare'
    { X₁ := atlasOpen k f g h none, X₂ := atlasOpen k f g h (some false),
      X₃ := atlasOpen k f g h (some true), X₄ := ⊤,
      f₁₂ := homOfLE (overlap_le k f g h false), f₁₃ := homOfLE (overlap_le k f g h true),
      f₂₄ := homOfLE le_top, f₃₄ := homOfLE le_top, fac := Subsingleton.elim _ _ }
    (atlas_union k f g h).symm (atlas_intersection k f g h)

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.affineSections_natural
#print axioms ZInQBlueprint.BinaryCover.Cech.atlas_union
#print axioms ZInQBlueprint.BinaryCover.Cech.atlas_intersection
#print axioms ZInQBlueprint.BinaryCover.Cech.atlasSquare
