import ThetaSectionUniqueness
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.ZeroSchemeIdealCompEq
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleComapZeroSchemeIdeal

/-! Transport of the unique zero divisor. Both isomorphisms may change the base
field action. All linear algebra takes place on the original scheme. -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace ZInQBlueprint.ThetaLinearSystem
noncomputable section
universe u
variable {k : Type u} [Field k] {X Y : Scheme.{u}}

private def pullEquivalence (a : Y ≅ X) : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback a.hom) (Scheme.Modules.pullback a.inv)
    ((Scheme.Modules.pullbackComp a.inv a.hom ≪≫ Scheme.Modules.pullbackCongr a.inv_hom_id ≪≫
      Scheme.Modules.pullbackId X).symm)
    (Scheme.Modules.pullbackComp a.hom a.inv ≪≫ Scheme.Modules.pullbackCongr a.hom_inv_id ≪≫
      Scheme.Modules.pullbackId Y)

/-- Pullback on sections is bijective along a scheme isomorphism. -/
theorem pull_sections_bijective (a : Y ≅ X) (L : X.Modules) :
    Function.Bijective (Scheme.Modules.pullbackSection (M := L) a.hom) := by
  let F := Scheme.Modules.pullback a.hom
  let E := pullEquivalence a
  let : F.Full := E.full_functor
  let : F.Faithful := E.faithful_functor
  let U : F.obj (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules := Scheme.Modules.pullbackUnitIso a.hom
  constructor
  · intro s t h
    have h' := congrArg (fun f : 𝟙_ Y.Modules ⟶ F.obj L => U.hom ≫ f) h
    exact F.map_injective ((U.hom_inv_id_assoc (F.map s)).symm.trans
      (h'.trans (U.hom_inv_id_assoc (F.map t))))
  · intro t
    refine ⟨F.preimage (U.hom ≫ t), ?_⟩
    change U.inv ≫ F.map (F.preimage (U.hom ≫ t)) = t
    exact (congrArg (fun f => U.inv ≫ f) (F.map_preimage (U.hom ≫ t))).trans
      (U.inv_hom_id_assoc t)

private theorem pull_zero (a : Y ≅ X) (L : X.Modules) :
    Scheme.Modules.pullbackSection a.hom (0 : 𝟙_ X.Modules ⟶ L) = 0 := by
  let U : (Scheme.Modules.pullback a.hom).obj (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules :=
    Scheme.Modules.pullbackUnitIso a.hom
  change U.inv ≫ (Scheme.Modules.pullback a.hom).map (0 : 𝟙_ X.Modules ⟶ L) = 0
  exact (congrArg (fun f => U.inv ≫ f) ((Scheme.Modules.pullback a.hom).map_zero _ _)).trans
    (Limits.comp_zero (C := Y.Modules) (f := U.inv) (Z := (Scheme.Modules.pullback a.hom).obj L))

/-- The equality holds in the lattice of ideal sheaves and uses only the
dimension of the original line bundle. Neither an equality of section
supports nor a chosen compatibility of sections is an assumption. -/
theorem comap_eq_of_pullback_linearly_equivalent (c : X ⟶ Spec (.of k)) (L : X.Modules)
    (hL : Scheme.Modules.IsInvertible L) (theta : 𝟙_ X.Modules ⟶ L) (htheta : theta ≠ 0)
    (h0 : rankH0 c L = 1) (a t : Y ≅ X)
    (e : (Scheme.Modules.pullback a.hom).obj L ≅ (Scheme.Modules.pullback t.hom).obj L) :
    (Scheme.Modules.zeroSchemeIdeal theta).comap a.hom =
      (Scheme.Modules.zeroSchemeIdeal theta).comap t.hom := by
  let s := Scheme.Modules.pullbackSection a.hom theta
  have hs : s ≠ 0 := fun h => htheta ((pull_sections_bijective a L).1 (h.trans (pull_zero a L).symm))
  obtain ⟨v, hv⟩ := (pull_sections_bijective t L).2 (s ≫ e.hom)
  have hv0 : v ≠ 0 := by
    rintro rfl
    apply hs
    apply (cancel_mono e.hom).1
    simpa only [pull_zero, Limits.zero_comp] using hv.symm
  have hzero := congrArg (fun I : X.IdealSheafData => I.comap t.hom)
    (zeroScheme_eq c L hL h0 v theta hv0 htheta)
  rw [hL.comap_zeroSchemeIdeal, hv, Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso] at hzero
  exact (hL.comap_zeroSchemeIdeal a.hom theta).trans hzero

end
end ZInQBlueprint.ThetaLinearSystem
#print axioms ZInQBlueprint.ThetaLinearSystem.pull_sections_bijective
#print axioms ZInQBlueprint.ThetaLinearSystem.comap_eq_of_pullback_linearly_equivalent
