import JacobianTranslation
import ThetaIntegralFibre

/-! Reconstruction of a reduced effective Cartier divisor and its line bundle
from its geometric points. The two comparison maps may be semilinear. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent SixThetaRestriction CanonicalTheta
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Over an algebraically closed field the closed points determine a closed
subset of a locally finite-type scheme. The point maps used to test it are
over the field even when the two endomorphisms being tested are semilinear. -/
theorem support_eq_of_points {k : Type} [Field k] [IsAlgClosed k] {X : Scheme}
    (c : X ⟶ Spec (.of k)) [LocallyOfFiniteType c] (I J : X.IdealSheafData)
    (h : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk c,
      p.left (IsLocalRing.closedPoint k) ∈ I.support ↔ p.left (IsLocalRing.closedPoint k) ∈ J.support) :
    I.support = J.support := by
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace c
  apply SetLike.coe_injective
  rw [←closure_inter_closedPoints I.support.isClosed,←closure_inter_closedPoints J.support.isClosed]
  congr 1
  ext x
  by_cases hc : x ∈ closedPoints X
  · let p : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk c :=
      Over.homMk (pointOfClosedPoint c x hc) (pointOfClosedPoint_comp c x hc)
    have pe : p.left (IsLocalRing.closedPoint k) = x := pointOfClosedPoint_apply _ _ _ _
    have he := h p
    rw [pe] at he
    exact and_congr_left (fun _ => he)
  · exact iff_of_false (fun h => hc h.2) (fun h => hc h.2)

private theorem radical_comap_iso {X Y : Scheme} (I : X.IdealSheafData) [IsReduced I.subscheme]
    (e : Y ≅ X) : (I.comap e.hom).radical = I.comap e.hom := by
  let w : (I.comap e.hom).subscheme ≅ I.subscheme :=
    I.comapIso e.hom ≪≫ asIso (pullback.snd e.hom I.subschemeι)
  let := isReduced_of_isOpenImmersion w.hom
  exact ideal_eq_of_reduced_zero_scheme _

/-- Pullbacks of a reduced divisor along two scheme isomorphisms are equal
whenever their sections vanish at the same geometric points. -/
theorem comap_eq_of_reduced_points {k : Type} [Field k] [IsAlgClosed k] {X Y : Scheme}
    (c : Y ⟶ Spec (.of k)) [LocallyOfFiniteType c] {L : X.Modules}
    (hL : L.IsInvertible) (s : 𝟙_ X.Modules ⟶ L) [IsReduced (Scheme.Modules.zeroSchemeIdeal s).subscheme]
    (a b : Y ≅ X) (h : ∀ p : Over.mk (𝟙 (Spec (.of k))) ⟶ Over.mk c,
      Scheme.Modules.pullbackSection (p.left ≫ a.hom) s = 0 ↔
      Scheme.Modules.pullbackSection (p.left ≫ b.hom) s = 0) :
    (Scheme.Modules.zeroSchemeIdeal s).comap a.hom = (Scheme.Modules.zeroSchemeIdeal s).comap b.hom := by
  let I := Scheme.Modules.zeroSchemeIdeal s
  have eq := support_eq_of_points c (I.comap a.hom) (I.comap b.hom) (by
    intro p
    rw [Scheme.IdealSheafData.support_comap,Scheme.IdealSheafData.support_comap]
    exact (ThetaLinearSystem.field_vanishes_iff_mem _ hL s).symm.trans
      ((h p).trans (ThetaLinearSystem.field_vanishes_iff_mem _ hL s)))
  calc
    _ = (I.comap a.hom).radical := (radical_comap_iso I a).symm
    _ = Scheme.IdealSheafData.vanishingIdeal (I.comap a.hom).support :=
      Scheme.IdealSheafData.vanishingIdeal_support.symm
    _ = Scheme.IdealSheafData.vanishingIdeal (I.comap b.hom).support := congrArg _ eq
    _ = (I.comap b.hom).radical := Scheme.IdealSheafData.vanishingIdeal_support
    _ = _ := radical_comap_iso I b

/-- An invertible zero ideal identifies the line of a section with its Cartier
line bundle. Its two pullbacks are isomorphic if their Cartier ideals are equal. -/
theorem pullback_line_of_ideal {X Y : Scheme} {L : X.Modules} (hL : L.IsInvertible)
    (s : 𝟙_ X.Modules ⟶ L) (cartier : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible)
    (a b : Y ≅ X) (h : (Scheme.Modules.zeroSchemeIdeal s).comap a.hom =
      (Scheme.Modules.zeroSchemeIdeal s).comap b.hom) :
    Nonempty ((Scheme.Modules.pullback a.hom).obj L ≅ (Scheme.Modules.pullback b.hom).obj L) := by
  let I := Scheme.Modules.zeroSchemeIdeal s
  obtain ⟨d,-⟩ := hL.exists_iso_invModule_zeroSchemeIdeal s cartier
  have v (f : Y ≅ X) : (I.comap f.hom).IsInvertible := by
    exact AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal.ZDHeadG.isInvertible_comap_of_isIso cartier f.hom
  obtain ⟨ea⟩ := cartier.nonempty_pullback_invModule_iso a.hom (v a)
  obtain ⟨eb⟩ := cartier.nonempty_pullback_invModule_iso b.hom (v b)
  exact ⟨(Scheme.Modules.pullback a.hom).mapIso d ≪≫ ea ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.invModule h) ≪≫ eb.symm ≪≫
    (Scheme.Modules.pullback b.hom).mapIso d.symm⟩

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.support_eq_of_points
#print axioms ZInQBlueprint.ThetaClass.comap_eq_of_reduced_points
#print axioms ZInQBlueprint.ThetaClass.pullback_line_of_ideal
