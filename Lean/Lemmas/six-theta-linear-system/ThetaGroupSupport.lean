import ThetaSupportTransport
import ThetaTranslation

/-! The zero divisor evaluated on the additive group of geometric points. -/

open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaLinearSystem
open AbelianModel QuaternionMarking GeometricMarking SixThetaRestriction NormalDescent
noncomputable section

/-- Points of the project group carried by an ideal sheaf. -/
def sectionSupport {A : GroupScheme Qbar} (I : A.X.left.IdealSheafData) : Set (sections A) :=
  {p | p.toMul ∈ fieldSupport I}

/-- The marking comparison consumes one undecorated line-bundle isomorphism.
The conclusion compares the actual automorphism and translation on geometric
points. -/
theorem group_mem_iff {A : GroupScheme Qbar} (L : A.X.left.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ A.X.left.Modules ⟶ L) (hs : s ≠ 0)
    (h0 : rankH0 A.X.hom L = 1) (a : A ≅ A) (t : sections A)
    (e : (Scheme.Modules.pullback a.hom.hom.hom.hom.left).obj L ≅
      (Scheme.Modules.pullback (translation t).hom.left).obj L) (p : sections A) :
    onSections a.hom p ∈ sectionSupport (Scheme.Modules.zeroSchemeIdeal s) ↔
      p+t ∈ sectionSupport (Scheme.Modules.zeroSchemeIdeal s) := by
  rw [← translate_point p t]
  let d := (Over.forget _).mapIso ((CommGrp.forget _).mapIso a)
  let u := (Over.forget _).mapIso (translation t)
  exact point_mem_iff A.X.hom L hL s hs h0 d u e (p.toMul.left (IsLocalRing.closedPoint Qbar))

/-- The same point comparison directly in the vanishing convention for
Poincaré-normalized sections. It uses no reduced-support identification. -/
theorem group_vanishes_iff {A : GroupScheme Qbar} (L : A.X.left.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ A.X.left.Modules ⟶ L) (hs : s ≠ 0)
    (h0 : rankH0 A.X.hom L = 1) (a : A ≅ A) (t : sections A)
    (e : (Scheme.Modules.pullback a.hom.hom.hom.hom.left).obj L ≅
      (Scheme.Modules.pullback (translation t).hom.left).obj L) (p : sections A) :
    Scheme.Modules.pullbackSection (onSections a.hom p).toMul.left s = 0 ↔
      Scheme.Modules.pullbackSection (p+t).toMul.left s = 0 := by
  rw [← translate_point p t]
  exact vanishes_comp_iff A.X.hom L hL s hs h0
    ((Over.forget _).mapIso ((CommGrp.forget _).mapIso a))
    ((Over.forget _).mapIso (translation t)) e p.toMul.left

/-- Forward image version. With inverse pullbacks, the translation has the
same sign on the geometric points as it has on the forward scheme map. -/
theorem group_image_translate {A : GroupScheme Qbar} (L : A.X.left.Modules)
    (hL : Scheme.Modules.IsInvertible L) (s : 𝟙_ A.X.left.Modules ⟶ L) (hs : s ≠ 0)
    (h0 : rankH0 A.X.hom L = 1) (a : A ≅ A) (t : sections A)
    (e : (Scheme.Modules.pullback a.inv.hom.hom.hom.left).obj L ≅
      (Scheme.Modules.pullback (translation t).inv.left).obj L) :
    (onSections a.hom) '' sectionSupport (Scheme.Modules.zeroSchemeIdeal s) =
      (fun p => p+t) '' sectionSupport (Scheme.Modules.zeroSchemeIdeal s) := by
  let d := (CommGrp.forget _).mapIso a
  have h := image_fieldSupport_eq L hL s hs h0 d (translation t) e
  ext p
  constructor
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨v,hv,hv'⟩ := (Set.ext_iff.mp h (q.toMul ≫ d.hom)).mp ⟨q.toMul,hq,rfl⟩
    refine ⟨Additive.ofMul v,hv,?_⟩
    exact (translate_point (Additive.ofMul v) t).symm.trans (congrArg Additive.ofMul hv')
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨v,hv,hv'⟩ := (Set.ext_iff.mp h (q.toMul ≫ (translation t).hom)).mpr ⟨q.toMul,hq,rfl⟩
    refine ⟨Additive.ofMul v,hv,?_⟩
    exact (congrArg Additive.ofMul hv').trans (translate_point q t)

end
end ZInQBlueprint.ThetaLinearSystem
#print axioms ZInQBlueprint.ThetaLinearSystem.group_mem_iff
#print axioms ZInQBlueprint.ThetaLinearSystem.group_vanishes_iff
#print axioms ZInQBlueprint.ThetaLinearSystem.group_image_translate
