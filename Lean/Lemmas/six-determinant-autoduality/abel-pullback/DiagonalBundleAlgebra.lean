/- 
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Adapted from the NYLL sources recorded in diagonal-extract.json.
Released under the Apache License 2.0; see sources/LICENSE and sources/NOTICE.
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AbelJacobiFamily
import Nyll.AlgebraicCurves.Geometry.Picard.AbelJacobi.AjFamilyFibreIso
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgebraicEquivalence.RelativeDivisorAlgebraicEquivalenceTwistModuleFibre
import Nyll.AlgebraicCurves.Geometry.Picard.Functor.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Designation
import Nyll.AlgebraicCurves.Geometry.Picard.Representability.Representation
import Nyll.AlgebraicCurves.Geometry.Schemes.Morphisms.HomInvertibleKerCompEqId
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.IdealSheafModuleMaps
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealInvertibleModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealIsoPullbackModuleComparison
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealModuleTensorInvModuleIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealMulModuleIsoTensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Divisors.InvertibleIdealPullbackInvModuleIso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleDual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoTensorUnitField
import Nyll.AlgebraicCurves.Geometry.Sheaves.Tensor.InvertibleIsoTensorUnitLocalRing
import Nyll.AlgebraicCurves.RelativeDivisors.BaseChange.InvertibleTwistModulePullbackIso
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierIdeal
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier.EffectiveCartierInvertibility
import Nyll.AlgebraicCurves.RelativeDivisors.LineBundles.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.PointKernelPullback
import Nyll.AlgebraicCurves.RelativeDivisors.PointSums.RelEffCartierDivOfPoint
import Nyll.SchemeTheory.CategoryTheory.MonoidalCategoryIsoTensorIsoTensorUnit
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.CartierProducts
import Nyll.SchemeTheory.Divisors.FlatPullback
import Nyll.SchemeTheory.Modules.Invertible.Rigidify
import Nyll.SchemeTheory.Modules.Tensor.Monoidal
import Nyll.SchemeTheory.Modules.Tensor.PullbackMonoidal

/-! The scheme and sheaf arguments for the normalized diagonal. The original
sources also develop étale cycle classes; this module retains only the
Cartesian, Cartier and Picard constructions under a distinct namespace. -/
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open NeronModelInfra GoodReductionJacobian
noncomputable section
universe u

namespace ZInQBlueprint.AbelDiagonalAlgebra.Classical
section
variable {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-- A section of the second factor gives the actual section of the
first product projection. -/
def kunnethSectionLeft (p : S ⟶ Y) (hp : p ≫ g = 𝟙 S) : X ⟶ pullback f g :=
  pullback.lift (𝟙 X) (f ≫ p) (by
    rw [Category.id_comp, Category.assoc, hp, Category.comp_id])

/-- A section of the first factor gives the actual section of the
second product projection. -/
def kunnethSectionRight (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) : Y ⟶ pullback f g :=
  pullback.lift (g ≫ p) (𝟙 Y) (by
    rw [Category.assoc, hp, Category.comp_id, Category.id_comp])

theorem kunnethSectionLeft_fst (p : S ⟶ Y) (hp : p ≫ g = 𝟙 S) :
    kunnethSectionLeft f g p hp ≫ pullback.fst f g = 𝟙 X :=
  pullback.lift_fst _ _ _

theorem kunnethSectionLeft_snd (p : S ⟶ Y) (hp : p ≫ g = 𝟙 S) :
    kunnethSectionLeft f g p hp ≫ pullback.snd f g = f ≫ p :=
  pullback.lift_snd _ _ _

theorem kunnethSectionRight_fst (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    kunnethSectionRight f g p hp ≫ pullback.fst f g = g ≫ p :=
  pullback.lift_fst _ _ _

theorem kunnethSectionRight_snd (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    kunnethSectionRight f g p hp ≫ pullback.snd f g = 𝟙 Y :=
  pullback.lift_snd _ _ _


end
end ZInQBlueprint.AbelDiagonalAlgebra.Classical
namespace ZInQBlueprint.AbelDiagonalAlgebra
/-- The actual graph kernel as an actual effective Cartier divisor in a
product with a separated smooth relative curve. -/
def graphEffectiveCartierDivisor
    {X Y S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (g : Y ⟶ S)
    (a : Y ⟶ X) (ha : a ≫ f = g) :
    Scheme.EffectiveCartierDivisor (pullback f g) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (C := Scheme.{u}) (fun {_ _} h => SmoothOfRelativeDimension 1 h) :=
    smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)
  have : SmoothOfRelativeDimension 1 (pullback.snd f g) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {_ _ : Scheme.{u}} h => SmoothOfRelativeDimension 1 h)
      (IsPullback.of_hasPullback f g) inferInstance
  exact ⟨(graphOver f a ha).ker,
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id
      (graphOver f a ha) (graphOver_snd f a ha)).isEffectiveCartier⟩

end ZInQBlueprint.AbelDiagonalAlgebra
namespace ZInQBlueprint.AbelDiagonalAlgebra.Classical
variable {X S : Scheme.{u}} (f : X ⟶ S) (p : S ⟶ X) (hp : p ≫ f = 𝟙 S)

/-- The actual left point section preserves the original structure map. -/
theorem kunnethSectionLeft_comp_structure :
    kunnethSectionLeft f f p hp ≫ (pullback.snd f f ≫ f) = f := by
  rw [← Category.assoc, kunnethSectionLeft_snd, Category.assoc, hp,
    Category.comp_id]

/-- The actual right point section preserves that same structure map. -/
theorem kunnethSectionRight_comp_structure :
    kunnethSectionRight f f p hp ≫ (pullback.snd f f ≫ f) = f := by
  rw [← Category.assoc, kunnethSectionRight_snd, Category.id_comp]

/-- The original left point section meets the original diagonal in the
original point, as an actual Cartesian square. -/
theorem diagonal_kunnethSectionLeft_isPullback :
    IsPullback p p (kunnethSectionLeft f f p hp)
      (graphOver f (𝟙 X) (Category.id_comp f)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply pullback.hom_ext
    · simp only [Category.assoc, kunnethSectionLeft_fst, graphOver_fst,
        Category.comp_id]
    · simp only [Category.assoc, kunnethSectionLeft_snd, graphOver_snd,
        Category.comp_id]
      rw [← Category.assoc, hp, Category.id_comp]
  · intro T a b h₁ h₂
    have h := congrArg (fun k : T ⟶ X => k ≫ f) h₁
    simpa only [Category.assoc, hp, Category.comp_id] using h
  · intro T a b h
    have hab : a = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.fst f f) h
      simpa only [Category.assoc, kunnethSectionLeft_fst, graphOver_fst,
        Category.comp_id] using h'
    have hfp : a ≫ f ≫ p = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.snd f f) h
      simpa only [Category.assoc, kunnethSectionLeft_snd, graphOver_snd,
        Category.comp_id] using h'
    exact ⟨a ≫ f, (Category.assoc a f p).trans (hfp.trans hab.symm),
      (Category.assoc a f p).trans hfp⟩

/-- The original right point section has the same actual diagonal
intersection, with the two projection equations interchanged. -/
theorem diagonal_kunnethSectionRight_isPullback :
    IsPullback p p (kunnethSectionRight f f p hp)
      (graphOver f (𝟙 X) (Category.id_comp f)) := by
  refine IsPullback.mk' ?_ ?_ ?_
  · apply pullback.hom_ext
    · simp only [Category.assoc, kunnethSectionRight_fst, graphOver_fst,
        Category.comp_id]
      rw [← Category.assoc, hp, Category.id_comp]
    · simp only [Category.assoc, kunnethSectionRight_snd, graphOver_snd,
        Category.comp_id]
  · intro T a b h₁ h₂
    have h := congrArg (fun k : T ⟶ X => k ≫ f) h₁
    simpa only [Category.assoc, hp, Category.comp_id] using h
  · intro T a b h
    have hab : a = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.snd f f) h
      simpa only [Category.assoc, kunnethSectionRight_snd, graphOver_snd,
        Category.comp_id] using h'
    have hfp : a ≫ f ≫ p = b := by
      have h' := congrArg (fun k : T ⟶ pullback f f => k ≫ pullback.fst f f) h
      simpa only [Category.assoc, kunnethSectionRight_fst, graphOver_fst,
        Category.comp_id] using h'
    exact ⟨a ≫ f, (Category.assoc a f p).trans (hfp.trans hab.symm),
      (Category.assoc a f p).trans hfp⟩

variable [IsSeparated f]

/-- The full original diagonal ideal pulls back to the full point
kernel along the left point section. -/
theorem diagonalIdeal_comap_kunnethSectionLeft :
    (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap
        (kunnethSectionLeft f f p hp) = p.ker := by
  let H := diagonal_kunnethSectionLeft_isPullback f p hp
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (graphOver f (𝟙 X) (Category.id_comp f))
    (kunnethSectionLeft f f p hp)).symm.trans
      ((Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom
        (pullback.fst (kunnethSectionLeft f f p hp)
          (graphOver f (𝟙 X) (Category.id_comp f)))).symm.trans
            (congrArg (fun q : S ⟶ X => q.ker) H.isoPullback_hom_fst))

/-- The same ideal equality for the right point section. -/
theorem diagonalIdeal_comap_kunnethSectionRight :
    (graphOver f (𝟙 X) (Category.id_comp f)).ker.comap
        (kunnethSectionRight f f p hp) = p.ker := by
  let H := diagonal_kunnethSectionRight_isPullback f p hp
  exact (Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (graphOver f (𝟙 X) (Category.id_comp f))
    (kunnethSectionRight f f p hp)).symm.trans
      ((Scheme.Hom.ker_comp_of_isIso H.isoPullback.hom
        (pullback.fst (kunnethSectionRight f f p hp)
          (graphOver f (𝟙 X) (Category.id_comp f)))).symm.trans
            (congrArg (fun q : S ⟶ X => q.ker) H.isoPullback_hom_fst))


end ZInQBlueprint.AbelDiagonalAlgebra.Classical
namespace ZInQBlueprint.AbelDiagonalAlgebra
/-- The original kernel of a section of a separated smooth relative
curve, with the genuine Cartier regularity supplied by that section. -/
def sectionEffectiveCartierDivisor
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    Scheme.EffectiveCartierDivisor X :=
  ⟨p.ker, (Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp).isEffectiveCartier⟩

/-- The divisor retains the actual point kernel ideal. -/
theorem sectionEffectiveCartierDivisor_ideal
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [SmoothOfRelativeDimension 1 f] (p : S ⟶ X) (hp : p ≫ f = 𝟙 S) :
    (sectionEffectiveCartierDivisor f p hp).1 = p.ker := rfl


section
open ZInQBlueprint.AbelDiagonalAlgebra.Classical

section Divisors

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
  [SmoothOfRelativeDimension 1 f] (p : S ⟶ X) (hp : p ≫ f = 𝟙 S)

/-- The original point ideal pulled back under the first projection,
with its Cartier property supplied by actual flatness. -/
def productPointFstEffectiveCartierDivisor : Scheme.EffectiveCartierDivisor (pullback f f) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨p.ker.comap (pullback.fst f f),
    (sectionEffectiveCartierDivisor f p hp).2.comap_of_flat (pullback.fst f f)⟩

/-- The same original point ideal pulled back under the second
projection of the actual scheme product. -/
def productPointSndEffectiveCartierDivisor : Scheme.EffectiveCartierDivisor (pullback f f) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  exact ⟨p.ker.comap (pullback.snd f f),
    (sectionEffectiveCartierDivisor f p hp).2.comap_of_flat (pullback.snd f f)⟩

/-- The two actual point pullbacks form the effective divisor whose
original cycle class is the sum of the two geometric edge classes. -/
def diagonalEdgeEffectiveCartierDivisor : Scheme.EffectiveCartierDivisor (pullback f f) :=
  ⟨(productPointFstEffectiveCartierDivisor f p hp).1 *
      (productPointSndEffectiveCartierDivisor f p hp).1,
    (productPointFstEffectiveCartierDivisor f p hp).2.mul
      (productPointSndEffectiveCartierDivisor f p hp).2⟩

/-- The original first point pullback has exactly the original
constant-graph ideal used by the Abel–Jacobi family. -/
theorem productPointFstEffectiveCartierDivisor_ideal :
    (productPointFstEffectiveCartierDivisor f p hp).1 =
      (graphOver f (f ≫ p) (by rw [Category.assoc, hp, Category.comp_id])).ker :=
  pointKernel_comap_fst f f p hp

end Divisors

/-- The signed divisor bundle of the actual normalized diagonal is
the original Abel–Jacobi family with the actual second point ideal.
No equality of cohomological comparison maps is an input. -/
theorem diagonalMiddleDivisorBundle_iso_ajFamily
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _) :
    Nonempty
      ((graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module ≅
        RelPicard.ajFamily (a := f) ⟨p, hp⟩ ⊗
          (productPointSndEffectiveCartierDivisor f p hp).1.module) := by
  let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
  let A := productPointFstEffectiveCartierDivisor f p hp
  let B := productPointSndEffectiveCartierDivisor f p hp
  have hA : A.1.IsInvertible := A.2.isInvertible
  have hB : B.1.IsInvertible := B.2.isInvertible
  obtain ⟨eAB⟩ := hA.nonempty_mul_module_iso_tensor hB
  let eA : A.1.module ≅ (RelPicard.constDiv (a := f) ⟨p, hp⟩).idealModule :=
    eqToIso (congrArg (fun I : (pullback f f).IdealSheafData => I.module)
      (pointKernel_comap_fst f f p hp))
  exact ⟨(Iso.refl D.1.invModule ⊗ᵢ eAB) ≪≫
    (α_ D.1.invModule A.1.module B.1.module).symm ≪≫
    ((Iso.refl D.1.invModule ⊗ᵢ eA) ⊗ᵢ Iso.refl B.1.module)⟩


end
section
open ZInQBlueprint.AbelDiagonalAlgebra.Classical

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

/-- The original Abel–Jacobi family's restriction to its actual
rigidifying section is the original point line bundle. -/
theorem ajFamily_rigSection_iso_pointLineBundle :
    Nonempty
      ((Scheme.Modules.pullback (RelPicard.rigSection f f ⟨p, hp⟩)).obj
          (RelPicard.ajFamily (a := f) ⟨p, hp⟩) ≅ p.ker.invModule) := by
  let σ := RelPicard.rigSection f f ⟨p, hp⟩
  let D := graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)
  let A := productPointFstEffectiveCartierDivisor f p hp
  have hP : p.ker.IsInvertible := (sectionEffectiveCartierDivisor f p hp).2.isInvertible
  have hD : D.1.IsInvertible := D.2.isInvertible
  have hA : A.1.IsInvertible := A.2.isInvertible
  have hσD : D.1.comap σ = p.ker :=
    diagonalIdeal_comap_kunnethSectionRight f p hp
  have hσDinv : (D.1.comap σ).IsInvertible := hσD.symm ▸ hP
  obtain ⟨d⟩ := hD.nonempty_pullback_invModule_iso σ hσDinv
  let eD : (Scheme.Modules.pullback σ).obj D.1.invModule ≅ p.ker.invModule :=
    d ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule hσD)
  have hF : IsIso (p.ker.pullbackModuleComparison (pullback.fst f f)) :=
    hP.isIso_pullbackModuleComparison (pullback.fst f f) hA
  let eF : (Scheme.Modules.pullback (pullback.fst f f)).obj p.ker.module ≅ A.1.module :=
    @asIso _ _ _ _ (p.ker.pullbackModuleComparison (pullback.fst f f)) hF
  have hσfst : σ ≫ pullback.fst f f = f ≫ p :=
    kunnethSectionRight_fst f f p hp
  let eConst : (Scheme.Modules.pullback σ).obj A.1.module ≅
      (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj p.ker.module) :=
    (Scheme.Modules.pullback σ).mapIso eF.symm ≪≫
      (Scheme.Modules.pullbackComp σ (pullback.fst f f)).app p.ker.module ≪≫
      (Scheme.Modules.pullbackCongr hσfst).app p.ker.module ≪≫
      ((Scheme.Modules.pullbackComp f p).app p.ker.module).symm
  obtain ⟨eK⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field K
    ((Scheme.Modules.pullback p).obj p.ker.module) (hP.isInvertible_module.pullback p)
  let eUnit : (Scheme.Modules.pullback σ).obj A.1.module ≅ 𝟙_ X.Modules :=
    eConst ≪≫ (Scheme.Modules.pullback f).mapIso eK ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso f
  let eA : A.1.module ≅ (RelPicard.constDiv (a := f) ⟨p, hp⟩).idealModule :=
    eqToIso (congrArg (fun I : (pullback f f).IdealSheafData => I.module)
      (pointKernel_comap_fst f f p hp))
  exact ⟨(Scheme.Modules.pullback σ).mapIso (Iso.refl D.1.invModule ⊗ᵢ eA.symm) ≪≫
    Scheme.Modules.pullbackTensorObjIso σ D.1.invModule A.1.module ≪≫
      (eD ⊗ᵢ eUnit) ≪≫ ρ_ p.ker.invModule⟩

/-- The actual rigidification of the Abel–Jacobi family is the signed
divisor bundle of the actual normalized diagonal. -/
theorem rigidify_ajFamily_iso_middleDivisorBundle :
    Nonempty
      (Scheme.Modules.rigidify (RelPicard.rigSection f f ⟨p, hp⟩) (pullback.snd f f)
          (RelPicard.ajFamily (a := f) ⟨p, hp⟩) ≅
        (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) := by
  let σ := RelPicard.rigSection f f ⟨p, hp⟩
  let L := RelPicard.ajFamily (a := f) ⟨p, hp⟩
  let B := productPointSndEffectiveCartierDivisor f p hp
  have hP : p.ker.IsInvertible := (sectionEffectiveCartierDivisor f p hp).2.isInvertible
  have hB : B.1.IsInvertible := B.2.isInvertible
  have hL : Scheme.Modules.IsInvertible L := RelPicard.isInvertible_ajFamily ⟨p, hp⟩
  obtain ⟨eσ⟩ := ajFamily_rigSection_iso_pointLineBundle f p hp
  obtain ⟨eDual⟩ := nonempty_iso_of_tensor_iso_tensorUnit eσ
    (hL.pullback σ).dual.2 hP.nonempty_module_tensor_invModule_iso.2
  have hBiso : IsIso (p.ker.pullbackModuleComparison (pullback.snd f f)) :=
    hP.isIso_pullbackModuleComparison (pullback.snd f f) hB
  let eB : (Scheme.Modules.pullback (pullback.snd f f)).obj p.ker.module ≅ B.1.module :=
    @asIso _ _ _ _ (p.ker.pullbackModuleComparison (pullback.snd f f)) hBiso
  obtain ⟨e⟩ := diagonalMiddleDivisorBundle_iso_ajFamily f p hp
  exact ⟨(Iso.refl L ⊗ᵢ ((Scheme.Modules.pullback (pullback.snd f f)).mapIso eDual ≪≫ eB)) ≪≫
    e.symm⟩

/-- The original relative diagonal twist, used by actual Picard
representability, is the very same signed divisor bundle. -/
theorem diagonalTwistModule_iso_middleDivisorBundle :
    Nonempty
      ((RelPicard.diagDiv (a := f)).twistModule f ⟨p, hp⟩ ≅
        (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) := by
  let eL : (RelPicard.diagDiv (a := f)).lineBundle ⊗
      ((RelPicard.sectionIdeal f ⟨p, hp⟩ f) ^ 1).module ≅
        RelPicard.ajFamily (a := f) ⟨p, hp⟩ :=
    Iso.refl _ ⊗ᵢ eqToIso (congrArg Scheme.IdealSheafData.module (pow_one _))
  obtain ⟨e⟩ := rigidify_ajFamily_iso_middleDivisorBundle f p hp
  exact ⟨Scheme.Modules.rigidifyMapIso (RelPicard.rigSection f f ⟨p, hp⟩)
    (pullback.snd f f) eL ≪≫ e⟩


end
section
open ZInQBlueprint.AbelDiagonalAlgebra.Classical

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of K)) [SmoothOfRelativeDimension 1 f]
  (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)

section

variable [IsSeparated f]

/-- The actual relative diagonal twist, with its original rigidification. -/
def diagonalRigidifiedLineBundle : RelPicard.RigidifiedLineBundle f ⟨p, hp⟩ f where
  L := (RelPicard.diagDiv (a := f)).twistModule f ⟨p, hp⟩
  isInvertible :=
    (RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso
      f ⟨p, hp⟩ (RelPicard.diagDiv (a := f))).1
  rigidified :=
    (RelEffCartierDiv.isInvertible_twistModule_and_nonempty_pullback_iso
      f ⟨p, hp⟩ (RelPicard.diagDiv (a := f))).2

end

variable [IsProper f] [GeometricallyIntegral f]

/-- The original relative Cartier theorem supplies the Picard condition
for every geometric fibre of the actual diagonal family. -/
theorem diagonalRigidifiedLineBundle_fibrewise :
    RelPicard.FibrewiseAlgEquivZero (diagonalRigidifiedLineBundle f p hp) := by
  intro k _ _ s
  exact RelEffCartierDiv.isAlgEquivZero_twistModule_fibre
    f ⟨p, hp⟩ (RelPicard.diagDiv (a := f)) k s

variable (D : RelativePic0Designation K f)
  (h : RelPicard.RepresentsRelSubPic f ⟨p, hp⟩ (RelPicard.algEquivZeroCut f ⟨p, hp⟩) D)

/-- The original representing morphism of the actual rigidified
diagonal family. -/
def diagonalPicardClassifyingMap : SchemeHomOver f D.toBase :=
  h.classify f (diagonalRigidifiedLineBundle f p hp)
    (diagonalRigidifiedLineBundle_fibrewise f p hp)

/-- The original Poincaré family pulled back along the actual
classifying morphism is the original normalized diagonal bundle on the
whole self-product. -/
theorem diagonalPicardClassifyingMap_poincareIso :
    Nonempty
      ((h.poincare.pullbackAlong (diagonalPicardClassifyingMap f p hp D h)).L ≅
        (graphEffectiveCartierDivisor f f (𝟙 X) (Category.id_comp f)).1.invModule ⊗
          (diagonalEdgeEffectiveCartierDivisor f p hp).1.module) := by
  obtain ⟨e⟩ := h.classify_spec f (diagonalRigidifiedLineBundle f p hp)
    (diagonalRigidifiedLineBundle_fibrewise f p hp)
  obtain ⟨d⟩ := diagonalTwistModule_iso_middleDivisorBundle f p hp
  exact ⟨e ≪≫ d⟩

/-- Every field-valued point of the same diagonal classifying map
classifies its actual point-minus-base-point line bundle. The extra
normalizing factor is pulled back from the parameter field, where the
original invertible module is trivial. -/
theorem diagonalPicardClassifyingMap_fieldPointIso
    (L : Type u) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
    (x : SchemeHomOver t f) :
    Nonempty ((h.poincare.pullbackAlong
      ⟨x.1 ≫ (diagonalPicardClassifyingMap f p hp D h).1,
        (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) (diagonalPicardClassifyingMap f p hp D h).2).trans x.2)⟩).L ≅
      (RelEffCartierDiv.ofPoint f x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint f (t ≫ p)
          ((Category.assoc _ _ _).trans
            ((congrArg (t ≫ ·) hp).trans (Category.comp_id t)))).idealModule) := by
  let aj := diagonalPicardClassifyingMap f p hp D h
  let ψ := RelPicard.baseChangeSnd f x
  let A := RelPicard.ajFamily (a := f) ⟨p, hp⟩
  let B := productPointSndEffectiveCartierDivisor f p hp
  let V := (RelEffCartierDiv.ofPoint f x.1 x.2).lineBundle ⊗
    (RelEffCartierDiv.ofPoint f (t ≫ p)
      ((Category.assoc _ _ _).trans
        ((congrArg (t ≫ ·) hp).trans (Category.comp_id t)))).idealModule
  obtain ⟨eClassify⟩ := diagonalPicardClassifyingMap_poincareIso f p hp D h
  obtain ⟨eMiddle⟩ := diagonalMiddleDivisorBundle_iso_ajFamily f p hp
  obtain ⟨ePoint⟩ := RelPicard.nonempty_ajFamily_pullbackAlong_iso ⟨p, hp⟩ t x
  have hP : p.ker.IsInvertible := (sectionEffectiveCartierDivisor f p hp).2.isInvertible
  let c : (Scheme.Modules.pullback (pullback.snd f f)).obj p.ker.module ⟶ B.1.module :=
    p.ker.pullbackModuleComparison (pullback.snd f f)
  have : IsIso c :=
    hP.isIso_pullbackModuleComparison (pullback.snd f f) B.2.isInvertible
  let eB : (Scheme.Modules.pullback (pullback.snd f f)).obj p.ker.module ≅ B.1.module :=
    asIso c
  obtain ⟨eField⟩ :=
    (hP.isInvertible_module.pullback x.1).nonempty_iso_tensorUnit_of_isLocalRing
  have hψ : ψ ≫ pullback.snd f f = pullback.snd f t ≫ x.1 := by
    change RelPicard.baseChangeSnd f x ≫ pullback.snd f f = _
    unfold RelPicard.baseChangeSnd
    exact pullback.lift_snd _ _ _
  let eUnit : (Scheme.Modules.pullback ψ).obj B.1.module ≅ 𝟙_ (pullback f t).Modules :=
    (Scheme.Modules.pullback ψ).mapIso eB.symm ≪≫
      (Scheme.Modules.pullbackComp ψ (pullback.snd f f)).app p.ker.module ≪≫
      (Scheme.Modules.pullbackCongr hψ).app p.ker.module ≪≫
      ((Scheme.Modules.pullbackComp (pullback.snd f t) x.1).app p.ker.module).symm ≪≫
      (Scheme.Modules.pullback (pullback.snd f t)).mapIso eField ≪≫
      Scheme.Modules.pullbackTensorUnitObjIso (pullback.snd f t)
  let eComp : (h.poincare.pullbackAlong (RelPicard.postComp aj x)).L ≅
      (Scheme.Modules.pullback ψ).obj (h.poincare.pullbackAlong aj).L :=
    (Scheme.Modules.pullbackCongr (RelPicard.baseChangeSnd_comp f aj x).symm).app
        h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp ψ (RelPicard.baseChangeSnd f aj)).app h.poincare.L).symm
  exact ⟨eComp ≪≫ (Scheme.Modules.pullback ψ).mapIso (eClassify ≪≫ eMiddle) ≪≫
    Scheme.Modules.pullbackTensorObjIso ψ A B.1.module ≪≫ (ePoint ⊗ᵢ eUnit) ≪≫ ρ_ V⟩


end
end ZInQBlueprint.AbelDiagonalAlgebra
end
#print axioms ZInQBlueprint.AbelDiagonalAlgebra.diagonalPicardClassifyingMap_poincareIso
#print axioms ZInQBlueprint.AbelDiagonalAlgebra.diagonalPicardClassifyingMap_fieldPointIso
