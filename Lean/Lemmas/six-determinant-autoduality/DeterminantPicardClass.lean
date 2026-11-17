import PolarizationClass
import Nyll.AbelianVarieties.LineBundles.Translation

/-! Translation classes in the Picard group of a geometric abelian variety. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj
namespace ZInQBlueprint.DeterminantAutoduality
open GeometricMarking QuaternionMarking AbelianModel NormalDescent SixThetaRestriction ThetaClass
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

/-- The units of the monoid of isomorphism classes of modules contain the line-bundle classes. -/
abbrev PicUnits (X : Scheme.{0}) := (Skeleton X.Modules)ˣ

def lineClass {X : Scheme.{0}} (L : X.Modules) (hL : L.IsInvertible) : PicUnits X := by
  let V := hL.exists_tensor_inverse.choose
  let e := hL.exists_tensor_inverse.choose_spec.2.some
  exact ⟨toSkeleton L,toSkeleton V,
    (Skeleton.toSkeleton_tensorObj L V).symm.trans ((toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩).trans Skeleton.one_eq.symm),
    (mul_comm _ _).trans ((Skeleton.toSkeleton_tensorObj L V).symm.trans
      ((toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩).trans Skeleton.one_eq.symm))⟩

theorem lineClass_val {X : Scheme.{0}} (L : X.Modules) (hL : L.IsInvertible) :
    (lineClass L hL).val = toSkeleton L := by
  unfold lineClass
  rfl

theorem lineClass_eq {X : Scheme.{0}} {L M : X.Modules} (hL : L.IsInvertible) (hM : M.IsInvertible) :
    lineClass L hL = lineClass M hM ↔ Nonempty (L ≅ M) := by
  rw [Units.ext_iff,lineClass_val,lineClass_val,toSkeleton_eq_toSkeleton_iff]

theorem lineClass_tensor {X : Scheme.{0}} {L M : X.Modules} (hL : L.IsInvertible) (hM : M.IsInvertible) :
    lineClass (L ⊗ M) (hL.tensor hM) = lineClass L hL * lineClass M hM := by
  apply Units.ext
  rw [lineClass_val,Units.val_mul,lineClass_val,lineClass_val,Skeleton.toSkeleton_tensorObj]

variable {A : GroupScheme Qbar}

abbrev translated (L : A.X.left.Modules) (t : sections A) : A.X.left.Modules :=
  pullModule (translation t).hom L

theorem translation_zero : (translation (0 : sections A)).hom = 𝟙 A.X := by
  change (𝟙 A.X) * (toBase A.X ≫ (1 : basePoint ⟶ A.X)) = _
  rw [MonObj.comp_one,mul_one]

theorem square (hA : IsAbelianScheme A) (L : A.X.left.Modules) (hL : L.IsInvertible) (x y : sections A) :
    Nonempty (translated L x ⊗ translated L y ≅ translated L (x+y) ⊗ L) := by
  let : GrpObj (Over.mk A.X.hom) := inferInstanceAs (GrpObj A.X)
  let : IsCommMonObj (Over.mk A.X.hom) := inferInstanceAs (IsCommMonObj A.X)
  have e := Scheme.Modules.forall_nonempty_pullback_translate_tensor_iso Qbar A.X.hom hA.smooth hA.proper
    hA.geometricallyConnected L hL x.toMul y.toMul
  have h : CartesianMonoidalCategory.toUnit A.X = toBase A.X := by
    apply Over.OverMorphism.ext
    exact Over.toUnit_left
  change Nonempty (pullModule (𝟙 A.X * (CartesianMonoidalCategory.toUnit A.X ≫ x.toMul)) L ⊗
    pullModule (𝟙 A.X * (CartesianMonoidalCategory.toUnit A.X ≫ y.toMul)) L ≅
    pullModule (𝟙 A.X * (CartesianMonoidalCategory.toUnit A.X ≫ (x.toMul*y.toMul))) L ⊗ L) at e
  rw [h] at e
  exact e

abbrev translatedClass (L : A.X.left.Modules) (hL : L.IsInvertible) (x : sections A) :=
  lineClass (translated L x) (hL.pullback (translation x).hom.left)

/-- The homomorphism x ↦ [T_x^*L] [L]⁻¹ on geometric points. -/
def polarization (hA : IsAbelianScheme A) (L : A.X.left.Modules) (hL : L.IsInvertible) :
    sections A →+ Additive (PicUnits A.X.left) where
  toFun x := Additive.ofMul (translatedClass L hL x / lineClass L hL)
  map_zero' := by
    change translatedClass L hL 0 / lineClass L hL = 1
    apply (div_eq_one).mpr
    apply (lineClass_eq _ _).mpr
    unfold translated
    rw [translation_zero]
    exact ⟨(Scheme.Modules.pullbackId _).app L⟩
  map_add' x y := by
    have e := (lineClass_eq ((hL.pullback (translation x).hom.left).tensor (hL.pullback (translation y).hom.left))
      ((hL.pullback (translation (x+y)).hom.left).tensor hL)).mpr (square hA L hL x y)
    rw [lineClass_tensor,lineClass_tensor] at e
    change translatedClass L hL (x+y) / lineClass L hL =
      (translatedClass L hL x / lineClass L hL) * (translatedClass L hL y / lineClass L hL)
    change translatedClass L hL x * translatedClass L hL y =
      translatedClass L hL (x+y) * lineClass L hL at e
    rw [div_mul_div_comm,e]
    exact (mul_div_mul_right_eq_div _ _ _).symm

theorem principal_iff_classes (hA : IsAbelianScheme A) (L : A.X.left.Modules) (hL : L.IsInvertible) :
    PrincipalTranslations (A := A) L ↔
      ∀ N : A.X.left.Modules, ∀ hN : N.IsInvertible, RelPicard.IsAlgEquivZero A.X.hom N →
        Additive.ofMul (lineClass N hN) ∈ (polarization hA L hL).range := by
  constructor
  · intro H N hN hn
    obtain ⟨t,e⟩ := H N hN hn
    refine ⟨t,?_⟩
    change translatedClass L hL t / lineClass L hL = lineClass N hN
    apply (div_eq_iff_eq_mul).mpr
    rw [mul_comm,←lineClass_tensor]
    exact ((lineClass_eq _ _).mpr e).symm
  · intro H N hN hn
    obtain ⟨t,ht⟩ := H N hN hn
    change translatedClass L hL t / lineClass L hL = lineClass N hN at ht
    refine ⟨t,(lineClass_eq (hL.tensor hN) (hL.pullback (translation t).hom.left)).mp ?_⟩
    rw [lineClass_tensor,mul_comm]
    exact ((div_eq_iff_eq_mul).mp ht).symm

end
end ZInQBlueprint.DeterminantAutoduality
#print axioms ZInQBlueprint.DeterminantAutoduality.lineClass_eq
#print axioms ZInQBlueprint.DeterminantAutoduality.square
#print axioms ZInQBlueprint.DeterminantAutoduality.polarization
#print axioms ZInQBlueprint.DeterminantAutoduality.principal_iff_classes
