import SexticChartFraction
import Nyll.SchemeTheory.FunctionFields.StructureMorphismNaturality
import Nyll.SchemeTheory.FunctionFields.OpenImmersion
import Nyll.SchemeTheory.FunctionFields.AffineFunctionFieldNaturality
import Nyll.AlgebraicCurves.Models.Points.AlgEquivPointPlaceCompHomEqAlgAutSmulPointPlace

/-! A chart with equation y²=f identifies the scheme function field and its involution,
with the original embedding of constants. -/
open CategoryTheory AlgebraicGeometry AlgebraicCurve Polynomial
namespace ZInQBlueprint.FibreDivisors
open BinaryCover
open AlgebraicCurves.Models.Proofs.CurveModel_exists_algEquiv_pointEquivPlace_comp_hom_eq_ofAlgAut_smul_pointEquivPlace.AlgebraicCurve.CurveModel.ModelIndepSol.FunctionFieldPull
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem pull_eq_fieldMap {X Y : Scheme} [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Y]
    (f : X ⟶ Y) (hd : DenseRange f) (hs : f.base (genericPoint X) ⤳ genericPoint Y) :
    (pull f hs).hom = f.functionFieldMap hd := by
  have transport (a b : Y) (h : a = b) (s : a ⤳ b) :
      Y.presheaf.stalkSpecializes s =
        eqToHom (congrArg (fun y => Y.presheaf.stalk y) h.symm) := by
    subst b
    exact Y.presheaf.stalkSpecializes_refl a
  unfold pull Scheme.Hom.functionFieldMap
  rw [transport _ _ (f.map_genericPoint_of_denseRange hd)]

variable {K : Type} [Field K] (f : K[X]) [IsDomain (Cover f)] [Fact (¬IsSquare (rmap f))]

local instance : Algebra (Cover f) (Cover (rmap f)) := (chartEmbedding f).toAlgebra
local instance : IsFractionRing (Cover f) (Cover (rmap f)) := chartIsFractionRing f

local instance affineAlg (A : Type) [CommRing A] [IsDomain A] :
    Algebra A (Spec (.of A)).functionField :=
  AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of A)

local instance affineFrac (A : Type) [CommRing A] [IsDomain A] :
    IsFractionRing A (Spec (.of A)).functionField :=
  functionField_isFractionRing_of_affine (CommRingCat.of A)

def affineFieldEquiv : (Spec (.of (Cover f))).functionField ≃+* Cover (rmap f) :=
  IsFractionRing.ringEquivOfRingEquiv (RingEquiv.refl (Cover f))

theorem affineFieldEquiv_apply (z : Cover f) :
    affineFieldEquiv f (algebraMap (Cover f) _ z) = chartEmbedding f z :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _

variable {C : Over (Spec (.of K))} [AlgebraicGeometry.IsIntegral C.left]
variable (j : SpecOver (R := K) (Cover f) ⟶ C) [IsOpenImmersion j.left]

local instance : AlgebraicGeometry.IsIntegral (SpecOver (R := K) (Cover f)).left :=
  inferInstanceAs (AlgebraicGeometry.IsIntegral (Spec (.of (Cover f))))

def chartFieldIso : C.left.functionField ≃+* Cover (rmap f) :=
  j.left.functionFieldRingEquivOfIsOpenImmersion.trans (affineFieldEquiv f)

theorem chartFieldIso_constants (a : K) :
    chartFieldIso f j (baseToFunctionField C.hom a) =
      chartEmbedding f (algebraMap K (Cover f) a) := by
  let d := j.left.denseRange_of_isOpenImmersion
  have h := DFunLike.congr_fun (functionFieldMap_comp_baseToFunctionField C.hom j.left d) a
  rw [j.w] at h
  change affineFieldEquiv f (j.left.functionFieldMap d (baseToFunctionField C.hom a)) = _
  change j.left.functionFieldMap d (baseToFunctionField C.hom a) =
    (baseToFunctionField (Spec.map (CommRingCat.ofHom (algebraMap K (Cover f))))) a at h
  rw [h, ←affineFieldEquiv_apply]
  congr 1
  change _ = _
  let : Nonempty (⊤ : (Spec (.of (Cover f))).Opens) := ⟨⟨genericPoint _,trivial⟩⟩
  let φ : K →+* Cover f := algebraMap K (Cover f)
  change (Spec (.of (Cover f))).germToFunctionField ⊤ ((Spec.map (CommRingCat.ofHom φ)).appTop
    ((Scheme.ΓSpecIso (.of K)).inv a)) = _
  rw [show (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of K)).inv a) =
      (Scheme.ΓSpecIso (.of (Cover f))).inv (φ a) from
    (congrArg (fun g : CommRingCat.of K ⟶ Γ(Spec (.of (Cover f)),⊤) => g a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm]
  rfl

theorem affineFieldEquiv_star (x : (Spec (.of (Cover f))).functionField) :
    let t := Spec.map (CommRingCat.ofHom (starRingEnd (Cover f)))
    let hd := Scheme.Hom.affineSpecMap_denseRange_of_injective _
      (show Function.Injective (starRingEnd (Cover f)) from star_injective)
    affineFieldEquiv f (t.functionFieldMap hd x) =
      ordinateConjugation (rmap f) (affineFieldEquiv f x) := by
  intro t hd
  have maps : (affineFieldEquiv f).toRingHom.comp (t.functionFieldMap hd) =
      (ordinateConjugation (rmap f)).toRingHom.comp (affineFieldEquiv f).toRingHom := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors (Cover f))
    apply RingHom.ext
    intro z
    change affineFieldEquiv f (t.functionFieldMap hd (algebraMap (Cover f) _ z)) =
      ordinateConjugation _ (affineFieldEquiv f (algebraMap (Cover f) _ z))
    rw [show t.functionFieldMap hd (algebraMap (Cover f) _ z) = algebraMap (Cover f) _ (star z) from
      Scheme.Hom.affineSpecMap_functionFieldMap_algebraMap (starRingEnd (Cover f)) hd z,
      affineFieldEquiv_apply,affineFieldEquiv_apply]
    exact chartEmbedding_star _ _
  exact DFunLike.congr_fun maps x

theorem chartFieldIso_action (e : C.left ≅ C.left)
    (he : j.left ≫ e.inv = Spec.map (CommRingCat.ofHom (starRingEnd (Cover f))) ≫ j.left)
    (x : C.left.functionField) :
    chartFieldIso f j ((equivOfIso e).symm x) =
      ordinateConjugation (rmap f) (chartFieldIso f j x) := by
  let t := Spec.map (CommRingCat.ofHom (starRingEnd (Cover f)))
  let ht : DenseRange t := Scheme.Hom.affineSpecMap_denseRange_of_injective _
      (show Function.Injective (starRingEnd (Cover f)) from star_injective)
  let hd := j.left.denseRange_of_isOpenImmersion
  let he' := e.inv.denseRange_of_isOpenImmersion
  have sq : (j.left.functionFieldMap hd).comp (e.inv.functionFieldMap he') =
       (t.functionFieldMap ht).comp (j.left.functionFieldMap hd) := by
    rw [EtaleFundamentalGroups.functionFieldMap_comp_of_dense,
      EtaleFundamentalGroups.functionFieldMap_comp_of_dense]
    congr 1
  have eq := DFunLike.congr_fun sq x
  change affineFieldEquiv f (j.left.functionFieldMap hd ((pull e.inv _).hom x)) = _
  rw [pull_eq_fieldMap _ he']
  change j.left.functionFieldMap hd (e.inv.functionFieldMap he' x) =
    t.functionFieldMap ht (j.left.functionFieldMap hd x) at eq
  rw [eq]
  exact affineFieldEquiv_star f _

end
end ZInQBlueprint.FibreDivisors
#print axioms ZInQBlueprint.FibreDivisors.pull_eq_fieldMap
#print axioms ZInQBlueprint.FibreDivisors.chartFieldIso_constants
#print axioms ZInQBlueprint.FibreDivisors.chartFieldIso_action

