import OpeningSections
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The first cohomology contributed by a pair of opens, expressed in ordinary sections. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
namespace ZInQBlueprint.BinaryCover.Cech
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type} [Category.{0} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type 0)] [HasSheafify J AddCommGrpCat.{0}]
  [HasExt.{0} (Sheaf J AddCommGrpCat.{0})]
  (S : J.MayerVietorisSquare) (F : Sheaf J AddCommGrpCat.{0})

/-- Difference of restrictions of ordinary sections to the overlap. -/
def sectionDifference : (F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) →+ F.obj.obj (op S.X₁) :=
  ((F.obj.map S.f₁₂.op).hom.comp (AddMonoidHom.fst _ _)) -
    ((F.obj.map S.f₁₃.op).hom.comp (AddMonoidHom.snd _ _))

/-- The connecting homomorphism, evaluated on an ordinary overlap section. -/
def boundarySection : F.obj.obj (op S.X₁) →+ F.H' 1 S.X₄ :=
  (S.δ F 0 1 rfl).hom.comp (openingSections F S.X₁).symm.toAddMonoidHom

private def sectionsPair : (F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) ≃+
    (↑(F.H' 0 S.X₂ ⊞ F.H' 0 S.X₃) : Type) :=
  (((openingSections F S.X₂).symm.prodCongr (openingSections F S.X₃).symm).trans
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm)

private theorem sectionDifference_eq (x : F.obj.obj (op S.X₂) × F.obj.obj (op S.X₃)) :
    sectionDifference S F x = openingSections F S.X₁ ((S.fromBiprod F 0) (sectionsPair S F x)) := by
  rcases x with ⟨u,v⟩
  change _ = openingSections F S.X₁ ((S.fromBiprod F 0)
    ((AddCommGrpCat.biprodIsoProd _ _).inv
      ⟨(openingSections F S.X₂).symm u, (openingSections F S.X₃).symm v⟩))
  rw [S.fromBiprod_biprodIsoProd_inv_apply, map_sub, openingSections_restrict,
    openingSections_restrict, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  rfl

/-- Exactness in actual sections, obtained from the Mayer–Vietoris sequence. -/
theorem sectionDifference_range : (sectionDifference S F).range = (boundarySection S F).ker := by
  have he : (S.fromBiprod F 0).hom.range = (S.δ F 0 1 rfl).hom.ker :=
    ((S.sequence_exact F 0 1 rfl).exact 1).ab_range_eq_ker
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    rw [sectionDifference_eq]
    change (S.δ F 0 1 rfl) ((openingSections F S.X₁).symm _) = 0
    rw [AddEquiv.symm_apply_apply]
    have hx : (S.fromBiprod F 0) (sectionsPair S F y) ∈ (S.fromBiprod F 0).hom.range :=
      ⟨_,rfl⟩
    rw [he] at hx
    exact hx
  · intro hx
    change (openingSections F S.X₁).symm x ∈ (S.δ F 0 1 rfl).hom.ker at hx
    rw [← he] at hx
    obtain ⟨y,hy⟩ := hx
    refine ⟨(sectionsPair S F).symm y, ?_⟩
    rw [sectionDifference_eq, (sectionsPair S F).apply_symm_apply]
    exact (congrArg (openingSections F S.X₁) hy).trans (AddEquiv.apply_symm_apply _ _)

/-- A cover by two opens always gives an injection from its ordinary Čech quotient. -/
def overlapToH1 : (F.obj.obj (op S.X₁) ⧸ (sectionDifference S F).range) →+ F.H' 1 S.X₄ :=
  (QuotientAddGroup.kerLift (boundarySection S F)).comp
    (QuotientAddGroup.quotientAddEquivOfEq (sectionDifference_range S F)).toAddMonoidHom

theorem overlapToH1_injective : Function.Injective (overlapToH1 S F) :=
  (QuotientAddGroup.kerLift_injective (boundarySection S F)).comp
    (QuotientAddGroup.quotientAddEquivOfEq (sectionDifference_range S F)).injective

/-- The image consists exactly of classes that vanish on both charts. -/
theorem overlapToH1_range : (overlapToH1 S F).range = (S.toBiprod F 1).hom.ker := by
  have he : (S.δ F 0 1 rfl).hom.range = (S.toBiprod F 1).hom.ker :=
    ((S.sequence_exact F 0 1 rfl).exact 2).ab_range_eq_ker
  rw [← he]
  ext y
  constructor
  · rintro ⟨q,rfl⟩
    obtain ⟨z,rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨(openingSections F S.X₁).symm z,rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨QuotientAddGroup.mk (openingSections F S.X₁ z),?_⟩
    exact congrArg (fun w => (S.δ F 0 1 rfl) w) ((openingSections F S.X₁).symm_apply_apply z)

/-- Vanishing of H¹ on the two members suffices to compute H¹ of the union. -/
def overlapEquivH1 (h₂ : Subsingleton (F.H' 1 S.X₂)) (h₃ : Subsingleton (F.H' 1 S.X₃)) :
    (F.obj.obj (op S.X₁) ⧸ (sectionDifference S F).range) ≃+ F.H' 1 S.X₄ :=
  AddEquiv.ofBijective _ ⟨overlapToH1_injective S F, by
    intro y
    have h : y ∈ (S.toBiprod F 1).hom.ker := by
      change S.toBiprod F 1 y = 0
      rw [S.toBiprod_apply]
      rw [show (F.cohomologyPresheaf 1).map S.f₂₄.op y = 0 from h₂.elim _ _,
        show (F.cohomologyPresheaf 1).map S.f₃₄.op y = 0 from h₃.elim _ _]
      exact map_zero _
    rw [← overlapToH1_range S F] at h
    exact h⟩

end
end ZInQBlueprint.BinaryCover.Cech
#print axioms ZInQBlueprint.BinaryCover.Cech.sectionDifference_range
#print axioms ZInQBlueprint.BinaryCover.Cech.overlapToH1_injective
#print axioms ZInQBlueprint.BinaryCover.Cech.overlapToH1_range
#print axioms ZInQBlueprint.BinaryCover.Cech.overlapEquivH1
