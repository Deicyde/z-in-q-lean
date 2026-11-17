import LabelledModuliField
import Nyll.JacobianVarieties.Picard.AlgebraicEquivalence.AlgebraicEquivalenceBaseChange

/-! The equivalence relation of Baba–Granath §2.1 and its behaviour under
change of coordinates. We keep the integral order action and remember only
its specified real generator in the equivalence relation. -/
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.QuaternionLift
open ThetaClass QuaternionMarking NormalDescent AbelianModel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev Gal := Qbar ≃ₐ[ℚ] Qbar
abbrev conjugateFunctor (σ : Gal) := (conjugation σ.toRingEquiv).mapCommGrp

/-- A geometric surface with the marked integral endomorphism and a line
representing the polarization. Only the geometric isomorphism classes of
items arising from a faithful maximal-order action will be used. -/
structure RealLabel where
  surface : GroupScheme Qbar
  line : surface.X.left.Modules
  generator : End surface

/-- Equivalence in the coarse moduli problem for R₃ (Baba–Granath p. 737). -/
def Equivalent (A B : RealLabel) : Prop :=
  ∃ f : A.surface ≅ B.surface,
    A.generator.asHom ≫ f.hom = f.hom ≫ B.generator.asHom ∧
    SameClass A.surface.X.hom A.line (pullModule (underlying f).hom B.line)

private def pullComp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (L : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj L) ≅
      (Scheme.Modules.pullback (f ≫ g)).obj L := (Scheme.Modules.pullbackComp f g).app L

theorem equiv_refl (A : RealLabel) : Equivalent A A := by
  refine ⟨Iso.refl _,by simp,?_⟩
  exact (SameClass.refl _ _).congr (Iso.refl _) ((Scheme.Modules.pullbackId _).app A.line).symm

theorem equiv_symm {A B : RealLabel} (h : Equivalent A B) : Equivalent B A := by
  obtain ⟨f,comm,pol⟩ := h
  refine ⟨f.symm,?_,?_⟩
  · apply (cancel_epi f.hom).mp
    simp only [Iso.hom_inv_id_assoc,Iso.symm_hom]
    rw [← Category.assoc,← comm,Category.assoc,f.hom_inv_id,Category.comp_id]
  · let v := underlying f
    have e := pol.symm.pull v.inv.left v.inv.w
    have idcomp : v.inv.left ≫ v.hom.left = 𝟙 B.surface.X.left :=
      congrArg (fun a : B.surface.X ⟶ B.surface.X => a.left) v.inv_hom_id
    let iso : pullModule v.inv (pullModule v.hom B.line) ≅ B.line :=
      pullComp v.inv.left v.hom.left B.line ≪≫
        (Scheme.Modules.pullbackCongr idcomp).app B.line ≪≫
        (Scheme.Modules.pullbackId _).app B.line
    exact e.congr iso (Iso.refl _)

theorem equiv_trans {A B C : RealLabel} (h : Equivalent A B) (h' : Equivalent B C) :
    Equivalent A C := by
  obtain ⟨f,comm,pol⟩ := h
  obtain ⟨g,comm',pol'⟩ := h'
  refine ⟨f ≪≫ g,?_,?_⟩
  · simp only [Iso.trans_hom]
    rw [← Category.assoc,comm,Category.assoc,comm',Category.assoc]
  · let v := underlying f
    let w := underlying g
    exact pol.trans ((pol'.pull v.hom.left v.hom.w).congr (Iso.refl _)
      (pullComp v.hom.left w.hom.left C.line))

def labelSetoid : Setoid RealLabel := ⟨Equivalent,equiv_refl,equiv_symm,equiv_trans⟩
abbrev ModuliClass := Quotient labelSetoid
def moduliClass (A : RealLabel) : ModuliClass := Quotient.mk labelSetoid A

theorem class_eq {A B : RealLabel} : moduliClass A = moduliClass B ↔ Equivalent A B :=
  Quotient.eq

def conjugateLabel (σ : Gal) (A : RealLabel) : RealLabel where
  surface := (conjugateFunctor σ).obj A.surface
  line := (Scheme.Modules.pullback (projection A.surface σ)).obj A.line
  generator := End.of ((conjugateFunctor σ).map A.generator.asHom)

/-- Algebraic equivalence survives semilinear field conjugation. -/
theorem conjugateClass {A : GroupScheme Qbar} {L M : A.X.left.Modules}
    (h : SameClass A.X.hom L M) (σ : Gal) :
    SameClass ((conjugateFunctor σ).obj A).X.hom
      ((Scheme.Modules.pullback (projection A σ)).obj L)
      ((Scheme.Modules.pullback (projection A σ)).obj M) := by
  obtain ⟨N,hi,hz,⟨iso⟩⟩ := h
  let : Algebra Qbar Qbar := σ.toRingHom.toAlgebra
  have alg : algebraMap Qbar Qbar = σ.toRingHom := rfl
  have h0 := RelPicard.IsAlgEquivZero.baseChange Qbar A.X.hom hz
  rw [alg] at h0
  let π := projection A σ
  exact ⟨_,hi.pullback π,h0,⟨(Scheme.Modules.pullbackTensorObjIso π L N).symm ≪≫
    (Scheme.Modules.pullback π).mapIso iso⟩⟩

theorem equiv_conjugate {A B : RealLabel} (h : Equivalent A B) (σ : Gal) :
    Equivalent (conjugateLabel σ A) (conjugateLabel σ B) := by
  obtain ⟨f,comm,pol⟩ := h
  let F := conjugateFunctor σ
  let φ := F.mapIso f
  refine ⟨φ,?_,?_⟩
  · change F.map A.generator.asHom ≫ F.map f.hom = F.map f.hom ≫ F.map B.generator.asHom
    rw [← F.map_comp,comm,F.map_comp]
  · have p := conjugateClass pol σ
    let v := underlying f
    let w := underlying φ
    let iso := pullComp (projection A.surface σ) v.hom.left B.line ≪≫
      (Scheme.Modules.pullbackCongr (pull_fst σ f.hom).symm).app B.line ≪≫
      (pullComp w.hom.left (projection B.surface σ) B.line).symm
    exact p.congr (Iso.refl _) iso

/-- The action on moduli classes is independent of the representative. -/
def conjugateModuli (σ : Gal) (m : ModuliClass) : ModuliClass :=
  Quotient.map (conjugateLabel σ) (fun _ _ e => equiv_conjugate e σ) m

def markedObject (A : GroupScheme Qbar) (L : A.X.left.Modules)
    (a : LevelThree.O →+* End A) : RealLabel := ⟨A,L,a sqrtThree⟩

theorem labelled_iff_fixed_class (A : GroupScheme Qbar) (L : A.X.left.Modules) (z : Qbar) :
    LabelledModuli A L z ↔
    ∃ a : LevelThree.O →+* End A, Function.Injective a ∧
      ∀ σ : Gal, σ z = z →
        moduliClass (markedObject A L a) = conjugateModuli σ (moduliClass (markedObject A L a)) := by
  constructor
  · rintro ⟨a,ha,f⟩
    exact ⟨a,ha,fun σ hz => class_eq.mpr (f σ hz)⟩
  · rintro ⟨a,ha,f⟩
    exact ⟨a,ha,fun σ hz => class_eq.mp (f σ hz)⟩

end
end ZInQBlueprint.QuaternionLift
#print axioms ZInQBlueprint.QuaternionLift.class_eq
#print axioms ZInQBlueprint.QuaternionLift.conjugateClass
#print axioms ZInQBlueprint.QuaternionLift.equiv_conjugate
#print axioms ZInQBlueprint.QuaternionLift.labelled_iff_fixed_class
