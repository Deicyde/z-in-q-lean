import SixLabelledClass

/-! Changing the geometric ppav representative transports the faithful
maximal-order embedding by conjugation. Only the class of the chosen
polarization has to agree under this isomorphism. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.QuaternionLift
open ThetaClass QuaternionMarking NormalDescent AbelianModel
noncomputable section
set_option backward.isDefEq.respectTransparency false

def carryAction {A B : GroupScheme Qbar} (f : A ≅ B) (act : LevelThree.O →+* End A) :
    LevelThree.O →+* End B := (endRingEquiv f).toRingHom.comp act

theorem carry_faithful {A B : GroupScheme Qbar} (f : A ≅ B) {act : LevelThree.O →+* End A}
    (faithful : Function.Injective act) : Function.Injective (carryAction f act) :=
  (endRingEquiv f).injective.comp faithful

theorem class_transport {A B : GroupScheme Qbar} {L : A.X.left.Modules} {M : B.X.left.Modules}
    (f : A ≅ B) (polar : SameClass A.X.hom L (pullModule (underlying f).hom M))
    (act : LevelThree.O →+* End A) :
    moduliClass (markedObject A L act) = moduliClass (markedObject B M (carryAction f act)) := by
  apply class_eq.mpr
  refine ⟨f,?_,polar⟩
  change (act sqrtThree).asHom ≫ f.hom = f.hom ≫ f.inv ≫ (act sqrtThree).asHom ≫ f.hom
  rw [Iso.hom_inv_id_assoc]

/-- The labelled field-of-moduli condition is intrinsic to a polarized
geometric isomorphism class. The proof transports the same integral action
before imposing any condition on Galois elements. -/
theorem labelled_transport {A B : GroupScheme Qbar} {L : A.X.left.Modules} {M : B.X.left.Modules}
    (f : A ≅ B) (polar : SameClass A.X.hom L (pullModule (underlying f).hom M)) (z : Qbar) :
    LabelledModuli A L z → LabelledModuli B M z := by
  rw [labelled_iff_fixed_class,labelled_iff_fixed_class]
  rintro ⟨act,faithful,fixed⟩
  refine ⟨carryAction f act,carry_faithful f faithful,?_⟩
  intro σ h
  rw [← class_transport f polar act]
  exact fixed σ h

/-- The standard comparison between two printed models is formed through
the signed model, so its two transported theta classes agree. -/
theorem between_models {J A B : GroupScheme Qbar} (f : J ≅ A) (g : J ≅ B)
    (L : J.X.left.Modules) :
    SameClass A.X.hom (pullModule (underlying f).inv L)
      (pullModule (underlying (f.symm ≪≫ g)).hom (pullModule (underlying g).inv L)) := by
  let F := underlying f
  let G := underlying g
  have t := (sameClass_transport G L).pull F.inv.left F.inv.w
  exact t.congr (Iso.refl _) ((Scheme.Modules.pullbackComp F.inv.left G.hom.left).app _)

/-- A Galois hypothesis depending on a radical depends only on its square. -/
theorem labelled_root_iff (A : GroupScheme Qbar) (L : A.X.left.Modules) {z w : Qbar}
    (h : z^2 = w^2) : LabelledModuli A L z ↔ LabelledModuli A L w := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with e|e
  · rw [e]
  · rw [e]
    simp [LabelledModuli]

end
end ZInQBlueprint.QuaternionLift
#print axioms ZInQBlueprint.QuaternionLift.carry_faithful
#print axioms ZInQBlueprint.QuaternionLift.class_transport
#print axioms ZInQBlueprint.QuaternionLift.labelled_transport
#print axioms ZInQBlueprint.QuaternionLift.between_models
#print axioms ZInQBlueprint.QuaternionLift.labelled_root_iff
