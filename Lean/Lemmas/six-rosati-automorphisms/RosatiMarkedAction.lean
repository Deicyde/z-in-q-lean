import RosatiTransport

/-! The correction to a labelled Galois isomorphism is a polarized
automorphism. Its order coordinates are scalar, so it cancels before
descending the real quadratic generator. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.RosatiSigns
open LevelThree QuaternionMarking ThetaClass QuaternionLift NormalDescent AbelianModel
open GeometricMarking CanonicalTheta JacobianHeight
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem commute_sign {A : GroupScheme Qbar} (a : A ≅ A) (x : End A)
    (h : End.of a.hom = 1 ∨ End.of a.hom = -1) : a.hom ≫ x.asHom = x.asHom ≫ a.hom := by
  have eq : x * End.of a.hom = End.of a.hom * x := by
    rcases h with he|he <;> rw [he] <;> simp
  exact congrArg End.asHom eq

/-- The descent needs only scalarity of automorphisms of the specified
polarized group scheme. A correction by an isomorphism cancels on the left,
so the labelled real endomorphism itself commutes with Galois. -/
theorem marked_of_class_signs {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    {P : GroupScheme Qbar} (e : geometricJacobian hu ≅ P)
    (L : (geometricJacobian hu).X.left.Modules) (bg : PrintedClassMarking e L)
    (aut : ∀ a : geometricJacobian hu ≅ geometricJacobian hu,
      Compatible a L L → End.of a.hom = 1 ∨ End.of a.hom = -1) :
    Nonempty (MarkedAction u (SixJacobian.jacobian hu)) := by
  obtain ⟨act,hact,comp⟩ := bg
  let i := restrictedAction e act
  refine ⟨⟨i, restricted_faithful e hact, fun g => g = 𝟙 _,?_,?_⟩⟩
  · intro square
    dsimp only
    intro σ
    obtain ⟨φ,inter,pol⟩ := comp square σ
    let a := correctionIso e σ φ
    let E := (i QuadraticAlgebra.omega).asHom.hom.hom.hom.left
    let s := deck (SixJacobian.jacobian hu).X.hom σ
    have hp : Compatible a L L := correction_sameClass e σ φ L pol
    have c := commute_sign a (i QuadraticAlgebra.omega) (aut a hp)
    have commute : groupMap a ≫ E = E ≫ groupMap a :=
      congrArg (fun f : geometricJacobian hu ⟶ geometricJacobian hu => f.hom.hom.hom.left) c
    have h : (groupMap a ≫ s) ≫ E = E ≫ groupMap a ≫ s := corrected_generator e act σ φ inter
    have tri : groupMap a ≫ s ≫ E = groupMap a ≫ E ≫ s := by
      calc
        _ = (groupMap a ≫ s) ≫ E := (Category.assoc ..).symm
        _ = E ≫ groupMap a ≫ s := h
        _ = groupMap a ≫ E ≫ s := by rw [← Category.assoc, ← commute, Category.assoc]
    let ai := (Over.forget _).mapIso (underlying a)
    have cancels : s ≫ E = E ≫ s := (cancel_epi ai.hom).mp tri
    refine ⟨𝟙 _,rfl,?_⟩
    change (s ≫ 𝟙 _) ≫ E = E ≫ s ≫ 𝟙 _
    simpa only [Category.comp_id] using cancels
  · intro _ g hg
    exact Or.inl hg

/-- This single extra clause in the printed polarized comparison records
the full non-CM order and the formula for its Rosati involution on the
same Shimura representative. All NS transport is performed below. -/
structure RosatiRealization (U : ShimuraClassMap) (p : ConicPoint) (P : GroupScheme Qbar)
    (B : P.X.left.Modules) extends PolarizedRealization U p P B where
  full : Function.Surjective order
  rosati : IsRosatiPresentation theta (RingEquiv.ofBijective order ⟨faithful,full⟩)

def RosatiPrintedComparison (U : ShimuraClassMap) : Prop :=
  ∀ (u : ℚ) (hu : u ∉ ZInQ.contactSet), OutsideCM (SixContact.J u) →
    ∃ (p : ConicPoint), FibrePoint u p ∧
    ∃ (d : Qbar) (hd : d^2 = 6) (v : Qbar) (hv : v^2 = PrintedModel.factor u d),
      Nonempty (RosatiRealization U p (PrintedModel.jacobian hu hd)
        (printedBundle (PrintedModel.jacobianIso hu hd v hv) (signedThetaLine hu)))

theorem printed_of_rosati {U : ShimuraClassMap} (models : RosatiPrintedComparison U) :
    PrintedComparison U := by
  intro u hu off
  obtain ⟨p,hp,d,hd,v,hv,⟨m⟩⟩ := models u hu off
  exact ⟨p,hp,d,hd,v,hv,⟨m.toPolarizedRealization⟩⟩

theorem printedField_of_rosati (U : ShimuraClassMap) (models : RosatiPrintedComparison U)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) : PrintedField hu :=
  printedField_of_shimura U (printed_of_rosati models) hu

/-- The new marking route on the signed determinant. Its only separate
polarization property is rationality of the NS class. -/
theorem marked_of_shimura_rational (U : ShimuraClassMap) (models : RosatiPrintedComparison U)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet)
    (rat : RationalThetaClass (hu:=hu) (signedThetaLine hu)) :
    Nonempty (MarkedAction u (SixJacobian.jacobian hu)) := by
  obtain ⟨p,hp,d,hd,v,hv,⟨m⟩⟩ := models u hu (fun _ ha => avoids_cm_table hu ha)
  let e := PrintedModel.jacobianIso hu hd v hv
  let L := signedThetaLine hu
  have polar : Compatible e.symm (printedBundle e L) L := SameClass.refl _ _
  have compat : Compatible (m.comparison ≪≫ e.symm) m.theta L := compatible_comp m.polarized polar
  have aut := signed_of_comparison m.rosati (m.comparison ≪≫ e.symm) compat
  have field := labelled_of_realization U p m.toPolarizedRealization
  obtain ⟨_,square,_⟩ := marked_quotient_coordinate hu hp.y_square hp.z_square
  exact marked_of_class_signs hu e L (classMarking_of_labelled_field e L rat _ square field) aut

end
end ZInQBlueprint.RosatiSigns
#print axioms ZInQBlueprint.RosatiSigns.marked_of_class_signs
#print axioms ZInQBlueprint.RosatiSigns.printed_of_rosati
#print axioms ZInQBlueprint.RosatiSigns.printedField_of_rosati
#print axioms ZInQBlueprint.RosatiSigns.marked_of_shimura_rational
