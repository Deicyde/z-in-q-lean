import DiscriminantSixUnits
import SixShimuraEndpoint

/-! A comparison of polarized abelian surfaces carries integral polarized
automorphisms by conjugation before any choice of a Galois isomorphism. -/
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.RosatiSigns
open LevelThree QuaternionMarking ThetaClass QuaternionLift NormalDescent AbelianModel
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An isomorphism carries the specified two Néron–Severi classes into one another. -/
abbrev Compatible {A B : GroupScheme Qbar} (f : A ≅ B)
    (L : A.X.left.Modules) (M : B.X.left.Modules) :=
  SameClass A.X.hom L (pullModule (underlying f).hom M)

theorem compatible_comp {A B C : GroupScheme Qbar} {f : A ≅ B} {g : B ≅ C}
    {L : A.X.left.Modules} {M : B.X.left.Modules} {N : C.X.left.Modules}
    (ef : Compatible f L M) (eg : Compatible g M N) : Compatible (f ≪≫ g) L N := by
  let v := underlying f
  let w := underlying g
  exact ef.trans ((eg.pull v.hom.left v.hom.w).congr (Iso.refl _)
    ((Scheme.Modules.pullbackComp v.hom.left w.hom.left).app N))

theorem compatible_symm {A B : GroupScheme Qbar} {f : A ≅ B}
    {L : A.X.left.Modules} {M : B.X.left.Modules} (ef : Compatible f L M) :
    Compatible f.symm M L := by
  let v := underlying f
  have e := ef.symm.pull v.inv.left v.inv.w
  have eq : v.inv.left ≫ v.hom.left = 𝟙 B.X.left :=
    congrArg (fun a : B.X ⟶ B.X => a.left) v.inv_hom_id
  let iso : pullModule v.inv (pullModule v.hom M) ≅ M :=
    (Scheme.Modules.pullbackComp v.inv.left v.hom.left).app M ≪≫
    (Scheme.Modules.pullbackCongr eq).app M ≪≫ (Scheme.Modules.pullbackId _).app M
  exact e.congr iso (Iso.refl _)

/-- On the geometric Shimura representative Baba–Granath's Riemann form
identifies the Rosati involution with conjugation by the specified mu. We
only use the implication for a pullback preserving its NS class. -/
def IsRosatiPresentation {A : GroupScheme Qbar} (L : A.X.left.Modules)
    (order : O ≃+* End A) : Prop :=
  ∀ a : A ≅ A, Compatible a L L →
    let x := embed (order.symm (End.of a.hom))
    dagger x * x = 1

theorem signed_automorphism {A : GroupScheme Qbar} {L : A.X.left.Modules}
    {order : O ≃+* End A} (pres : IsRosatiPresentation L order) (a : A ≅ A)
    (polar : Compatible a L L) : End.of a.hom = 1 ∨ End.of a.hom = -1 := by
  have cases := (polarized_order_iff _).mp (pres a polar)
  rcases cases with h|h
  · left; simpa using congrArg order h
  · right; simpa using congrArg order h

/-- The comparison can occur before taking any Galois conjugate, and
the two endomorphism rings are carried by the actual group isomorphism. -/
theorem signed_of_comparison {A B : GroupScheme Qbar} {L : A.X.left.Modules}
    {M : B.X.left.Modules} {order : O ≃+* End A} (pres : IsRosatiPresentation L order)
    (f : A ≅ B) (polar : Compatible f L M) (a : B ≅ B) (ha : Compatible a M M) :
    End.of a.hom = 1 ∨ End.of a.hom = -1 := by
  let b := f ≪≫ a ≪≫ f.symm
  have bp : Compatible b L L := compatible_comp polar (compatible_comp ha (compatible_symm polar))
  have h := signed_automorphism pres b bp
  have eq : endRingEquiv f (End.of b.hom) = End.of a.hom := by
    apply End.homEquiv.injective
    change f.inv ≫ (f.hom ≫ a.hom ≫ f.inv) ≫ f.hom = a.hom
    simp
  rcases h with h|h
  · left; rw [← eq,h,map_one]
  · right; rw [← eq,h]
    exact (endRingEquiv f).toRingHom.map_neg (1 : End A) |>.trans (congrArg Neg.neg (endRingEquiv f).map_one)

end
end ZInQBlueprint.RosatiSigns
#print axioms ZInQBlueprint.RosatiSigns.compatible_comp
#print axioms ZInQBlueprint.RosatiSigns.compatible_symm
#print axioms ZInQBlueprint.RosatiSigns.signed_automorphism
#print axioms ZInQBlueprint.RosatiSigns.signed_of_comparison
