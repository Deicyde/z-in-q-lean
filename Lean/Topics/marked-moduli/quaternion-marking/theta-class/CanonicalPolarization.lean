import PrintedPolarization
import ThetaGroupSupport

/-! From a polarization on the Jacobian to the translates of its Abel curve.
An algebraically trivial twist is a translate, and the one-dimensional
linear system then identifies the pulled-back divisors. -/
open CategoryTheory AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.MonObj ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ThetaClass
open QuaternionMarking GeometricMarking AbelianModel NormalDescent
noncomputable section
variable {u : ℚ} {hu : u ∉ ZInQ.contactSet} {P : GroupScheme Qbar}
local notation "J" => geometricJacobian hu

theorem preserves_of_polarization (D : DivisorData hu)
    (L : (geometricJacobian hu).X.left.Modules) (hL : L.IsInvertible)
    (s : 𝟙_ (geometricJacobian hu).X.left.Modules ⟶ L) (hs : s ≠ 0)
    (zeros : ∀ p : sections J, Scheme.Modules.pullbackSection p.toMul.left s = 0 ↔ p ∈ Set.range D.abel)
    (one : ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom L = 1) (principal : PrincipalTranslations (A:=J) L)
    (a : J ≅ J) (h : SameClass (geometricJacobian hu).X.hom L (pullModule (underlying a).hom L)) :
    preservesTheta D a := by
  obtain ⟨t,⟨v⟩⟩ := translate_of_sameClass principal h
  rw [preservesTheta,abel_translates]
  apply preserves_of_preimages _ a t
  intro p
  exact (zeros _).symm.trans ((ThetaLinearSystem.group_vanishes_iff L hL s hs one a t v p).trans (zeros _))

/-- The labelled comparison preserves every translate of the Abel image as
a consequence of its equality of polarization classes. -/
theorem printed_of_class (D : DivisorData hu)
    (L : (geometricJacobian hu).X.left.Modules) (hL : L.IsInvertible)
    (s : 𝟙_ (geometricJacobian hu).X.left.Modules ⟶ L) (hs : s ≠ 0)
    (zeros : ∀ p : sections J, Scheme.Modules.pullbackSection p.toMul.left s = 0 ↔ p ∈ Set.range D.abel)
    (one : ThetaLinearSystem.rankH0 (geometricJacobian hu).X.hom L = 1) (principal : PrincipalTranslations (A:=J) L)
    (e : J ≅ P) (bg : PrintedClassMarking e L) : PrintedMarking D e := by
  obtain ⟨act,hact,marked⟩ := bg
  refine ⟨act,hact,?_⟩
  intro square σ
  obtain ⟨φ,gen,pull⟩ := marked square σ
  exact ⟨φ,gen,comparison_of_corrected D e σ φ
    (preserves_of_polarization D L hL s hs zeros one principal _ (correction_sameClass e σ φ L pull))⟩

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.preserves_of_polarization
#print axioms ZInQBlueprint.ThetaClass.printed_of_class
