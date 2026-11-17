import RealOrderInQuaternion
import CanonicalJacobianPoints
import Mathlib.CategoryTheory.Conj

/-! Transport of integral endomorphisms and their marked Galois intertwiners
through a specified isomorphism of commutative group schemes. -/
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace ZInQBlueprint.QuaternionMarking
open NormalDescent AbelianModel
open scoped NormalDescent
noncomputable section

def endRingEquiv {C : Type*} [Category* C] [Preadditive C] {A B : C} (e : A ≅ B) :
    End A ≃+* End B where
  __ := e.conj
  map_add' f g := by
    apply End.homEquiv.injective
    change e.inv ≫ (f.asHom + g.asHom) ≫ e.hom = (e.inv ≫ f.asHom ≫ e.hom) + (e.inv ≫ g.asHom ≫ e.hom)
    rw [Preadditive.add_comp,Preadditive.comp_add]

variable {k : Type} [Field k] {P J : GroupScheme k}

def restrictedAction (e : J ≅ P) (ι : LevelThree.O →+* End P) : realOrder →+* End J :=
  (endRingEquiv e.symm).toRingHom.comp (ι.comp realInclusion)

theorem restricted_faithful (e : J ≅ P) {ι : LevelThree.O →+* End P} (hι : Function.Injective ι) :
    Function.Injective (restrictedAction e ι) :=
  (endRingEquiv e.symm).injective.comp (hι.comp inclusion_injective)

abbrev conjugation (σ : k ≃+* k) := Over.pullback (Spec.map (CommRingCat.ofHom σ.toRingHom))

/-- A marked isomorphism on the printed surface induces a marked isomorphism
on the rational model after scalar extension. All arrows belong to over-categories. -/
theorem transport_intertwiner (e : J ≅ P) (ι : LevelThree.O →+* End P) (σ : k ≃+* k)
    (φ : P ≅ (conjugation σ).mapCommGrp.obj P)
    (hφ : (ι sqrtThree).asHom ≫ φ.hom = φ.hom ≫ (conjugation σ).mapCommGrp.map (ι sqrtThree).asHom) :
    let ψ := e ≪≫ φ ≪≫ (conjugation σ).mapCommGrp.mapIso e.symm
    let E := (restrictedAction e ι QuadraticAlgebra.omega).asHom
    E ≫ ψ.hom = ψ.hom ≫ (conjugation σ).mapCommGrp.map E := by
  let F := (conjugation σ).mapCommGrp
  change (e.hom ≫ (ι sqrtThree).asHom ≫ e.inv) ≫ e.hom ≫ φ.hom ≫ F.map e.inv =
    (e.hom ≫ φ.hom ≫ F.map e.inv) ≫ F.map (e.hom ≫ (ι sqrtThree).asHom ≫ e.inv)
  have cancel : F.map e.inv ≫ F.map e.hom = 𝟙 _ := by rw [← F.map_comp,e.inv_hom_id,F.map_id]
  have cancel' {A} (t : F.obj P ⟶ A) : F.map e.inv ≫ F.map e.hom ≫ t = t := by
    rw [← Category.assoc,cancel,Category.id_comp]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, cancel']
  rw [← Category.assoc (ι sqrtThree).asHom, hφ, Category.assoc]

end
end ZInQBlueprint.QuaternionMarking
#print axioms ZInQBlueprint.QuaternionMarking.endRingEquiv
#print axioms ZInQBlueprint.QuaternionMarking.restricted_faithful
#print axioms ZInQBlueprint.QuaternionMarking.transport_intertwiner
