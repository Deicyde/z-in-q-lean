import SixUnpolarizedQM
import Mathlib.Analysis.Complex.Basic

/-! Full faithfulness is used only for homomorphisms between abelian varieties.
An isomorphism and its two inverse equations then descend, as does every
endomorphism in an integral order. -/
open CategoryTheory AlgebraicGeometry
open scoped ZInQBlueprint.NormalDescent
namespace ZInQBlueprint.ShimuraAtlas
open AbelianModel NormalDescent
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 160000
set_option maxHeartbeats 1400000

/-- Milne, Abelian Varieties, Corollary 20.4(b), together with faithful
descent of morphisms along a field extension. -/
def HomBaseChange (ι : Qbar →+* ℂ) : Prop :=
  ∀ (A B : GroupScheme Qbar), IsAbelianScheme A → IsAbelianScheme B →
    Function.Bijective ((baseChange ι).map : (A ⟶ B) → _)

def descendIso {ι : Qbar →+* ℂ} (hom : HomBaseChange ι) {A B : GroupScheme Qbar}
    (ab : IsAbelianScheme A) (bb : IsAbelianScheme B)
    (e : (baseChange ι).obj A ≅ (baseChange ι).obj B) : A ≅ B := by
  let F := baseChange ι
  let f := ((hom A B ab bb).2 e.hom).choose
  let g := ((hom B A bb ab).2 e.inv).choose
  have hf : F.map f = e.hom := ((hom A B ab bb).2 e.hom).choose_spec
  have hg : F.map g = e.inv := ((hom B A bb ab).2 e.inv).choose_spec
  exact ⟨f,g,(hom A A ab ab).1 (by rw [F.map_comp,F.map_id,hf,hg,e.hom_inv_id]),
    (hom B B bb bb).1 (by rw [F.map_comp,F.map_id,hg,hf,e.inv_hom_id])⟩

def endBaseEquiv {ι : Qbar →+* ℂ} (hom : HomBaseChange ι) (A : GroupScheme Qbar)
    (ab : IsAbelianScheme A) : End A ≃+* End ((baseChange ι).obj A) := by
  let f : End A →+* End ((baseChange ι).obj A) := changeEndRing (Over.pullback (Spec.map (CommRingCat.ofHom ι))) A
  refine RingEquiv.ofBijective f ?_
  constructor
  · intro x y h
    exact End.homEquiv.injective ((hom A A ab ab).1 (congrArg End.asHom h))
  · intro y
    obtain ⟨x,hx⟩ := (hom A A ab ab).2 y.asHom
    exact ⟨End.of x,End.homEquiv.injective hx⟩

/-- This chooses one integral order on A over Qbar. Extending it recovers
the prescribed action, generator by generator. -/
def descendedOrder {ι : Qbar →+* ℂ} (hom : HomBaseChange ι) (A : GroupScheme Qbar)
    (ab : IsAbelianScheme A) (o : LevelThree.O ≃+* End ((baseChange ι).obj A)) :
    LevelThree.O ≃+* End A := o.trans (endBaseEquiv hom A ab).symm

theorem order_extends {ι : Qbar →+* ℂ} (hom : HomBaseChange ι) (A : GroupScheme Qbar)
    (ab : IsAbelianScheme A) (o : LevelThree.O ≃+* End ((baseChange ι).obj A)) (r : LevelThree.O) :
    (baseChange ι).map ((descendedOrder hom A ab o r).asHom) = (o r).asHom := by
  exact congrArg End.asHom ((endBaseEquiv hom A ab).apply_symm_apply (o r))

end
end ZInQBlueprint.ShimuraAtlas
#print axioms ZInQBlueprint.ShimuraAtlas.descendIso
#print axioms ZInQBlueprint.ShimuraAtlas.endBaseEquiv
#print axioms ZInQBlueprint.ShimuraAtlas.order_extends
