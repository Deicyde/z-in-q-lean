import MarkingTransport
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Data.ZMod.Basic

/-! Integral endomorphism actions and full level-three structures on a polarized object. -/

open CategoryTheory
namespace ZInQBlueprint.PolarizedMarkings
universe v u w
abbrev k := ZMod 3

variable {O V : Type*} [Ring O] [AddCommGroup V] [Module k V]
variable {C : Type u} [Groupoid.{v} C] (E : C ⥤ RingCat.{w}) (T : C ⥤ ModuleCat.{w} k)

/-- The reference order with its involution, action on the level lattice and alternating form.
The application takes V = O/3O with its left regular action. -/
structure Reference (O V : Type*) [Ring O] [AddCommGroup V] [Module k V] where
  adjoint : O → O
  action : O →+* Module.End k V
  form : V → V → k

/-- Conjugation on endomorphisms and transport on torsion, together with the Rosati
involution and Weil pairing in a chosen basis of the group of cube roots of unity.
A change of basis is absorbed by the multiplier. -/
structure Realization where
  adjoint (X : C) : E.obj X → E.obj X
  action (X : C) : E.obj X →+* Module.End k (T.obj X)
  form (X : C) : T.obj X → T.obj X → k
  adjoint_map {X Y : C} (f : X ⟶ Y) (d : E.obj X) :
    adjoint Y (E.map f d) = E.map f (adjoint X d)
  action_map {X Y : C} (f : X ⟶ Y) (d : E.obj X) (t : T.obj X) :
    action Y (E.map f d) (T.map f t) = T.map f (action X d t)
  form_map {X Y : C} (f : X ⟶ Y) : ∃ m : kˣ, ∀ x y : T.obj X,
    form Y (T.map f x) (T.map f y) = (m : k) * form X x y

variable {E T} (R : Reference O V) (P : Realization E T)

/-- A marking consists of the full order embedding and a linear isomorphism.
The multiplier is a property. Counting a chosen multiplier separately would
depend on a trivialization of the group of cube roots of unity. -/
@[ext]
structure Marking (X : C) where
  embedding : O →+* E.obj X
  faithful : Function.Injective embedding
  rosati (o : O) : P.adjoint X (embedding o) = embedding (R.adjoint o)
  level : V ≃ₗ[k] T.obj X
  linearity (o : O) (x : V) : P.action X (embedding o) (level x) = level (R.action o x)
  weil : ∃ m : kˣ, ∀ x y : V, P.form X (level x) (level y) = (m : k) * R.form x y

variable {R P}

noncomputable def transport {X Y : C} (f : X ⟶ Y) (m : Marking R P X) : Marking R P Y where
  embedding := (E.map f).hom.comp m.embedding
  faithful := (by
    intro x y eqn
    apply m.faithful
    have t := congrArg (fun d => E.map (Groupoid.inv f) d) eqn
    change E.map (Groupoid.inv f) (E.map f _) = E.map (Groupoid.inv f) (E.map f _) at t
    simpa only [← ConcreteCategory.comp_apply, ← E.map_comp, Groupoid.comp_inv, E.map_id, ConcreteCategory.id_apply] using t)
  rosati o := (P.adjoint_map f _).trans (congrArg (E.map f) (m.rosati o))
  level := m.level.trans ((T.mapIso (asIso f)).toLinearEquiv)
  linearity o x := (P.action_map f _ _).trans (congrArg (T.map f) (m.linearity o x))
  weil := by
    obtain ⟨a,ha⟩ := P.form_map f
    obtain ⟨b,hb⟩ := m.weil
    refine ⟨a*b, fun x y => ?_⟩
    change P.form _ (T.map f (m.level x)) (T.map f (m.level y)) = _ 
    rw [ha,hb, Units.val_mul, mul_assoc]

/-- Transport along the actual morphisms in C defines a functor of full markings. -/
noncomputable def functor (R : Reference O V) (P : Realization E T) : C ⥤ Type _ where
  obj := Marking R P
  map f := ↾(fun m => transport (R:=R) (P:=P) f m)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro m
    apply Marking.ext
    · ext o
      change E.map (𝟙 X) _ = _
      simp
    · ext x
      change T.map (𝟙 X) _ = _
      simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro m
    apply Marking.ext
    · ext o
      change E.map (f ≫ g) _ = E.map g (E.map f _)
      simp
    · ext x
      change T.map (f ≫ g) _ = T.map g (T.map f _)
      simp

/-- The coarse fibre of this particular moduli problem, with both Weil multipliers. -/
noncomputable def fibreEquiv (A : C) :
    Quotient (MarkingTransport.orbit (functor R P) A) ≃ MarkingTransport.fibre (functor R P) A :=
  MarkingTransport.orbitEquivFibre _ A

end ZInQBlueprint.PolarizedMarkings

#print axioms ZInQBlueprint.PolarizedMarkings.transport
#print axioms ZInQBlueprint.PolarizedMarkings.functor
#print axioms ZInQBlueprint.PolarizedMarkings.fibreEquiv
