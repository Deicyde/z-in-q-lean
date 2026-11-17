import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.IsomorphismClasses

/-! The fibre of the forgetful map on isomorphism classes of marked objects. -/

open CategoryTheory
namespace ZInQBlueprint.MarkingTransport

universe w v u
variable {C : Type u} [Category.{v} C] (M : C ⥤ Type w)

abbrev Classes (D : Type*) [Category D] := Quotient (isIsomorphicSetoid D)

def classOf {D : Type*} [Category D] (X : D) : Classes D := Quotient.mk _ X

/-- Apply a functor to isomorphism classes. -/
def onClasses {D E : Type*} [Category D] [Category E] (F : D ⥤ E) :
    Classes D → Classes E :=
  Quotient.map F.obj (fun _ _ ⟨i⟩ => ⟨F.mapIso i⟩)

abbrev forget : Classes M.Elements → Classes C := onClasses (Functor.Elements.π M)

abbrev fibre (A : C) := {x : Classes M.Elements // forget M x = classOf A}

def mark (A : C) (m : M.obj A) : fibre M A :=
  ⟨classOf (M.elementsMk A m), rfl⟩

/-- Changing the identification of the underlying object with A acts by Aut(A). -/
def orbit (A : C) : Setoid (M.obj A) where
  r x y := ∃ e : A ≅ A, M.map e.hom x = y
  iseqv := {
    refl x := ⟨Iso.refl A, by simp⟩
    symm := by
      rintro x y ⟨e, rfl⟩
      exact ⟨e.symm, Functor.map_hom_inv'_apply M e x⟩
    trans := by
      rintro x y z ⟨e, rfl⟩ ⟨f, rfl⟩
      exact ⟨e.trans f, by simp⟩ }

/-- Every isomorphism class over [A] has a representative on A itself. -/
theorem mark_surjective (A : C) : Function.Surjective (mark M A) := by
  rintro ⟨x,hx⟩
  induction x using Quotient.inductionOn with
  | _ X =>
    obtain ⟨e⟩ : IsIsomorphic X.obj A := Quotient.exact hx
    refine ⟨M.map e.hom X.val, Subtype.ext ?_⟩
    exact Quotient.sound ⟨(Functor.Elements.isoMk e (by rfl) :
      X ≅ M.elementsMk A (M.map e.hom X.val)).symm⟩

/-- Two representatives give the same point precisely when an automorphism
of the underlying object carries one marking to the other. -/
theorem mark_eq_iff (A : C) (x y : M.obj A) :
    mark M A x = mark M A y ↔ (orbit M A).r x y := by
  constructor
  · intro h
    obtain ⟨e⟩ : IsIsomorphic (M.elementsMk A x) (M.elementsMk A y) :=
      Quotient.exact (congrArg Subtype.val h)
    exact ⟨(Functor.Elements.π M).mapIso e, e.hom.map_val⟩
  · rintro ⟨e,he⟩
    exact Subtype.ext (Quotient.sound ⟨Functor.Elements.isoMk e he⟩)

/-- The coarse fibre of a functor of markings is its orbit set on A. -/
noncomputable def orbitEquivFibre (A : C) : Quotient (orbit M A) ≃ fibre M A :=
  Equiv.ofBijective
    (Quotient.lift (mark M A) (fun x y => (mark_eq_iff M A x y).2)) (by
      constructor
      · intro x y
        induction x using Quotient.inductionOn with
        | _ a =>
          induction y using Quotient.inductionOn with
          | _ b => exact fun h => Quotient.sound ((mark_eq_iff M A a b).1 h)
      · intro x
        obtain ⟨a,rfl⟩ := mark_surjective M A x
        exact ⟨Quotient.mk _ a,rfl⟩)

variable {M} (g : C ⥤ C) (a : M ⟶ g ⋙ M)

/-- The map on marked objects induced by change of base and naturality of the markings. -/
def onElements : M.Elements ⥤ M.Elements where
  obj X := M.elementsMk (g.obj X.obj) (a.app X.obj X.val)
  map f := Functor.Elements.homMk (g.map f.hom)
    (by rw [← f.map_val]; exact (a.naturality_apply f.hom _).symm)
  map_id X := Functor.Elements.hom_ext (g.map_id _)
  map_comp f h := Functor.Elements.hom_ext (g.map_comp _ _)

/-- A comparison gA ≅ A intertwines base change on classes with transport of markings on A. -/
theorem transport_class {A : C} (h : g.obj A ≅ A) (m : M.obj A) :
    onClasses (onElements g a) (mark M A m).val =
      (mark M A (M.map h.hom (a.app A m))).val :=
  Quotient.sound ⟨Functor.Elements.isoMk h rfl⟩

/-- Changing the comparison isomorphism has no effect on the coarse point. -/
theorem comparison_independent {A : C} (h k : g.obj A ≅ A) (m : M.obj A) :
    mark M A (M.map h.hom (a.app A m)) = mark M A (M.map k.hom (a.app A m)) :=
  Subtype.ext ((transport_class g a h m).symm.trans (transport_class g a k m))

/-- Exact fixed-fibre criterion. The correcting automorphism may depend on the marking. -/
theorem fixes_fibre_iff {A : C} (h : g.obj A ≅ A) :
    (∀ z : fibre M A, onClasses (onElements g a) z.val = z.val) ↔
    ∀ m : M.obj A, ∃ e : A ≅ A, M.map e.hom (M.map h.hom (a.app A m)) = m := by
  constructor
  · intro fixed m
    apply (mark_eq_iff M A _ _).1
    exact Subtype.ext ((transport_class g a h m).symm.trans (fixed (mark M A m)))
  · intro correct z
    obtain ⟨m,rfl⟩ := mark_surjective M A z
    exact (transport_class g a h m).trans
      (congrArg Subtype.val ((mark_eq_iff M A _ _).2 (correct m)))

end ZInQBlueprint.MarkingTransport

#print axioms ZInQBlueprint.MarkingTransport.mark_surjective
#print axioms ZInQBlueprint.MarkingTransport.mark_eq_iff
#print axioms ZInQBlueprint.MarkingTransport.orbitEquivFibre
#print axioms ZInQBlueprint.MarkingTransport.transport_class
#print axioms ZInQBlueprint.MarkingTransport.comparison_independent
#print axioms ZInQBlueprint.MarkingTransport.fixes_fibre_iff
