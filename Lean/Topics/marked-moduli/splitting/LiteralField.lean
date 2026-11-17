import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Normal.Closure

/-! Splitting subfields inside a specified ambient field. -/
namespace MarkedModuli.Splitting
open Polynomial IntermediateField

variable (F : Type*) [Field F] (Ω : Type*) [Field Ω] [Algebra F Ω]
variable (A : Type*) [CommRing A] [Algebra F A]

/-- Geometric points of an affine fibre in the chosen ambient field. -/
abbrev Points := A →ₐ[F] Ω

/-- The Galois permutation acts by postcomposition on *all* geometric points. -/
def pointAction : (Ω ≃ₐ[F] Ω) →* Equiv.Perm (Points F Ω A) where
  toFun g := {
    toFun x := g.toAlgHom.comp x
    invFun x := g.symm.toAlgHom.comp x
    left_inv x := by ext a; exact g.symm_apply_apply _
    right_inv x := by ext a; exact g.apply_symm_apply _ }
  map_one' := by ext x a; rfl
  map_mul' _ _ := by ext x a; rfl

/-- Smallest subfield in which every geometric point is rational. -/
def pointField : IntermediateField F Ω :=
  adjoin F {z : Ω | ∃ (x : Points F Ω A) (a : A), x a = z}

theorem pointField_le_iff (U : IntermediateField F Ω) :
    pointField F Ω A ≤ U ↔ ∀ (x : Points F Ω A) (a : A), x a ∈ U := by
  rw [pointField, adjoin_le_iff]
  exact ⟨fun h x a ↦ h ⟨x, a, rfl⟩, fun h _ ⟨x, a, e⟩ ↦ e ▸ h x a⟩

/-- A field of definition for each point, in the given embedding into Ω,
contains the literal common splitting subfield. -/
theorem pointField_le_iff_lifts (U : IntermediateField F Ω) :
    pointField F Ω A ≤ U ↔ ∀ x : Points F Ω A, ∃ y : A →ₐ[F] U, U.val.comp y = x := by
  rw [pointField_le_iff]
  constructor
  · intro h x
    exact ⟨x.codRestrict U.toSubalgebra (h x), rfl⟩
  · rintro h x a
    obtain ⟨y, rfl⟩ := h x
    exact (y a).2

/-- Fixing an arbitrary generating set fixes the entire intermediate field. -/
theorem mem_fixing_adjoin_iff (s : Set Ω) (g : Ω ≃ₐ[F] Ω) :
    g ∈ (adjoin F s).fixingSubgroup ↔ ∀ x ∈ s, g x = x := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · exact fun h x hx ↦ h x (subset_adjoin F s hx)
  · intro h x hx
    have he : g.toAlgHom.comp (adjoin F s).val = (adjoin F s).val :=
      IntermediateField.adjoin_algHom_ext F (fun z hz ↦ h z hz)
    exact DFunLike.congr_fun he ⟨x, hx⟩

theorem pointAction_kernel :
    (pointAction F Ω A).ker = (pointField F Ω A).fixingSubgroup := by
  ext g
  rw [pointField, mem_fixing_adjoin_iff, MonoidHom.mem_ker]
  constructor
  · intro h z ⟨x, a, e⟩
    subst z
    exact DFunLike.congr_fun (Equiv.congr_fun h x) a
  · intro h
    ext x a
    exact h (x a) ⟨x, a, rfl⟩

theorem fixedField_pointAction [IsGalois F Ω] :
    fixedField (pointAction F Ω A).ker = pointField F Ω A := by
  rw [pointAction_kernel, InfiniteGalois.fixedField_fixingSubgroup]

/-- For a field component the common field of definition is Mathlib's normal
closure, taken inside Ω. This statement asks for every embedding of that field. -/
theorem pointField_field (E : Type*) [Field E] [Algebra F E] :
    pointField F Ω E = normalClosure F E Ω := by
  apply le_antisymm
  · apply (pointField_le_iff F Ω E _).mpr
    exact fun x a ↦ x.fieldRange_le_normalClosure ⟨a, rfl⟩
  · refine iSup_le (fun (x : E →ₐ[F] Ω) z hz ↦ ?_)
    obtain ⟨a, rfl⟩ := hz
    exact subset_adjoin F _ ⟨x, a, rfl⟩

/-- The roots of a polynomial as a Galois set in the chosen ambient field. -/
def rootAction (p : F[X]) : (Ω ≃ₐ[F] Ω) →* Equiv.Perm (p.rootSet Ω) := by
  let forward (g : Ω ≃ₐ[F] Ω) (r : p.rootSet Ω) : p.rootSet Ω :=
    ⟨g r, mem_rootSet'.mpr ⟨(mem_rootSet'.mp r.2).1, by
      rw [aeval_algHom_apply g, (mem_rootSet'.mp r.2).2, map_zero]⟩⟩
  exact {
    toFun g := {
      toFun := forward g
      invFun := forward g.symm
      left_inv r := Subtype.ext (g.symm_apply_apply _)
      right_inv r := Subtype.ext (g.apply_symm_apply _) }
    map_one' := by ext; rfl
    map_mul' _ _ := by ext; rfl }

theorem rootAction_apply (p : F[X]) (g : Ω ≃ₐ[F] Ω) (r : p.rootSet Ω) :
    ((rootAction F Ω p g r : p.rootSet Ω) : Ω) = g r := rfl

theorem rootAction_kernel (p : F[X]) :
    (rootAction F Ω p).ker = (adjoin F (p.rootSet Ω)).fixingSubgroup := by
  ext g
  rw [mem_fixing_adjoin_iff, MonoidHom.mem_ker]
  constructor
  · intro h z hz
    exact congrArg Subtype.val (Equiv.congr_fun h ⟨z,hz⟩)
  · intro h
    ext r
    exact h r r.2

/-- In a Galois ambient field that contains all the roots, the fixed field
is the literal intermediate splitting field, and carries the stock splitting-field predicate. -/
theorem fixedField_rootAction (p : F[X]) [IsGalois F Ω]
    (hs : (p.map (algebraMap F Ω)).Splits) :
    fixedField (rootAction F Ω p).ker = adjoin F (p.rootSet Ω) ∧
      p.IsSplittingField F (fixedField (rootAction F Ω p).ker) := by
  rw [rootAction_kernel, InfiniteGalois.fixedField_fixingSubgroup]
  exact ⟨rfl, adjoin_rootSet_isSplittingField hs⟩

end MarkedModuli.Splitting

#print axioms MarkedModuli.Splitting.pointField_le_iff_lifts
#print axioms MarkedModuli.Splitting.pointAction_kernel
#print axioms MarkedModuli.Splitting.fixedField_pointAction
#print axioms MarkedModuli.Splitting.pointField_field
#print axioms MarkedModuli.Splitting.rootAction_kernel
#print axioms MarkedModuli.Splitting.fixedField_rootAction
