import Mathlib.FieldTheory.Galois.Basic

namespace ZInQBlueprint.BranchId
open IntermediateField
noncomputable section
variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- A base-preserving isomorphism from a normal subfield already determines
its image in the chosen common ambient field. -/
theorem same_normal_subfield {L M : IntermediateField F K} [Normal F L]
    (e : L ≃ₐ[F] M) : L=M := by
  have h := (M.val.comp e.toAlgHom).fieldRange_of_normal
  rw [←h]
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact (e a).property
  · intro hx
    let y : M:=⟨x,hx⟩
    refine ⟨e.symm y,?_⟩
    change (e (e.symm y) : K)=x
    rw [e.apply_symm_apply]
    
/-- In a finite Galois field, quotient fields fixed by disjoint inertia
subgroups recover their entire common covering field by compositum. -/
theorem quotient_compositum [FiniteDimensional F K] [IsGalois F K]
    (H J : Subgroup (K ≃ₐ[F] K)) (disj : H ⊓ J=⊥) :
    fixedField H ⊔ fixedField J = (⊤ : IntermediateField F K) := by
  let e := (IsGalois.intermediateFieldEquivSubgroup (F:=F) (E:=K)).symm
  calc
    fixedField H ⊔ fixedField J = e (OrderDual.toDual H ⊔ OrderDual.toDual J) :=
      (e.map_sup _ _).symm
    _ = fixedField (H⊓J) := rfl
    _ = ⊤ := by rw [disj,fixedField_bot]

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.same_normal_subfield
#print axioms ZInQBlueprint.BranchId.quotient_compositum
