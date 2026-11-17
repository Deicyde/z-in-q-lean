import MarkedScalarTower
import Mathlib.FieldTheory.Galois.Infinite

namespace ZInQBlueprint.DiamondHeight
noncomputable section

/-- The restriction to a finite Galois marking field has open kernel in the Krull topology. -/
theorem marking_open (L : IntermediateField ℚ Qbar) [IsGalois ℚ L] [FiniteDimensional ℚ L] :
    IsOpen (markingGroup L : Set GQ) := by
  change IsOpen ((AlgEquiv.restrictNormalHom L : (Qbar ≃ₐ[ℚ] Qbar) →* (L ≃ₐ[ℚ] L)).ker.carrier)
  rw [L.restrictNormalHom_ker]
  exact IntermediateField.fixingSubgroup_isOpen L

/-- A continuous scalar character of bounded order cuts out an open subgroup.
Its image lies in a finite discrete subspace of the complex units. -/
theorem continuous_scalar_kernel {R:ℕ} (S:ScalarTower R) (marking : IsOpen (S.marking:Set GQ))
    (continuous : Continuous S.scalar) :
    IsOpen ((S.scalar.ker.map S.marking.subtype:Subgroup GQ):Set GQ) := by
  let : NeZero (2*S.m) := ⟨(Nat.mul_pos (by decide) S.m_pos).ne'⟩
  let b : S.marking → rootsOfUnity (2*S.m) ℂ :=
    fun x => ⟨S.scalar x,(mem_rootsOfUnity ..).mpr (S.exponent_bound x)⟩
  have bc : Continuous b:=continuous.subtype_mk _
  have same : (S.scalar.ker:Set S.marking) = b ⁻¹' ({1} : Set (rootsOfUnity (2*S.m) ℂ)) := by
    ext x
    change S.scalar x=1 ↔ b x=1
    exact ⟨fun eqn => Subtype.ext eqn,fun eqn => congrArg Subtype.val eqn⟩
  apply marking.isOpenMap_subtype_val (S.scalar.ker:Set S.marking)
  rw [same]
  exact (isOpen_discrete _).preimage bc

/-- The open kernel defines a finite Galois number field, and its actual
field degree is the index used in the isogeny estimate. -/
theorem isogeny_field {R:ℕ} (S : ScalarTower R)
    (open_kernel : IsOpen ((S.scalar.ker.map S.marking.subtype : Subgroup GQ) : Set GQ)) :
    ∃ L' : IntermediateField ℚ Qbar, FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      L'.fixingSubgroup=S.scalar.ker.map S.marking.subtype ∧
      Module.finrank ℚ L'=S.fieldDegree ∧ Module.finrank ℚ L'≤2304*unitOrders R := by
  let U : OpenSubgroup (Qbar ≃ₐ[ℚ] Qbar) := ⟨S.scalar.ker.map S.marking.subtype,open_kernel⟩
  let H : ClosedSubgroup (Qbar ≃ₐ[ℚ] Qbar) := ⟨U.toSubgroup,U.isClosed⟩
  let L := IntermediateField.fixedField (F:=ℚ) (E:=Qbar) H.toSubgroup
  have fixing : L.fixingSubgroup=H.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  have dim : FiniteDimensional ℚ L := (InfiniteGalois.isOpen_iff_finite L).mp (by rw [fixing];exact open_kernel)
  have gal : IsGalois ℚ L := (InfiniteGalois.normal_iff_isGalois L).mp (by rw [fixing];exact S.normal)
  have index := marking_index L
  have agree : markingGroup L=L.fixingSubgroup := L.restrictNormalHom_ker
  have eqn : Module.finrank ℚ L=S.fieldDegree := by rw [←index,agree,fixing];rfl
  exact ⟨L,dim,gal,fixing,eqn,eqn.le.trans (scalar_field_degree S)⟩

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.marking_open
#print axioms ZInQBlueprint.DiamondHeight.continuous_scalar_kernel
#print axioms ZInQBlueprint.DiamondHeight.isogeny_field
