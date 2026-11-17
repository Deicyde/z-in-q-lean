import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.Tactic

namespace ZInQBlueprint.WildLevel
open Matrix
open scoped MatrixGroups
noncomputable section

/-- Both actions above an element of the absolute Galois group implement the
same conjugation on a common absolutely irreducible summand. Schur's lemma
then compares the two invertible operators before passage to projective space. -/
theorem intertwiner_scalar {K M V : Type*} [Field K] [IsAlgClosed K] [Group M]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K M V) [ρ.IsIrreducible] (twist : M → M)
    (U T : V ≃ₗ[K] V)
    (geometric : ∀ m v, U (ρ m v) = ρ (twist m) (U v))
    (modular : ∀ m v, T (ρ m v) = ρ (twist m) (T v)) :
    ∃ c : Kˣ, ∀ v, T v = (c:K) • U v := by
  let q := (T.trans U.symm).toLinearMap
  have intertwines (m : M) (v : V) : q (ρ m v)=ρ m (q v) := by
    apply U.injective
    change U (U.symm (T (ρ m v)))=U (ρ m (U.symm (T v)))
    rw [U.apply_symm_apply,geometric,U.apply_symm_apply,modular]
  let f : Representation.IntertwiningMap ρ ρ := { q with isIntertwining' := fun m => LinearMap.ext (intertwines m) }
  obtain ⟨c,hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ:=ρ)).surjective f
  have identity (v : V) : U.symm (T v)=c • v :=
    (congrArg (fun x : Representation.IntertwiningMap ρ ρ => x v) hc).symm
  have cn : c≠0 := by
    intro h
    obtain ⟨v,hv⟩:=exists_ne (0:V)
    have := identity v
    rw [h,zero_smul] at this
    exact hv ((T.trans U.symm).injective (this.trans (map_zero (T.trans U.symm)).symm))
  refine ⟨Units.mk0 c cn,fun v=>?_⟩
  exact (U.apply_symm_apply (T v)).symm.trans ((congrArg U (identity v)).trans (map_smul U c v))

/-- A nonzero proportionality between two rank-two matrices is precisely
what is needed for equality after projectivization. -/
theorem same_projective_matrix {K : Type*} [Field K] (U T : GL (Fin 2) K)
    (h : ∃ c : Kˣ, ∀ i j, (T:Matrix (Fin 2) (Fin 2) K) i j = c.val*(U:Matrix (Fin 2) (Fin 2) K) i j) :
    ProjGenLinGroup.mk U = ProjGenLinGroup.mk T := by
  obtain ⟨c,hc⟩:=h
  apply ProjGenLinGroup.mk_eq_mk_iff.mpr
  refine ⟨c, GeneralLinearGroup.ext fun i j=>?_⟩
  simpa [GeneralLinearGroup.coe_scalar,Matrix.scalar,Matrix.mul_diagonal,mul_comm] using (hc i j).symm

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.intertwiner_scalar
#print axioms ZInQBlueprint.WildLevel.same_projective_matrix
