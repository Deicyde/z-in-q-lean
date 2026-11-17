import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.Tactic

open scoped TensorProduct

namespace ZInQBlueprint.ToricRank

/-- A rational action of a four-dimensional division algebra on a vector space of
dimension at most two forces the vector space to vanish. Evaluation at a nonzero
vector is injective since every nonzero element of the algebra acts invertibly. -/
theorem subsingleton_of_quaternion_action
    (D V : Type*) [DivisionRing D] [Algebra ℚ D] [FiniteDimensional ℚ D]
    [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (hD : Module.finrank ℚ D = 4) (hV : Module.finrank ℚ V ≤ 2)
    (ρ : D →ₐ[ℚ] Module.End ℚ V) : Subsingleton V := by
  by_contra hn
  have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hn
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let e : D →ₗ[ℚ] V := (LinearMap.applyₗ v).comp ρ.toLinearMap
  have hinj : Function.Injective e := by
    apply (LinearMap.ker_eq_bot.mp ?_)
    apply LinearMap.ker_eq_bot'.mpr
    intro d hd
    by_contra hd0
    apply hv
    have he := congrArg (fun w => ρ d⁻¹ w) hd
    change ρ d⁻¹ (ρ d v) = ρ d⁻¹ 0 at he
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel₀ hd0, map_one,
      Module.End.one_apply, map_zero] using he
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  omega

/-- It suffices to specialize the integral endomorphism order to the integral
cocharacter lattice. Tensoring both with the rationals constructs the action. -/
theorem toric_rank_zero (O D X : Type*) [Ring O] [DivisionRing D] [Algebra ℚ D]
    [FiniteDimensional ℚ D] [AddCommGroup X] {t : ℕ} (b : Module.Basis (Fin t) ℤ X)
    (order : (ℚ ⊗[ℤ] O) ≃ₐ[ℚ] D) (hD : Module.finrank ℚ D = 4) (ht : t ≤ 2)
    (act : O →ₐ[ℤ] Module.End ℤ X) : t = 0 := by
  let V := ℚ ⊗[ℤ] X
  let bQ : Module.Basis (Fin t) ℚ V := b.baseChange ℚ
  have : FiniteDimensional ℚ V := Module.Finite.of_basis bQ
  have hdim : Module.finrank ℚ V = t := by simpa using Module.finrank_eq_card_basis bQ
  let integral : O →ₐ[ℤ] Module.End ℚ V := (Module.End.baseChangeHom ℤ ℚ X).comp act
  let rational := AlgHom.liftEquiv ℤ ℚ O (Module.End ℚ V) integral
  have : Subsingleton V := subsingleton_of_quaternion_action D V hD (hdim.trans_le ht)
    (rational.comp order.symm.toAlgHom)
  rw [← hdim]
  exact Module.finrank_zero_of_subsingleton

end ZInQBlueprint.ToricRank

#print axioms ZInQBlueprint.ToricRank.subsingleton_of_quaternion_action

#print axioms ZInQBlueprint.ToricRank.toric_rank_zero
