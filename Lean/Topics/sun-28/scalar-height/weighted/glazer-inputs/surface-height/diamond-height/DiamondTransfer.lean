import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Tactic

/-! Determinants and descent to the effective diamond quotient. -/
namespace ZInQBlueprint.DiamondHeight
noncomputable section

/-- A character whose square is trivial on a finite-index normal subgroup has
order dividing twice its index. This applies to det(r)/χ_cyc on the Galois group. -/
theorem character_order_dvd {G K : Type*} [Group G] [CommGroup K]
    (ε : G →* K) (H : Subgroup G) [H.Normal]
    (square : ∀ g ∈ H, (ε g)^2=1) : orderOf ε ∣ 2*H.index := by
  apply orderOf_dvd_of_pow_eq_one
  ext g
  change (ε g)^(2*H.index)=1
  rw [Nat.mul_comm, pow_mul, ← map_pow]
  exact square _ (H.pow_index_mem g)

/-- Pullback after pushforward is the sum over the effective group of deck
transformations. Any invariant quotient then factors through pushforward over ℚ. -/
theorem factor_through_pushforward {H X Y A : Type*} [Fintype H] [Nonempty H]
    [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]
    [AddCommGroup A] [Module ℚ A]
    (push : X →ₗ[ℚ] Y) (pull : Y →ₗ[ℚ] X) (q : X →ₗ[ℚ] A)
    (action : H → X →ₗ[ℚ] X)
    (trace : ∀ x, pull (push x)=∑ i, action i x)
    (invariant : ∀ i x, q (action i x)=q x) :
    ∃ f : Y →ₗ[ℚ] A, f.comp push=q ∧ (Function.Surjective q → Function.Surjective f) := by
  let f : Y →ₗ[ℚ] A := (Fintype.card H : ℚ)⁻¹ • q.comp pull
  have hf (x:X) : f (push x)=q x := by
    change (Fintype.card H : ℚ)⁻¹ • q (pull (push x))=q x
    rw [trace,map_sum]
    simp only [invariant,Finset.sum_const,Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℚ,smul_smul,inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero),one_smul]
  exact ⟨f,LinearMap.ext hf,fun sur a => by obtain ⟨x,rfl⟩:=sur a;exact ⟨push x,hf x⟩⟩

end
end ZInQBlueprint.DiamondHeight
#print axioms ZInQBlueprint.DiamondHeight.character_order_dvd
#print axioms ZInQBlueprint.DiamondHeight.factor_through_pushforward
