import DivisorFields
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.FieldTheory.Finiteness

/-! Finite quadratic character sums in the proof of TYZ Theorem 3.5. -/
namespace ZInQBlueprint.TYZ.Specialization
open TensorProduct TraceAction
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.decEq

/-- A bit in the dual of the genus quotient gives an integer character value. -/
def quadraticSign (x : ZMod 2) : ℤ := if x = 0 then 1 else -1

theorem quadraticSign_add_one (x : ZMod 2) : quadraticSign (x + 1) = -quadraticSign x := by
  fin_cases x <;> decide

/-- Orthogonality for the full quadratic character group of an elementary
abelian two-group. The integer character sum vanishes away from zero. -/
theorem sum_quadraticSign {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (Module.Dual (ZMod 2) V)] (x : V) :
    ∑ f : Module.Dual (ZMod 2) V, quadraticSign (f x) =
      if x = 0 then (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) else 0 := by
  classical
  split_ifs with h
  · subst x
    simp [quadraticSign]
  · obtain ⟨g,hg⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) h
    let w := fun f : Module.Dual (ZMod 2) V => quadraticSign (f x)
    have shift := Equiv.sum_comp (Equiv.addRight g) w
    have neg (f : Module.Dual (ZMod 2) V) : w (f+g) = -w f := by
      change quadraticSign (f x + g x) = _
      rw [hg,quadraticSign_add_one]
    change (∑ f, w (f + g)) = ∑ f, w f at shift
    simp_rw [neg] at shift
    rw [Finset.sum_neg_distrib] at shift
    change ∑ f, w f = 0
    omega

/-- The common scalar in TYZ is exactly two to the dimension of the genus quotient. -/
theorem genus_character_card {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (Module.Dual (ZMod 2) V)] :
    Fintype.card (Module.Dual (ZMod 2) V) = 2 ^ Module.finrank (ZMod 2) V := by
  rw [Module.card_eq_pow_finrank (K := ZMod 2),ZMod.card,Subspace.dual_finrank_eq]

/-- The sum of the genus character traces is the number of characters times
the sum over representatives in the identity genus. Works in every abelian group. -/
theorem sum_character_traces {V I G : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (Module.Dual (ZMod 2) V)] [Fintype I] [AddCommGroup G]
    (q : I → V) (z : I → G) :
    ∑ f : Module.Dual (ZMod 2) V, ∑ t : I, quadraticSign (f (q t)) • z t =
      (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) •
        ∑ t ∈ Finset.univ.filter (fun t => q t = 0), z t := by
  classical
  rw [Finset.sum_comm, Finset.sum_filter, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [← Finset.sum_smul,sum_quadraticSign]
  split_ifs <;> simp

/-- A primitive genus trace expansion follows from the individual character
evaluations once their total is grouped into its proper-factor terms. -/
theorem trace_eq_of_character_values {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (Module.Dual (ZMod 2) V)] [Fintype I] (q : I → V) (z : I → (ℚ ⊗[ℤ] A))
    (P : ℚ ⊗[ℤ] A)
    (evaluations : ∑ f : Module.Dual (ZMod 2) V, ∑ t : I, quadraticSign (f (q t)) • z t =
      (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) • P) :
    ∑ t ∈ Finset.univ.filter (fun t => q t = 0), z t = P := by
  let c : ℤ := Fintype.card (Module.Dual (ZMod 2) V)
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (Fintype.card_pos (α := Module.Dual (ZMod 2) V)).ne'
  let _ : Module.IsTorsionFree ℤ (ℚ ⊗[ℤ] A) := Module.IsTorsionFree.trans ℚ
  exact smul_right_injective (ℚ ⊗[ℤ] A) hc ((sum_character_traces q z).symm.trans evaluations)

/-- Character calculations for one primitive trace. The first identity fixes the
points being summed and the identity-genus cosets. The second is the aggregate
of the character values supplied by the arithmetic theorem. -/
theorem primitive_trace_of_character_values {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (Module.Dual (ZMod 2) V)] [Fintype I] (D : RecursionData)
    (v : ℕ → ℚ ⊗[ℤ] A) (e : ℕ) (q : I → V) (z : I → A)
    (genusTrace : D.trace e = ∑ t ∈ Finset.univ.filter (fun t => q t = 0), z t)
    (evaluations : ∑ f : Module.Dual (ZMod 2) V, ∑ t : I,
        quadraticSign (f (q t)) • ((1:ℚ) ⊗ₜ[ℤ] z t) =
      (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) •
        (v e + ∑ t ∈ recursionFactors e, (D.L t) • unitVector (D.epsilon (e/t) t) (v (e/t)))) :
    (1:ℚ) ⊗ₜ[ℤ] D.trace e = v e + ∑ t ∈ recursionFactors e,
      (D.L t) • unitVector (D.epsilon (e/t) t) (v (e/t)) := by
  rw [genusTrace,TensorProduct.tmul_sum]
  exact trace_eq_of_character_values q (fun t => (1:ℚ) ⊗ₜ[ℤ] z t) _ evaluations

/-- Sum the individual Gross–Zagier character values. Each allowed factor has
one character, and the other character points have zero image after tensoring. -/
theorem primitive_trace_of_factors {V I : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Fintype (Module.Dual (ZMod 2) V)] [Fintype I] (D : RecursionData)
    (v : ℕ → ℚ ⊗[ℤ] A) (e : ℕ) (q : I → V) (z : I → A)
    (genusTrace : D.trace e = ∑ t ∈ Finset.univ.filter (fun t => q t = 0), z t)
    (chi : Option ↥(recursionFactors e) ↪ Module.Dual (ZMod 2) V)
    (trivialValue : ∑ t : I, quadraticSign (chi none (q t)) • ((1:ℚ) ⊗ₜ[ℤ] z t) =
      (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) • v e)
    (factorValue : ∀ j : ↥(recursionFactors e),
      ∑ t : I, quadraticSign (chi (some j) (q t)) • ((1:ℚ) ⊗ₜ[ℤ] z t) =
      (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) •
        ((D.L j.val) • unitVector (D.epsilon (e/j.val) j.val) (v (e/j.val))))
    (others : ∀ f : Module.Dual (ZMod 2) V, f ∉ Set.range chi →
      ∑ t : I, quadraticSign (f (q t)) • ((1:ℚ) ⊗ₜ[ℤ] z t) = 0) :
    (1:ℚ) ⊗ₜ[ℤ] D.trace e = v e + ∑ t ∈ recursionFactors e,
      (D.L t) • unitVector (D.epsilon (e/t) t) (v (e/t)) := by
  classical
  apply primitive_trace_of_character_values D v e q z genusTrace
  let H := fun f : Module.Dual (ZMod 2) V => ∑ t : I, quadraticSign (f (q t)) • ((1:ℚ) ⊗ₜ[ℤ] z t)
  change ∑ f, H f = _
  have support : ∑ f, H f = ∑ a : Option ↥(recursionFactors e), H (chi a) := by
    calc
      _ = ∑ f ∈ Finset.univ.map chi, H f := (Finset.sum_subset (Finset.subset_univ _) (by
        intro f _ hf
        apply others f
        rintro ⟨a,rfl⟩
        exact hf (Finset.mem_map_of_mem chi (Finset.mem_univ a)))).symm
      _ = _ := Finset.sum_map _ _ _
  change H (chi none) = _ at trivialValue
  rw [support,Fintype.sum_option,trivialValue,smul_add,Finset.smul_sum]
  congr 1
  calc
    _ = ∑ j : ↥(recursionFactors e), (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) •
        ((D.L j.val) • unitVector (D.epsilon (e/j.val) j.val) (v (e/j.val))) :=
      Finset.sum_congr rfl (fun j _ => factorValue j)
    _ = _ := Finset.sum_attach (recursionFactors e) (fun j : ℕ =>
      (Fintype.card (Module.Dual (ZMod 2) V) : ℤ) • ((D.L j) • unitVector (D.epsilon (e/j) j) (v (e/j))))

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.quadraticSign_add_one
#print axioms ZInQBlueprint.TYZ.Specialization.sum_quadraticSign
#print axioms ZInQBlueprint.TYZ.Specialization.sum_character_traces
#print axioms ZInQBlueprint.TYZ.Specialization.trace_eq_of_character_values
#print axioms ZInQBlueprint.TYZ.Specialization.primitive_trace_of_character_values
#print axioms ZInQBlueprint.TYZ.Specialization.primitive_trace_of_factors
#print axioms ZInQBlueprint.TYZ.Specialization.genus_character_card
