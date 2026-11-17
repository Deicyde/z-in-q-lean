import GenusVector

/-! A triangular character expansion in the rationalized elliptic group.
The only indices needed for an odd input are its divisors congruent to 5 or 7 modulo 8. -/
namespace ZInQBlueprint.TYZ.Specialization
open TensorProduct TraceAction
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.decEq

/-- Action of a Gaussian unit on the rationalized Mordell–Weil group. -/
def unitVector (u : GaussianUnit) : (ℚ ⊗[ℤ] A) →ₗ[ℤ] (ℚ ⊗[ℤ] A) :=
  (unitHom u).toIntLinearMap.lTensor ℚ

theorem unitVector_tmul (u : GaussianUnit) (a : ℚ) (P : A) :
    unitVector u (a ⊗ₜ[ℤ] P) = a ⊗ₜ[ℤ] u.act P := by
  rw [←unitHom_apply]
  rfl

/-- The genus trace is the sum of the distinguished character vector and the
proper-factor terms. This condition involves the primitive traces, not their
recursively chosen integral representatives. -/
def GenusExpansion (D : RecursionData) (v : ℕ → ℚ ⊗[ℤ] A) (N : ℕ) : Prop :=
  ∀ e, e ∣ N → (e%8=5 ∨ e%8=7) →
    (1:ℚ) ⊗ₜ[ℤ] D.trace e = v e + ∑ t ∈ recursionFactors e,
      (D.L t) • unitVector (D.epsilon (e/t) t) (v (e/t))

/-- The expansion has a unique solution on the needed divisors.
The integral recursion realizes this solution after tensoring with ℚ. -/
theorem representative_of_expansion {D : RecursionData} {N : ℕ} {v : ℕ → ℚ ⊗[ℤ] A}
    (h : GenusExpansion D v N) (e : ℕ) (he : e ∣ N) (hr : e%8=5 ∨ e%8=7) :
    (1:ℚ) ⊗ₜ[ℤ] representative D e = v e := by
  induction e using Nat.strong_induction_on with
  | h e ih =>
    let j := TensorProduct.mk ℤ ℚ A 1
    change j (representative D e) = _
    rw [representative_eq,map_sub,map_sum]
    have hterms : ∀ t ∈ recursionFactors e,
        j ((D.L t) • (D.epsilon (e/t) t).act (representative D (e/t))) =
          (D.L t) • unitVector (D.epsilon (e/t) t) (v (e/t)) := by
      intro t ht
      have hd := (Nat.mem_divisors.mp (Finset.mem_filter.mp ht).1).1
      have hp := ih (e/t) (factor_lt ht) ((Nat.div_dvd_of_dvd hd).trans he) (cofactor_odd_class ht hr)
      rw [map_zsmul,←hp,unitVector_tmul]
      rfl
    rw [Finset.sum_congr rfl hterms]
    have ht := h e he hr
    change j (D.trace e) = _ at ht
    rw [ht,add_sub_cancel_right]

/-- The character vectors lie in their own quadratic minus subgroups.
Their expansion of primitive traces suffices for the rank witness. -/
theorem represents_of_character_expansion {D : RecursionData} {N : ℕ}
    (v : ∀ e : ℕ, ℚ ⊗[ℤ] ↥(minusSource e))
    (h : GenusExpansion D (fun e => minusInclusion e (v e)) N)
    (hr : N%8=5 ∨ N%8=7) : RepresentsGenusVector N (representative D N) :=
  ⟨v N, (representative_of_expansion h N dvd_rfl hr).symm⟩

/-- Conditional fixed-polynomial endpoint. All odd-row CM assumptions refer
to primitive traces, their fields and the corresponding published character expansion. -/
theorem frozen_of_fixed_periods_and_character_expansions (hp : ThetaPeriod.HasFixedPeriods)
    (S : CMTraces) (L : ℕ → ℤ) (eps : ℕ → ℕ → GaussianUnit) (h1 : L 1 = 1)
    (hc : ClassThreePeriods L) (hf : TraceFields (S.recursion L eps) S.extended)
    (pointwise : ∀ n, n%8=5 → Squarefree n → ZInQ.RouteK.Rank5b.T5bCl n = 1 →
      (∃ σ : Gal, LocalTraceLaw (S.recursion L eps) σ n) ∧
      (∀ Y : pointsOver (genusCompositum S.extended n), IsOfFinAddOrder Y.val →
        onePlusI (onePlusI (onePlusI Y.val)) = 0) ∧
      ∃ v : ∀ e : ℕ, ℚ ⊗[ℤ] ↥(minusSource e),
        GenusExpansion (S.recursion L eps) (fun e => minusInclusion e (v e)) n) :
    ZInQ.FrozenTarget := by
  apply HeightBudget.frozen_of_remaining_and_class_rank
    (ThetaPeriod.remaining_of_labelledPeriods (ThetaPeriod.labelledPeriods_of_fixedPeriods hp))
  apply rank_of_genusVectors S L eps h1 hc hf
  intro n hn hs ho
  obtain ⟨hl,ht,v,hv⟩ := pointwise n hn hs ho
  exact ⟨hl,ht,represents_of_character_expansion v hv (Or.inl hn)⟩

end
end ZInQBlueprint.TYZ.Specialization
#print axioms ZInQBlueprint.TYZ.Specialization.unitVector_tmul
#print axioms ZInQBlueprint.TYZ.Specialization.representative_of_expansion
#print axioms ZInQBlueprint.TYZ.Specialization.represents_of_character_expansion
#print axioms ZInQBlueprint.TYZ.Specialization.frozen_of_fixed_periods_and_character_expansions
