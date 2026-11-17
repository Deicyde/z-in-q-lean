import RootDiscriminant
import BranchI4Identification

/-! The symmetric polynomial of the ten branch weights. This is a consequence of
the literal definitions of the two invariants, for an arbitrary labelling. -/
namespace ZInQBlueprint.BranchFormula
open ThetaPeriod BranchI4 SexticInvariants SexticThetaHeight Polynomial
noncomputable section

theorem quotient_of_scaling (w v : Fin 10 → ℂ) {d : ℂ} (hd : d ≠ 0)
    (h : ∀ i, v i*d = w i) :
    (∑ i, v i)^10/(∏ i, v i) = (∑ i, w i)^10/(∏ i, w i) := by
  have hs : (∑ i, v i)*d = ∑ i, w i := by simp [Finset.sum_mul,h]
  have hp : (∏ i, v i)*d^10 = ∏ i, w i := by
    simpa only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
      (Finset.prod_congr rfl (fun i (_ : i ∈ (Finset.univ : Finset (Fin 10))) => h i))
  rw [← hs,← hp, mul_pow, mul_div_mul_right _ _ (pow_ne_zero 10 hd)]

/-- The branch identity for any rational polynomial of degree six with six distinct roots. -/
theorem rational_branch_invariant (f : ℚ[X]) (hd : f.natDegree = 6)
    (r : Fin 6 → ℂ) (hr : Function.Injective r) (hz : ∀ i, aeval (r i) f = 0)
    (label : Fin 10 ≃ Partition) :
    (∑ i, branchValue (finiteBranches r) (label i))^10 /
      (∏ i, branchValue (finiteBranches r) (label i)) =
      (((igusaI4 f^5/f.discr^2 : ℚ) : ℂ))^2 := by
  let a : ℂ := f.leadingCoeff
  have ha : a ≠ 0 := by
    change (↑f.leadingCoeff : ℂ) ≠ 0
    exact_mod_cast leadingCoeff_ne_zero.mpr (fun hf => by simp [hf] at hd)
  have under : (f.discr : ℂ) = a^10*(vandermonde r)^2 := discriminant_roots f hd r hr hz
  have top : a^4*weightSum r = (igusaI4 f : ℂ) := rational_i4_sum f hd r hr hz
  have hv : vandermonde r ≠ 0 := by
    unfold vandermonde
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => by
      split_ifs with h
      · exact sub_ne_zero.mpr (hr.ne h.ne)
      · exact one_ne_zero))
  let v := branchValue (finiteBranches r)
  change (∑ i, v (label i))^10/(∏ i, v (label i)) = (((igusaI4 f^5/f.discr^2 : ℚ) : ℂ))^2
  rw [label.sum_comp v, label.prod_comp v, ← pairs.sum_comp v, ← pairs.prod_comp v]
  rw [quotient_of_scaling (rowWeight r) (fun i => v (pairs i)) (pow_ne_zero 4 (denominator_ne hr))
    (clear_row hr), sum_rowWeights,prod_rowWeights]
  push_cast
  rw [← top,under]
  field_simp [ha,hv]

theorem sextic_branch_invariant {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    (r : Fin 6 → ℂ) (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ) = 0)
    (label : Fin 10 ≃ Partition) :
    (∑ i, branchValue (finiteBranches r) (label i))^10 /
      (∏ i, branchValue (finiteBranches r) (label i)) =
      (((igusaI4 (sextic u δ)^5/(sextic u δ).discr^2 : ℚ) : ℂ))^2 :=
  rational_branch_invariant _ (smooth_sextic hu hδ).1 r hr hz label

end
end ZInQBlueprint.BranchFormula
#print axioms ZInQBlueprint.BranchFormula.quotient_of_scaling
#print axioms ZInQBlueprint.BranchFormula.rational_branch_invariant
#print axioms ZInQBlueprint.BranchFormula.sextic_branch_invariant
