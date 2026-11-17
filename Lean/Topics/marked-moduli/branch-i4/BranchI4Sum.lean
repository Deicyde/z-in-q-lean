import BranchCoefficients

/-! Translating the sixth branch to zero lowers the ring calculation by one variable. -/
namespace ZInQBlueprint.BranchI4
noncomputable section

private def translate (r : Fin 6 → ℂ) (z : ℂ) : Fin 6 → ℂ := fun i => r i-z

private theorem translate_sum (r : Fin 6 → ℂ) (z : ℂ) :
    weightSum (translate r z) = weightSum r := by
  simp only [weightSum,weight,triple,translate,sub_sub_sub_cancel_right]

private def coefficientQuartic (r : Fin 6 → ℂ) : ℂ :=
  quartic (rootsCoeff r 0) (rootsCoeff r 1) (rootsCoeff r 2) (rootsCoeff r 3)
    (rootsCoeff r 4) (rootsCoeff r 5) (rootsCoeff r 6)

private theorem translate_invariant (r : Fin 6 → ℂ) (z : ℂ) :
    coefficientQuartic (translate r z) = coefficientQuartic r := by
  let p := rootsCoeff r
  unfold coefficientQuartic
  refine Eq.trans ?_ (translate_quartic (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) z)
  congr 1 <;> simp [p, rootsCoeff,translate] <;> ring

set_option maxHeartbeats 5000000 in
private theorem zero_i4 (r : Fin 6 → ℂ) (h : r 5 = 0) :
    weightSum r = coefficientQuartic r := by
  simp only [coefficientQuartic, rootsCoeff, weightSum, weight, triple, quartic, h,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, neg_zero, mul_one, sq]
  grind only

theorem monic_i4_sum (r : Fin 6 → ℂ) :
    weightSum r = quartic (rootsCoeff r 0) (rootsCoeff r 1) (rootsCoeff r 2)
      (rootsCoeff r 3) (rootsCoeff r 4) (rootsCoeff r 5) (rootsCoeff r 6) :=
  (translate_sum r (r 5)).symm.trans <| (zero_i4 (translate r (r 5)) (sub_self _)).trans
    (translate_invariant r (r 5))

end
end ZInQBlueprint.BranchI4
#print axioms ZInQBlueprint.BranchI4.monic_i4_sum
