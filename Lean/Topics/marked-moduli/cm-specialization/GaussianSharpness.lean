import GaussianTwoPrimary

/-! Explicit point showing the obstruction √2 is exact for two-primary torsion. -/
namespace ZInQBlueprint.TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

/-- A field containing i and √2 contains a four-torsion point outside
A[(1+i)³]. Its tangent has slope (i+1)(1+√2). -/
theorem nonGaussian_four_of_sqrtTwo {F : SubfieldQ} (hiF : Rank.sqrtMinus 1 ∈ F)
    (hrF : sqrtDivisor 2 ∈ F) : ∃ P : A, P ∈ pointsOver F ∧ (4:ℕ) • P = 0 ∧
      onePlusI (onePlusI (onePlusI P)) ≠ 0 := by
  let i := Rank.sqrtMinus 1
  let r := sqrtDivisor 2
  have hi : i^2 = -1 := by simpa [i] using Rank.sqrtMinus_sq 1
  have hr : r^2 = 2 := by simpa [r] using sqrtDivisor_sq 2
  let t := 2*i
  let x := t*(1+r)
  let s := (i+1)*(1+r)
  let y := s*(x-t)
  have ht : t^2 = -4 := by dsimp [t]; linear_combination 4*hi
  have ht0 : t ≠ 0 := by intro hz; rw [hz] at ht; norm_num at ht
  have hquad : x^2-2*t*x+4 = 0 := by
    dsimp [x]
    linear_combination t^2*hr + ht
  have hs : s^2 = t+2*x := by
    dsimp [s,x,t]
    linear_combination (1+r)^2*hi+2*i*hr
  have hx : x-t ≠ 0 := by
    intro hz
    rw [sub_eq_zero.mp hz] at hquad
    have absurd : (8 : K) = 0 := by linear_combination hquad+ht
    norm_num at absurd
  have hs0 : s ≠ 0 := by
    intro hz
    rw [hz] at hs
    have hu : x = -(t/2) := by linear_combination -hs/2
    rw [hu] at hquad
    have absurd : (1 : K) = 0 := by linear_combination -hquad+5*ht/4
    norm_num at absurd
  have hy : y ≠ 0 := mul_ne_zero hs0 hx
  have eq : y^2 = x^3+4*x := by
    dsimp [y]
    linear_combination (x-t)^2*hs + (x-t)*hquad + (t-2*x)*ht
  have hns : genusCurve.toAffine.Nonsingular x y := by
    rw [nonsingular_iff]; refine ⟨?_,Or.inr ?_⟩
    · simpa [equation_iff,genusCurve] using eq
    · simp [genusCurve]; intro e; exact hy (by linear_combination e/2)
  have htEq : (0:K)^2 = t^3+4*t := by linear_combination -t*ht
  have htNS : genusCurve.toAffine.Nonsingular t 0 := by
    rw [nonsingular_iff]; refine ⟨?_,Or.inl ?_⟩
    · simpa [equation_iff,genusCurve] using htEq
    · simp [genusCurve]; intro e
      have absurd : (8 : K) = 0 := by linear_combination e+3*ht
      norm_num at absurd
  let P : A := .some x y hns
  let T : A := .some t 0 htNS
  have hP : P ∈ pointsOver F := by
    have htmem : t ∈ F := F.mul_mem (F.natCast_mem 2) hiF
    have hplus : 1+r ∈ F := F.add_mem F.one_mem hrF
    have hxmem : x ∈ F := F.mul_mem htmem hplus
    have hsmem : s ∈ F := F.mul_mem (F.add_mem hiF F.one_mem) hplus
    exact (some_mem_pointsOver F x y hns).mpr ⟨hxmem,F.mul_mem hsmem (F.sub_mem hxmem htmem)⟩
  have hny : y ≠ genusCurve.toAffine.negY x y := by
    simp [negY,genusCurve]; intro e; exact hy (by linear_combination e/2)
  have slope : genusCurve.toAffine.slope x x y y = s := by
    rw [slope_of_Y_ne rfl hny]
    simp [negY,genusCurve]
    field_simp [hy]
    dsimp [y]
    linear_combination -2*(x-t)*hs - hquad + 2*ht
  have addx : genusCurve.toAffine.addX x x s = t := by
    simp [addX,genusCurve]; linear_combination hs
  have hdouble : (2:ℕ) • P = T := by
    change (2:ℕ) • (.some x y hns : A) = .some t 0 htNS
    rw [two_nsmul,Point.add_self_of_Y_ne hny]
    erw [Point.some.injEq]
    rw [slope]
    refine ⟨addx,?_⟩
    rw [addY,negAddY,addx]
    simp [negY,genusCurve,y]; ring
  have htwo : (2:ℕ) • T = 0 := by
    exact (two_nsmul _).trans (Point.add_self_of_Y_eq (by simp [negY,genusCurve]))
  refine ⟨P,hP,?_,?_⟩
  · rw [show 4 = 2*2 by decide,mul_nsmul,hdouble,htwo]
  · intro h
    rcases (onePlusI_cube_kernel P).mp h with e | e
    · exact Point.some_ne_zero _ (hdouble.symm.trans e)
    · have e' : Point.some t 0 htNS = twiceCusp := hdouble.symm.trans e
      exact ht0 (Point.some.inj e').1

/-- Exclusion of √2 is equivalent to control of four-torsion, and
suffices for the entire two-primary subgroup. -/
theorem sqrtTwo_not_mem_iff_four {F : SubfieldQ} (hi : Rank.sqrtMinus 1 ∈ F) :
    sqrtDivisor 2 ∉ F ↔ ∀ P ∈ pointsOver F, (4:ℕ) • P = 0 →
      onePlusI (onePlusI (onePlusI P)) = 0 := by
  refine ⟨fun h _ hP h4 => gaussian_of_four h hP h4,?_⟩
  intro h hr
  obtain ⟨P,hP,h4,hn⟩ := nonGaussian_four_of_sqrtTwo hi hr
  exact hn (h P hP h4)

end
end ZInQBlueprint.TYZ.Specialization.TraceAction
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.nonGaussian_four_of_sqrtTwo
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.sqrtTwo_not_mem_iff_four
