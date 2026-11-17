import TYZTraceRank

/-! The subgroup A[(1+i)^3] on the integral TYZ model is defined over Q(i).
Here (1+i)^2=2i, so its kernel is the preimage under doubling of A[1+i]. -/
namespace ZInQBlueprint.TYZ.Specialization.TraceAction
noncomputable section
attribute [local instance] Classical.decEq
open WeierstrassCurve.Affine

private abbrev i := Rank.sqrtMinus 1
private abbrev F := Rank.imaginaryField 1
private theorem i_sq : i^2 = -1 := by simpa [i] using Rank.sqrtMinus_sq 1
private theorem i_mem : i ∈ F := IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

private def coords : A → Option (K × K)
  | .zero => none
  | .some x y _ => some (x,y)

private theorem nonvertical {x y : K} (hy : y ≠ 0) : y ≠ genusCurve.toAffine.negY x y := by
  intro e
  simp [negY, genusCurve] at e
  exact hy (by linear_combination e / 2)

private theorem torsion_y {x y : K} (h : genusCurve.toAffine.Nonsingular x y)
    (hP : (2:ℕ) • (.some x y h : A) = 0) : y = 0 := by
  by_contra hy
  rw [two_nsmul,Point.add_self_of_Y_ne (nonvertical hy)] at hP
  exact Point.some_ne_zero _ hP

theorem two_torsion_gaussian {P : A} (hP : (2:ℕ) • P = 0) : P ∈ pointsOver F := by
  cases P with
  | zero => exact (pointsOver F).zero_mem
  | some x y h =>
    obtain rfl := torsion_y h hP
    apply (some_mem_pointsOver F _ _ h).mpr
    refine ⟨?_, F.zero_mem⟩
    have eq : (0:K)^2 = x^3+4*x := by simpa [equation_iff,genusCurve] using h.1
    have fac : x * ((x-2*i)*(x+2*i)) = 0 := by linear_combination -eq - 4*x*i_sq
    rcases mul_eq_zero.mp fac with h0 | h1
    · rw [h0]; exact F.zero_mem
    · rcases mul_eq_zero.mp h1 with hp | hn
      · rw [sub_eq_zero.mp hp]; exact F.mul_mem (F.natCast_mem 2) i_mem
      · rw [eq_neg_of_add_eq_zero_left hn]; exact F.neg_mem (F.mul_mem (F.natCast_mem 2) i_mem)

private theorem half_cusp_x {x y : K} (h : genusCurve.toAffine.Nonsingular x y)
    (hP : (2:ℕ) • (.some x y h : A) = twiceCusp) : x^2 = 4 := by
  have hy : y ≠ 0 := by
    rintro rfl
    rw [two_nsmul, Point.add_self_of_Y_eq (by simp [negY,genusCurve])] at hP
    exact twiceCusp_ne_zero hP.symm
  have e := congrArg coords hP
  rw [two_nsmul, Point.add_self_of_Y_ne (nonvertical hy)] at e
  have ex := (Prod.mk.inj (Option.some.inj e)).1
  change genusCurve.toAffine.addX x x (genusCurve.toAffine.slope x x y y) = 0 at ex
  rw [slope_of_Y_ne rfl (nonvertical hy)] at ex
  simp [addX,negY,genusCurve] at ex
  field_simp [hy] at ex
  have eq : y^2 = x^3+4*x := by simpa [equation_iff,genusCurve] using h.1
  have zero : (x^2-4)^2 = 0 := by linear_combination ex + 8*x*eq
  exact sub_eq_zero.mp (pow_eq_zero_iff (by decide : 2 ≠ 0) |>.mp zero)

theorem halves_of_cusp_gaussian {P : A} (hP : (2:ℕ) • P = twiceCusp) : P ∈ pointsOver F := by
  cases P with
  | zero => exact (pointsOver F).zero_mem
  | some x y h =>
    have hx : x^2 = (2:K)^2 := (half_cusp_x h hP).trans (by norm_num)
    have eq : y^2 = x^3+4*x := by simpa [equation_iff,genusCurve] using h.1
    apply (some_mem_pointsOver F _ _ h).mpr
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hx with rfl | rfl
    · refine ⟨F.natCast_mem 2,?_⟩
      have hy : y^2 = (4:K)^2 := by linear_combination eq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with rfl | rfl
      · exact F.natCast_mem 4
      · exact F.neg_mem (F.natCast_mem 4)
    · refine ⟨F.neg_mem (F.natCast_mem 2),?_⟩
      have hy : y^2 = (4*i)^2 := by linear_combination eq - 16*i_sq
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hy with rfl | rfl
      · exact F.mul_mem (F.natCast_mem 4) i_mem
      · exact F.neg_mem (F.mul_mem (F.natCast_mem 4) i_mem)

theorem one_plus_i_kernel (P : A) : P + multiplyI P = 0 ↔ P = 0 ∨ P = twiceCusp := by
  constructor
  · intro zero
    have hneg : multiplyI P = -P := eq_neg_of_add_eq_zero_right zero
    cases P with
    | zero => exact Or.inl rfl
    | some x y h =>
      right
      have H := congrArg coords hneg
      change some ((-(Rank.sqrtMinus 1))^2*x, (-(Rank.sqrtMinus 1))^3*y) =
        some (x,genusCurve.toAffine.negY x y) at H
      have hx := (Prod.mk.inj (Option.some.inj H)).1
      have hx0 : x = 0 := by
        rw [neg_sq,i_sq] at hx
        linear_combination -hx / 2
      subst x
      have hy : y^2 = (0:K) := by simpa [equation_iff,genusCurve] using h.1
      obtain rfl := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp hy
      rfl
  · rintro (rfl | rfl)
    · simp
    · have hc : multiplyI twiceCusp = twiceCusp := unitHom_cusp .i
      rw [hc, ←two_nsmul, twice_twiceCusp]

def onePlusI : A →+ A := AddMonoidHom.id A + multiplyI

private theorem i_square (P : A) : multiplyI (multiplyI P) = -P := by
  cases P with
  | zero =>
    change multiplyI (multiplyI (0:A)) = -(0:A)
    simp
  | some x y h =>
    change Point.some ((-i)^2*((-i)^2*x)) ((-i)^3*((-i)^3*y)) _ =
      Point.some x (genusCurve.toAffine.negY x y) _
    erw [Point.some.injEq]
    have hc : (-i)^3=i := by linear_combination -i*i_sq
    rw [hc,neg_sq,i_sq]
    constructor
    · ring
    · simp only [negY,genusCurve,WeierstrassCurve.toAffine,zero_mul,sub_zero]
      linear_combination y*i_sq

theorem onePlusI_cube_kernel (P : A) :
    onePlusI (onePlusI (onePlusI P)) = 0 ↔ (2:ℕ) • P = 0 ∨ (2:ℕ) • P = twiceCusp := by
  have pure (Q : A) : onePlusI (onePlusI Q) = multiplyI ((2:ℕ) • Q) := by
    change Q + multiplyI Q + multiplyI (Q + multiplyI Q) = _
    rw [map_add,i_square,map_nsmul,two_nsmul]
    abel
  rw [pure]
  have distrib : (2:ℕ) • onePlusI P = onePlusI ((2:ℕ) • P) := (map_nsmul _ _ _).symm
  rw [distrib]
  have inject : ∀ Q : A, multiplyI Q = 0 ↔ Q = 0 := by
    intro Q
    refine ⟨fun hz => ?_,fun hz => by simp [hz]⟩
    have hh := i_square Q
    rw [hz,map_zero] at hh
    exact neg_eq_zero.mp hh.symm
  rw [inject]
  exact one_plus_i_kernel _

/-- The odd-compositum conclusion of TYZ 3.18 supplies both the field and the
exponent needed in the trace argument. -/
theorem gaussian_torsion {P : A} (h : onePlusI (onePlusI (onePlusI P)) = 0) :
    P ∈ pointsOver F ∧ (4:ℕ) • P = 0 := by
  rcases (onePlusI_cube_kernel P).mp h with z | c
  · exact ⟨two_torsion_gaussian z, by rw [show 4=2*2 by decide,mul_nsmul,z,nsmul_zero]⟩
  · exact ⟨halves_of_cusp_gaussian c, by rw [show 4=2*2 by decide,mul_nsmul,c,twice_twiceCusp]⟩

end
end ZInQBlueprint.TYZ.Specialization.TraceAction
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.two_torsion_gaussian
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.halves_of_cusp_gaussian
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.one_plus_i_kernel
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.onePlusI_cube_kernel
#print axioms ZInQBlueprint.TYZ.Specialization.TraceAction.gaussian_torsion
