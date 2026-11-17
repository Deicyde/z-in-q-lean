import LabelledModuliField

/-! Coordinates on the discriminant-six conic of Baba and Granath.
On the chart x=4 the quotient by w₃ is [y:z]. For the present family,
every lift with this parameter gives a rational quotient point. -/
open CategoryTheory AlgebraicGeometry
namespace ZInQBlueprint.ThetaClass
open CoarseConic SixContact NormalDescent
noncomputable section

/-- The coordinate 3z/y generates the marked field in Theorem 3.17.
The equations admit all signs of y and z. -/
theorem marked_quotient_coordinate {u : ℚ} (hu : u ∉ ZInQ.contactSet) {y z : Qbar}
    (hy : y^2 = 9*(SixContact.J u : Qbar)) (hz : z^2 = -27*(SixContact.J u : Qbar)-16) :
    y ≠ 0 ∧ (3*z/y)^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar) ∧
      ∃ a : ℚ, (a : Qbar) = 3*z/y ∧
        (a = 4*h u/r u ∨ a = -(4*h u/r u)) := by
  have hj : (SixContact.J u : Qbar) ≠ 0 := by exact_mod_cast (unmarked_range hu).2.ne
  have yn : y ≠ 0 := by rintro rfl; simp [hj] at hy
  have square : (3*z/y)^2 = ((-(27*SixContact.J u+16)/SixContact.J u : ℚ) : Qbar) := by
    push_cast
    rw [div_pow,mul_pow,hy,hz]
    field_simp
    ring
  refine ⟨yn,square,?_⟩
  rw [RealMultiplication.real_coordinate] at square
  push_cast at square
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp square with eq|eq
  · exact ⟨4*h u/r u,by push_cast; exact eq.symm,Or.inl rfl⟩
  · exact ⟨-(4*h u/r u),by push_cast; exact eq.symm,Or.inr rfl⟩

/-- Any parameter s of the printed sextic comes from the signed comparison
by taking d=s/r and a square root of its ordinate rescaling. -/
theorem lift_printed_parameter {u : ℚ} (hu : u ∉ ZInQ.contactSet) {s : Qbar}
    (hs : s^2 = -6*(SixContact.J u : Qbar)) :
    ∃ (d : Qbar) (_ : d^2=6) (v : Qbar), v^2=PrintedModel.factor u d ∧
      PrintedModel.argument u d = s ∧ 9*s^2-32 = -2*(27*(SixContact.J u : Qbar)+16) := by
  have rn : (r u : Qbar) ≠ 0 := by exact_mod_cast (radical_units hu).1
  have je : (SixContact.J u : Qbar) = -(r u : Qbar)^2 := by exact_mod_cast first_square u
  let d := s / (r u : Qbar)
  have hd : d^2 = 6 := by
    dsimp [d]
    rw [div_pow,hs,je]
    field_simp
  obtain ⟨v,hv⟩ := IsAlgClosed.exists_pow_nat_eq (PrintedModel.factor u d) (by decide : 0<2)
  exact ⟨d,hd,v,hv,div_mul_cancel₀ s rn,by linear_combination 9*hs⟩

end
end ZInQBlueprint.ThetaClass
#print axioms ZInQBlueprint.ThetaClass.marked_quotient_coordinate
#print axioms ZInQBlueprint.ThetaClass.lift_printed_parameter
