import PositiveDivisors

namespace Sun28.PointLifts
noncomputable section

private theorem direction_square {k : Type*} [Field k] {c X Y : k}
    (prim : X≠0 ∨ Y≠0) (eqn : X^2=c*Y^2) : IsSquare c := by
  have yn : Y≠0 := by
    intro zero
    have h : X^2=0 := by simpa [zero] using eqn
    exact (pow_ne_zero 2 (prim.resolve_right (not_not_intro zero))) h
  refine ⟨X/Y,?_⟩
  field_simp
  linear_combination -eqn

/-- Only split primes of the corresponding binary quadratic form can enter
the common squarefree divisor from the numerator or denominator of the ratio. -/
theorem divisor_root_tests {p : ℕ} [Fact p.Prime] {b θ n m U V D x : ℤ}
    (cop : U.natAbs.Coprime V.natAbs) (f : leftForm b (n^2) (θ*m^2) U V=D*x^2)
    (pd : (D:ZMod p)=0) :
    (((n:ZMod p)=0 ∧ (θ:ZMod p)*(m:ZMod p)^2≠0) → IsSquare (b:ZMod p)) ∧
    (((θ:ZMod p)*(m:ZMod p)^2=0 ∧ (n:ZMod p)≠0) → IsSquare (-3*(b:ZMod p))) := by
  have h := congrArg (fun t:ℤ => (t:ZMod p)) f
  push_cast [leftForm] at h
  rw [pd,zero_mul] at h
  constructor
  · rintro ⟨nz,dn⟩
    apply direction_square (primitive_mod cop)
    apply mul_left_cancel₀ dn
    rw [nz] at h
    linear_combination -h
  · rintro ⟨dz,nn⟩
    apply direction_square (primitive_mod cop)
    apply mul_left_cancel₀ (pow_ne_zero 2 nn)
    rw [dz] at h
    linear_combination h

end
end Sun28.PointLifts
#print axioms Sun28.PointLifts.divisor_root_tests
