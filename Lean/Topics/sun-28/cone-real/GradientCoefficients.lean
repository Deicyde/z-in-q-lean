import RowWeight

namespace Sun28.ConeReal
open Sun28.QuadricSieve
noncomputable section

/-- The five coefficients are the directional derivatives for the coordinate axes. -/
def pairing (κ:ℝ) (x h:Coordinates ℝ) :=
  2*x.1.1*h.1.1 + 2*x.1.2*h.1.2 - 2*x.2.1.1*h.2.1.1 - 2*x.2.1.2*h.2.1.2 - 2*κ*x.2.2*h.2.2

theorem along_line (κ:ℝ) (x h:Coordinates ℝ) :
    HasDerivAt (fun t : ℝ => form κ (x+t•h)) (pairing κ x h) 0 := by
  have lin (a b : ℝ) : HasDerivAt (fun t:ℝ=>a+t*b) b 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).mul_const b).const_add a
  have sq (a b : ℝ) : HasDerivAt (fun t:ℝ=>(a+t*b)^2) (2*a*b) 0 := by
    convert! (lin a b).mul (lin a b) using 1
    · ext t; simp [pow_two]
    · simp;ring
  convert! (((((sq x.1.1 h.1.1).add (sq x.1.2 h.1.2)).sub
    ((sq x.2.1.1 h.2.1.1).add (sq x.2.1.2 h.2.1.2))).sub
      ((sq x.2.2 h.2.2).const_mul κ))) using 1
  dsimp [form,rad,pairing]
  ring

theorem directional_deriv (κ:ℝ) (x h:Coordinates ℝ) :
    (fderiv ℝ (form κ) x) h = pairing κ x h := by
  have fd : DifferentiableAt ℝ (form κ) x := by unfold form rad;fun_prop
  have line : HasDerivAt (fun t:ℝ=>x+t•h) h 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const h).const_add x
  have c:=fd.hasFDerivAt.comp_hasDerivAt_of_eq (x:=0) line (by simp)
  exact c.unique (along_line κ x h)

theorem regular_fderiv (κ : ℝ) (j : ℕ) {x : Coordinates ℝ} (hx:x∈tsupport (weight j)) :
    fderiv ℝ (form κ) x ≠ 0 := by
  let h : Coordinates ℝ := (x.1,0)
  have e : (fderiv ℝ (form κ) x) h=2*rad x.1 := by
    rw [directional_deriv];dsimp [pairing,rad,h];ring
  have a:=(support_bounds j hx).1.1
  intro zero
  rw [zero] at e
  simp at e
  linarith

end
end Sun28.ConeReal
#print axioms Sun28.ConeReal.directional_deriv
#print axioms Sun28.ConeReal.regular_fderiv
