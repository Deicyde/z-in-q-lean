import RootOrdinate

namespace ProgressionWitnesses.GeneralOrdinate
open PhysicalProjection.Comparison
open PhysicalProjection.RootOrdinate (equation ordinate ordinate_iff ordinate_from_equation)

/-- Cubing a reduced rational already gives a reduced cubed numerator. -/
theorem two_not_cube (x : Rat) : x^3 ≠ 2 := by
  intro h
  have n : x.num^3 = (2:Int) := congrArg Rat.num h
  have size : x.num.natAbs^3 = 2 := by
    simpa only [Int.natAbs_pow] using congrArg Int.natAbs n
  by_cases small : x.num.natAbs ≤ 1
  · have bd := Nat.pow_le_pow_left small 3
    omega
  · have bd := Nat.pow_le_pow_left (show 2 ≤ x.num.natAbs by omega) 3
    omega

theorem cubic_zero_iff (a b : Rat) : a^3+2*b^3=0 ↔ a=0 ∧ b=0 := by
  constructor
  · intro h
    by_cases hb : b=0
    · subst b
      exact ⟨by grind, rfl⟩
    · let x := (-a)/b
      have xb : x*b = -a := Rat.div_mul_cancel hb
      have h0 : (x^3-2)*b^3=0 := by
        calc (x^3-2)*b^3 = (x*b)^3-2*b^3 := by grobner
             _ = 0 := by rw [xb]; grobner
      have hz : x^3-2=0 := (Rat.mul_eq_zero.mp h0).resolve_right (by grind)
      exact False.elim (two_not_cube x (by grobner))
  · rintro ⟨rfl,rfl⟩; grobner

def multiplier (C : Q2) : Q2 := (2*C.1-C.2,C.1-C.2)
def target (C : Q2) : Q2 := times (sq (multiplier C)) C
def inverse (m : Q2) : Q2 := (m.1*(norm m)⁻¹, -m.2*(norm m)⁻¹)
def decode (C : Q2) (u : Rat) : Q2 := times (inverse (multiplier C)) (ordinate (target C) u)

theorem norm_multiplier (C : Q2) : norm (multiplier C) = 2*C.1^2-C.2^2 := by
  dsimp [norm,multiplier]; grobner

theorem real_multiplier (y : Q2) : (times (multiplier (sq y)) y).1=2*(y.1^3+2*y.2^3) := by
  dsimp [multiplier,sq,times]; grobner

theorem real_nonzero {y : Q2} (hy : y ≠ (0,0)) : (times (multiplier (sq y)) y).1≠0 := by
  rw [real_multiplier]
  intro eqn
  have h := (cubic_zero_iff y.1 y.2).mp ((Rat.mul_eq_zero.mp eqn).resolve_left (by decide))
  exact hy (Prod.ext h.1 h.2)

private theorem norm_nonzero {C : Q2} (hC : C ≠ (0,0)) : norm (multiplier C) ≠ 0 := by
  rw [norm_multiplier]
  intro eqn
  have h := (CircuitTransport.Quadratic.norm_zero_iff C.2 C.1).mp (by
    dsimp [CircuitTransport.Quadratic.norm]; grobner)
  exact hC (Prod.ext h.2 h.1)

private theorem product_square (x y : Q2) : sq (times x y) = times (sq x) (sq y) := by
  apply Prod.ext <;> dsimp [sq,times] <;> grobner

private theorem mul_assoc (x y z : Q2) : times (times x y) z = times x (times y z) := by
  apply Prod.ext <;> dsimp [times] <;> grobner

private theorem one_left (x : Q2) : times (1,0) x=x := by
  apply Prod.ext <;> dsimp [times] <;> grobner

private theorem inv_left (m : Q2) (hn : norm m ≠ 0) : times (inverse m) m=(1,0) := by
  apply Prod.ext
  · calc (times (inverse m) m).1=(norm m)⁻¹*norm m := by
           dsimp [times,inverse,norm]; grobner
         _ = 1 := Rat.inv_mul_cancel _ hn
  · dsimp [times,inverse]; grobner

private theorem square_nonzero {y : Q2} (hy : y ≠ (0,0)) : sq y ≠ (0,0) := by
  intro eqn
  have h := real_nonzero hy
  rw [eqn] at h
  apply h
  dsimp [multiplier,times]; grobner

/-- A scalar parameter for either specified sign of a nonzero ordinate. -/
theorem encode (y : Q2) (hy : y ≠ (0,0)) :
    ∃ u : Rat, equation (target (sq y)) u=0 ∧ decode (sq y) u=y := by
  let m := multiplier (sq y)
  let z := times m y
  let u := z.1⁻¹
  have nz : z.1 ≠ 0 := real_nonzero hy
  have sqz : sq z=target (sq y) := product_square m y
  have code := (ordinate_iff (target (sq y)) z u).mp ⟨sqz, Rat.inv_mul_cancel _ nz⟩
  refine ⟨u, code.1, ?_⟩
  change times (inverse m) (ordinate (target (sq y)) u)=y
  rw [←code.2]
  change times (inverse m) (times m y)=y
  rw [←mul_assoc, inv_left m (norm_nonzero (square_nonzero hy)), one_left]

/-- A root of the scalar quartic itself rules out C=0 and decodes to a true nonzero ordinate. -/
theorem decode_spec {C : Q2} {u : Rat} (eqn : equation (target C) u=0) :
    sq (decode C u)=C ∧ decode C u ≠ (0,0) := by
  have hC : C≠(0,0) := by
    rintro rfl
    dsimp [equation,target,multiplier,sq,times] at eqn
    grobner
  have hn := norm_nonzero hC
  let m := multiplier C
  have z := (ordinate_from_equation (target C) u eqn).1
  have root : sq (decode C u)=C := by
    unfold decode
    rw [product_square,z]
    change times (sq (inverse m)) (times (sq m) C)=C
    rw [←mul_assoc,←product_square,inv_left m hn]
    change times (times (1,0) (1,0)) C=C
    rw [one_left,one_left]
  refine ⟨root,?_⟩
  intro hy
  rw [hy] at root
  exact hC (root.symm.trans (by apply Prod.ext <;> dsimp [sq,times] <;> grobner))

/-- Without any hypothesis on C, the equation parametrizes exactly the nonzero square fibres. -/
theorem projection (C : Q2) :
    (∃ y : Q2, y≠(0,0) ∧ sq y=C) ↔ ∃ u : Rat, equation (target C) u=0 := by
  constructor
  · rintro ⟨y,nz,rfl⟩
    obtain ⟨u,h,_⟩ := encode y nz
    exact ⟨u,h⟩
  · rintro ⟨u,h⟩
    exact ⟨decode C u,(decode_spec h).2,(decode_spec h).1⟩

/-- A finite nonzero-ordinate point on y²=x³-Dx uses the two coordinates of x and one u. -/
theorem finite_curve_chart (D x : Q2) :
    let C := PhysicalProjection.RootOrdinate.sub (times (sq x) x) (times D x)
    (∃ y : Q2, y≠(0,0) ∧ sq y=C) ↔ ∃ u : Rat, equation (target C) u=0 :=
  projection _

#print axioms two_not_cube
#print axioms cubic_zero_iff
#print axioms norm_multiplier
#print axioms real_multiplier
#print axioms real_nonzero
#print axioms encode
#print axioms decode_spec
#print axioms projection
#print axioms finite_curve_chart
end ProgressionWitnesses.GeneralOrdinate
