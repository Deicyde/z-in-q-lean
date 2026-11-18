import PicardLocal
import PicardSextic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Tactic.ComputeDegree

/-! The discriminant of the Picard sextic, computed using its quadratic
and quartic factors. The result uses Mathlib's polynomial discriminant. -/
namespace ZOverQ.Qualitative.Picard

open Polynomial PicardLocal
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

private def linear : K[X] := 2 * X - 1

private lemma linear_eq : (linear : K[X]) = C 2 * (X - C (1/2 : K)) := by
  rw [mul_sub, ← map_mul]
  norm_num [linear, map_ofNat]

private lemma q_deg : (quadratic : K[X]).natDegree = 2 := by
  unfold quadratic
  compute_degree!

private lemma g_deg (U V : K) (hV : V ≠ 0) : (quartic U V).natDegree = 4 := by
  unfold quartic
  compute_degree!

private lemma q_coeff : (quadratic : K[X]).coeff 2 = 1 := by
  unfold quadratic
  compute_degree!

private lemma g_coeff (U V : K) : (quartic U V).coeff 4 = -V := by
  unfold quartic
  compute_degree!

private lemma linear_deg : (linear : K[X]).natDegree = 1 := by
  unfold linear
  compute_degree!

private lemma res_linear (f : K[X]) (m : ℕ) (hf : f.natDegree ≤ m) :
    resultant f linear m 1 = 2 ^ m * ((-1 : K)^m * f.eval (1/2)) := by
  rw [linear_eq, resultant_C_mul_right, resultant_X_sub_C_right _ _ _ hf]

private lemma q_linear : resultant (quadratic : K[X]) linear 2 1 = -3 := by
  rw [res_linear _ _ q_deg.le]
  norm_num [quadratic]

private lemma g_linear (U V : K) (hV : V ≠ 0) :
    resultant (quartic U V) linear 4 1 = -9*V := by
  rw [res_linear _ _ (g_deg U V hV).le, quartic_eval]
  ring

private lemma res_qg (U V : K) :
    resultant quadratic (quartic U V) 2 4 = -48 * (U-V)^2 := by
  let q : K[X] := quadratic
  have reduce : quartic U V = C (4*(U-V)) * linear + q * (-C V * q) := by
    rw [quartic_contact]; simp [q,linear,map_ofNat]; ring
  have deg : (-C V * q).natDegree ≤ 2 := by unfold q quadratic; compute_degree
  rw [reduce, resultant_add_mul_right _ _ _ _ _ (by omega) q_deg.le, resultant_C_mul_right]
  rw [show 4 = 1+3 by decide, resultant_add_right_deg _ _ _ _ _ linear_deg.le, q_coeff, q_linear]
  ring

private lemma res_gq (U V : K) : resultant (quartic U V) quadratic 4 2 = -48 * (U-V)^2 := by
  rw [resultant_comm, res_qg]
  norm_num

omit [CharZero K] in
private lemma q_deriv : (quadratic : K[X]).derivative = 2*X+2 := by
  simp [quadratic, derivative_pow,map_ofNat]

omit [CharZero K] in
private lemma g_deriv (U V : K) :
    (quartic U V).derivative = C (8*U) - C (4*V)*X^2*(X+3) := by
  simp [quartic, derivative_pow,map_ofNat]; ring

private lemma g_deriv_deg (U V : K) (hV : V ≠ 0) :
    (quartic U V).derivative.natDegree = 3 := by
  rw [g_deriv]; compute_degree!

private lemma res_q_q' : resultant (quadratic : K[X]) quadratic.derivative 2 1 = -12 := by
  have h : (quadratic : K[X]).derivative = C 2 * (X + C 1) := by rw [q_deriv]; simp [map_ofNat]; ring
  rw [h, resultant_C_mul_right, resultant_X_add_C_right _ _ _ q_deg.le]
  norm_num [quadratic]

private lemma res_g_g' (U V : K) (hV : V ≠ 0) :
    resultant (quartic U V) (quartic U V).derivative 4 3 = 110592*U^2*V^3*(U-V)^2 := by
  let g := quartic U V
  let q : K[X] := quadratic
  have gd : g.natDegree = 4 := g_deg U V hV
  have dd : g.derivative.natDegree = 3 := g_deriv_deg U V hV
  have id : linear * g.derivative = C (-6*V)*(X^2*q) + g*C 2 := by
    dsimp only [g,q]
    rw [g_deriv]
    simp [linear,quartic,quadratic,map_ofNat]
    ring
  have res := congrArg (fun f : K[X] => resultant g f 4 4) id
  have lhs := resultant_mul_right g linear g.derivative 4 gd.le
  rw [linear_deg, dd] at lhs
  have rhs := resultant_mul_right g (X^2) q 4 gd.le
  rw [natDegree_X_pow, show q.natDegree = 2 from q_deg] at rhs
  rw [lhs, resultant_add_mul_right _ _ _ _ _ (by simp) gd.le, resultant_C_mul_right, rhs,
      resultant_X_pow_right _ _ _ gd.le, g_linear U V hV, res_gq] at res
  have gc : g.coeff 0 = -4*U := by rw [coeff_zero_eq_eval_zero, quartic_eval]; ring
  rw [gc] at res
  apply mul_left_cancel₀ (show -9*V ≠ 0 by exact mul_ne_zero (by norm_num) hV)
  calc
    -9*V * resultant g g.derivative 4 3 = _ := res
    _ = _ := by ring

private lemma res_sextic (U V : K) (hV : V ≠ 0) :
    resultant (sextic U V) (sextic U V).derivative 6 5 =
      -(2:K)^22*3^6*U^2*V^3*(U-V)^6 := by
  let q : K[X] := quadratic
  let g := quartic U V
  have qd : q.natDegree = 2 := q_deg
  have gd : g.natDegree = 4 := g_deg U V hV
  have qd' : q.derivative.natDegree = 1 := by dsimp only [q]; rw [q_deriv]; compute_degree!
  have gd' : g.derivative.natDegree = 3 := g_deriv_deg U V hV
  have fd : (q*g).natDegree = 6 := by
    rw [natDegree_mul (by intro h; simp [h] at qd) (by intro h; simp [h] at gd), qd, gd]
  have deriv := natDegree_derivative_le (q*g)
  have dh : (q*g).derivative.natDegree ≤ 5 := by simpa [fd] using deriv
  change resultant (q*g) (q*g).derivative 6 5 = _
  have split := resultant_mul_left q g (q*g).derivative 5 dh
  rw [qd, gd] at split
  rw [split, derivative_mul, resultant_add_mul_right _ _ _ _ _ (by omega) qd.le]
  rw [show q.derivative*g+q*g.derivative = q*g.derivative+g*q.derivative by ring,
    resultant_add_mul_right _ _ _ _ _ (by omega) gd.le]
  have a := resultant_mul_right q q.derivative g 2 qd.le
  rw [qd',gd] at a
  have b := resultant_mul_right g q g.derivative 4 gd.le
  rw [qd,gd'] at b
  rw [a,b,res_q_q',res_qg,res_gq,res_g_g' U V hV]
  ring

/-- Actual discriminant in every characteristic-zero coefficient field.
The leading coefficient is −V, so V ≠ 0 is the sextic degree condition. -/
theorem discr_sextic (U V : K) (hV : V ≠ 0) :
    (sextic U V).discr = discriminantValue U V := by
  have qd : (quadratic : K[X]).natDegree = 2 := q_deg
  have gd := g_deg U V hV
  have nq : (quadratic : K[X]) ≠ 0 := by intro h; simp [h] at qd
  have ng : quartic U V ≠ 0 := by intro h; simp [h] at gd
  have sd : (sextic U V).natDegree = 6 := by
    rw [sextic, natDegree_mul nq ng, qd, gd]
  have lc : (sextic U V).leadingCoeff = -V := by
    rw [sextic, leadingCoeff_mul, leadingCoeff, leadingCoeff, qd, gd, q_coeff, g_coeff, one_mul]
  have e := resultant_deriv (f := sextic U V) (natDegree_pos_iff_degree_pos.mp (by rw [sd]; decide))
  rw [sd, lc] at e
  norm_num at e
  apply mul_left_cancel₀ hV
  rw [← e, res_sextic _ _ hV]
  unfold discriminantValue
  ring

theorem ratio_eq_discriminant (U V : K) (hV : V ≠ 0) :
    ratio U V = (secondInvariant (coefficients U V))^5/(sextic U V).discr := by
  rw [discr_sextic _ _ hV]; rfl

/-- The invariant of the actual genus-two equation, with Mathlib's
discriminant, specialized to the geometric fibre used in the height bound. -/
theorem invariant_at (ρ : K) (hρ : ρ^2 = -3) {t : ℚ} (ht : t ∉ ZInQ.contactSet) :
    let s := (ZInQ.QualitativeHeight.picardParameter t : K)
    let U := (s+ρ)^6
    let V := (s-ρ)^6
    (secondInvariant (coefficients U V))^5 / (sextic U V).discr =
      (((ZInQ.JHeight.Jmap t + 4)^5 / (200000*(ZInQ.JHeight.Jmap t)^3) : ℚ) : K) := by
  dsimp only
  let s := ZInQ.QualitativeHeight.picardParameter t
  have pos : s^2+3 ≠ 0 := by positivity
  have hn : (s:K)^2+3 ≠ 0 := by exact_mod_cast pos
  have hp := sixth_product (s:K) ρ hρ
  have hV : ((s:K)-ρ)^6 ≠ 0 :=
    (mul_ne_zero_iff.mp (hp.trans_ne (pow_ne_zero _ hn))).2
  exact (ratio_eq_discriminant _ _ hV).symm.trans (ratio_at ρ hρ ht)

end
end ZOverQ.Qualitative.Picard

#print axioms ZOverQ.Qualitative.Picard.discr_sextic
#print axioms ZOverQ.Qualitative.Picard.ratio_eq_discriminant

#print axioms ZOverQ.Qualitative.Picard.invariant_at
