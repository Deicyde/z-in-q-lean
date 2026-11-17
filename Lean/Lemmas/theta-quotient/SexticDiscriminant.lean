import DirectCharts
import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-! A fraction-free resultant calculation for the family sextic. All leading
coefficients are cancelled over ℚ[T] before specializing T to a rational. -/
namespace ZInQBlueprint.SexticInvariants
open Polynomial ZInQBlueprint.DirectCharts
noncomputable section
variable {R : Type*} [CommRing R]

private def l4 (t : R) := -(5*t^2+18*t+81)
private def l3 (t : R) := -(5*t^2-4*t+27)
private def l2 (t : R) := 3*(t^3-2*t^2+9*t-12)
private def l1 (t : R) := -(3*t^2-16*t+17)

private def r5 (t : R) : R[X] :=
  C 6*X^5+C (5*(9-t))*X^4+C (36*(3-t))*X^3+C (3*(t^2-32*t+27))*X^2+
    C (12*t*(t-9))*X+C (12*t*(t-3))
private def r4 (t : R) : R[X] :=
  C (l4 t)*X^4+C (-18*(t^2+8*t+27))*X^3+C (3*(t-9)*(t^2+16*t+27))*X^2+
    C (12*t*(t^2+12*t-9))*X+C (12*t*(t+3)*(t+9))
private def r3 (t : R) : R[X] :=
  C (l3 t)*X^3+C (-3*(9*t^2-8*t+63))*X^2+C (-12*(4*t^2-t+27))*X+
    C (-4*t*(7*t+9))
private def r2 (t : R) : R[X] :=
  C (l2 t)*X^2+C (4*(3*t^3-5*t^2+19*t-27))*X+C (12*t*(t^2-t+2))
private def r1 (t : R) : R[X] := C (l1 t)*X+C (-6*(t^2-7*t+8))

private theorem deriv_monic (t : R) : (monicSextic t).derivative = r5 t := by
  have hd : derivative ((C t)^2) = 0 := by rw [← map_pow,derivative_C]
  rw [monic_coeffs]
  simp only [map_add, derivative_X_pow, derivative_C_mul_X_pow, derivative_C_mul_X, derivative_C]
  norm_num [r5,map_ofNat,hd]
  <;> ring

/-- A consecutive pseudo-remainder step, with the padded degrees fixed.
The sign is positive since degree changes by two on each side of the swap. -/
private theorem step (f g h q : R[X]) (k : ℕ) (a b : R)
    (hq : q.natDegree ≤ 1) (hg : g.natDegree ≤ k+1) (hh : h.natDegree ≤ k)
    (he : C a*f = C b*h + g*q) :
    a^(k+1) * resultant f g (k+2) (k+1) =
      b^(k+1)*(g.coeff (k+1))^2 * resultant g h (k+1) k := by
  rw [← resultant_C_mul_left,he,resultant_add_mul_left _ _ _ _ _ (by omega) hg,
    resultant_C_mul_left,resultant_add_left_deg h g k (k+1) 2 hh,resultant_comm h g k (k+1)]
  have e₁ : (-1:R)^((k+1)*2) = 1 := by rw [Nat.mul_comm,pow_mul]; norm_num
  have e₂ : (-1:R)^(k*(k+1)) = 1 := by
    obtain ⟨i,hi⟩ := Nat.two_dvd_mul_add_one k
    rw [hi,pow_mul]; norm_num
  rw [e₁,e₂]; ring

private theorem deg5 (t : R) : (r5 t).natDegree ≤ 5 := by unfold r5; compute_degree
private theorem deg4 (t : R) : (r4 t).natDegree ≤ 4 := by unfold r4; compute_degree
private theorem deg3 (t : R) : (r3 t).natDegree ≤ 3 := by unfold r3; compute_degree
private theorem deg2 (t : R) : (r2 t).natDegree ≤ 2 := by unfold r2; compute_degree
private theorem deg1 (t : R) : (r1 t).natDegree ≤ 1 := by unfold r1; compute_degree

private theorem coeff5 (t : R) : (r5 t).coeff 5 = 6 := by
  simp only [r5,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]; norm_num
private theorem coeff4 (t : R) : (r4 t).coeff 4 = l4 t := by
  simp only [r4,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]; norm_num
private theorem coeff3 (t : R) : (r3 t).coeff 3 = l3 t := by
  simp only [r3,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]; norm_num
private theorem coeff2 (t : R) : (r2 t).coeff 2 = l2 t := by
  simp only [r2,coeff_add,coeff_C_mul_X_pow,coeff_C_mul_X,coeff_C]; norm_num
private theorem coeff1 (t : R) : (r1 t).coeff 1 = l1 t := by
  simp only [r1,coeff_add,coeff_C_mul_X,coeff_C]; norm_num

private theorem step6 (t : R) :
    (36:R)^5 * resultant (monicSextic t) (r5 t) 6 5 = 36 * resultant (r5 t) (r4 t) 5 4 := by
  let q : R[X] := C 6*X+C (9-t)
  have e : C (36:R)*monicSextic t = C 1*r4 t+r5 t*q := by
    rw [monic_coeffs]; simp [r4,r5,l4,q,map_ofNat]; ring
  have hq : q.natDegree ≤ 1 := by dsimp [q]; compute_degree
  have h := step _ _ _ _ 4 _ _ hq (deg5 t) (deg4 t) e
  norm_num [coeff5] at h ⊢; exact h

private theorem step5 (t : R) :
    ((l4 t)^2)^4 * resultant (r5 t) (r4 t) 5 4 =
      (72*t*(t^2+27))^4*(l4 t)^2*resultant (r4 t) (r3 t) 4 3 := by
  let q : R[X] := C (6*l4 t)*X+C (25*t^3-27*t^2+459*t-729)
  have e : C ((l4 t)^2)*r5 t = C (72*t*(t^2+27))*r3 t+r4 t*q := by
    simp [r5,r4,r3,l4,l3,q,map_ofNat]; ring
  have hq : q.natDegree ≤ 1 := by dsimp [q]; compute_degree
  simpa only [show 3+1=4 by decide,coeff4] using step _ _ _ _ 3 _ _ hq (deg4 t) (deg3 t) e

private theorem step4 (t : R) :
    ((l3 t)^2)^3 * resultant (r4 t) (r3 t) 4 3 =
      ((l4 t)^2)^3*(l3 t)^2*resultant (r3 t) (r2 t) 3 2 := by
  let q : R[X] := C (l3 t*l4 t)*X+C (-3*(t-3)*(15*t^3-49*t^2-27*t-243))
  have e : C ((l3 t)^2)*r4 t = C ((l4 t)^2)*r2 t+r3 t*q := by
    simp [r4,r3,r2,l4,l3,l2,q,map_ofNat]; ring
  have hq : q.natDegree ≤ 1 := by dsimp [q]; compute_degree
  simpa only [show 2+1=3 by decide,coeff3] using step _ _ _ _ 2 _ _ hq (deg3 t) (deg2 t) e

private theorem step3 (t : R) :
    ((l2 t)^2)^2 * resultant (r3 t) (r2 t) 3 2 =
      (4*t*(l3 t)^2)^2*(l2 t)^2*resultant (r2 t) (r1 t) 2 1 := by
  let q : R[X] := C (l3 t*l2 t)*X+C (-21*t^5+86*t^4-656*t^3+1370*t^2-3483*t+3888)
  have e : C ((l2 t)^2)*r3 t = C (4*t*(l3 t)^2)*r1 t+r2 t*q := by
    simp [r3,r2,r1,l3,l2,l1,q,map_ofNat]; ring
  have hq : q.natDegree ≤ 1 := by dsimp [q]; compute_degree
  simpa only [show 1+1=2 by decide,coeff2] using step _ _ _ _ 1 _ _ hq (deg2 t) (deg1 t) e

private theorem step2 (t : R) :
    (l1 t)^2 * resultant (r2 t) (r1 t) 2 1 =
      (4*(l2 t)^2)*(l1 t)^2 := by
  let q : R[X] := C (l1 t*l2 t)*X+C (-2*(9*t^5-45*t^4+97*t^3-121*t^2+106*t-54))
  have e : C ((l1 t)^2)*r2 t = C (4*(l2 t)^2)*C (1:R)+r1 t*q := by
    simp [r2,r1,l2,l1,q,map_ofNat]; ring
  have hq : q.natDegree ≤ 1 := by dsimp [q]; compute_degree
  have h := step _ _ _ _ 0 _ _ hq (deg1 t) (show (C (1:R)).natDegree ≤ 0 by simp) e
  simpa [coeff1, resultant_C_zero_right] using h

private theorem generic [IsDomain R] [CharZero R] (t : R)
    (hn₁ : l1 t ≠ 0) (hn₂ : l2 t ≠ 0) (hn₃ : l3 t ≠ 0) (hn₄ : l4 t ≠ 0) :
    resultant (monicSextic t) (r5 t) 6 5 = 1024*t^6*(t^2+27)^4 := by
  have h2 : resultant (r2 t) (r1 t) 2 1 = 4*(l2 t)^2 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hn₁)
    linear_combination step2 t
  have h3 : resultant (r3 t) (r2 t) 3 2 = 64*t^2*(l3 t)^4 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 (pow_ne_zero 2 hn₂))
    have h := step3 t; rw [h2] at h; linear_combination h
  have h4 : resultant (r4 t) (r3 t) 4 3 = 64*t^2*(l4 t)^6 := by
    apply mul_left_cancel₀ (pow_ne_zero 3 (pow_ne_zero 2 hn₃))
    have h := step4 t; rw [h3] at h; linear_combination h
  have h5 : resultant (r5 t) (r4 t) 5 4 = 1719926784*t^6*(t^2+27)^4 := by
    apply mul_left_cancel₀ (pow_ne_zero 4 (pow_ne_zero 2 hn₄))
    have h := step5 t; rw [h4] at h; linear_combination h
  apply mul_left_cancel₀ (pow_ne_zero 5 (by norm_num : (36:R) ≠ 0))
  have h := step6 t
  rw [h5] at h
  linear_combination h

/-- The universal resultant is computed in the coefficient ring ℚ[T]. The
four nonzero pivots may be checked at T = 0, independently of the eventual
value at which the discriminant will be specialized. -/
private theorem universal :
    resultant (monicSextic (X : ℚ[X])) (r5 X) 6 5 = 1024*X^6*(X^2+27)^4 := by
  let t : ℚ[X] := X
  have hn₁ : l1 t ≠ 0 := by
    intro h; have e := congrArg (fun p : ℚ[X] => p.eval 0) h
    norm_num [l1,t] at e
  have hn₂ : l2 t ≠ 0 := by
    intro h; have e := congrArg (fun p : ℚ[X] => p.eval 0) h
    norm_num [l2,t] at e
  have hn₃ : l3 t ≠ 0 := by
    intro h; have e := congrArg (fun p : ℚ[X] => p.eval 0) h
    norm_num [l3,t] at e
  have hn₄ : l4 t ≠ 0 := by
    intro h; have e := congrArg (fun p : ℚ[X] => p.eval 0) h
    norm_num [l4,t] at e
  exact generic t hn₁ hn₂ hn₃ hn₄

/-- The actual resultant of the monic sextic with its derivative. -/
theorem resultant_monic_family (t : ℚ) :
    resultant (monicSextic t) (monicSextic t).derivative 6 5 = 1024*t^6*(t^2+27)^4 := by
  let φ := evalRingHom t
  have e := congrArg (fun p : ℚ[X] => φ p) universal
  rw [← resultant_map_map] at e
  have hf : (monicSextic (X : ℚ[X])).map φ = monicSextic t := by
    simp [monic_coeffs,φ]
  have hg : (r5 (X : ℚ[X])).map φ = r5 t := by simp [r5,φ]
  rw [hf,hg] at e
  rw [deriv_monic]
  simpa [φ] using e

theorem discr_monic_family (t : ℚ) :
    (monicSextic t).discr = -1024*t^6*(t^2+27)^4 := by
  obtain ⟨hm,hd⟩ := monic_six t
  have hp : 0 < (monicSextic t).degree := natDegree_pos_iff_degree_pos.mp (by rw [hd]; decide)
  have he := resultant_deriv hp
  rw [hd,hm.leadingCoeff] at he
  norm_num at he
  rw [resultant_monic_family] at he
  linarith

/-- A scalar twist of a sextic has its discriminant multiplied by s¹⁰. -/
theorem discr_family (s t : ℚ) (hs : s ≠ 0) :
    (C s*monicSextic t).discr = -1024*s^10*t^6*(t^2+27)^4 := by
  obtain ⟨hm,hd⟩ := monic_six t
  have hd' : (C s*monicSextic t).natDegree = 6 := (natDegree_C_mul hs).trans hd
  have hp : 0 < (C s*monicSextic t).degree := natDegree_pos_iff_degree_pos.mp (by rw [hd']; decide)
  have he := resultant_deriv hp
  rw [hd', leadingCoeff_mul_monic hm, leadingCoeff_C,derivative_C_mul] at he
  norm_num only at he
  rw [resultant_C_mul_left, resultant_C_mul_right,resultant_monic_family] at he
  apply mul_left_cancel₀ hs
  linear_combination he

end
end ZInQBlueprint.SexticInvariants
#print axioms ZInQBlueprint.SexticInvariants.resultant_monic_family
#print axioms ZInQBlueprint.SexticInvariants.discr_monic_family
#print axioms ZInQBlueprint.SexticInvariants.discr_family
