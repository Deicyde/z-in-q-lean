import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

/-! The Baba–Granath sextic at the generic Gauss residue. -/
namespace ZInQBlueprint.SexticCalibration
open Polynomial
noncomputable section

/-- Baba–Granath, Theorem 3.14, with t=9s²−32. -/
def sextic {R : Type*} [CommRing R] (s : R) : R[X] :=
  let t := 9*s^2-32
  C (-4+3*s)*X^6 + C (6*t)*X^5 + C (3*t*(28+9*s))*X^4 -
    C (4*t^2)*X^3 + C (3*t^2*(28-9*s))*X^2 + C (6*t^3)*X - C (t^3*(4+3*s))

def parameterResultant {R : Type*} [CommRing R] (s : R) : R :=
  resultant (sextic s) (sextic s).derivative 6 5

theorem map_sextic {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K) (s : R) :
    (sextic s).map f = sextic (f s) := by simp [sextic, map_ofNat]

theorem map_parameterResultant {R K : Type*} [CommRing R] [CommRing K] (f : R →+* K) (s : R) :
    f (parameterResultant s) = parameterResultant (f s) := by
  unfold parameterResultant
  rw [← resultant_map_map, ← derivative_map, map_sextic]

private def f6 : ℤ[X] := 2*X^6+24*X^5+552*X^4-64*X^3+480*X^2+384*X-640
private def f5 : ℤ[X] := X^5+10*X^4+184*X^3-16*X^2+80*X+32
private def f4 : ℤ[X] := 3*X^4-16*X^3+8*X^2-16
private def f3 : ℤ[X] := 37*X^3-8*X^2+12*X+16
private def f2 : ℤ[X] := 141*X^2+140*X-356
private def f1 : ℤ[X] := 17*X-11

theorem at_two : sextic (2:ℤ) = 2*X^6+24*X^5+552*X^4-64*X^3+480*X^2+384*X-640 := by
  norm_num [sextic, map_ofNat] <;> ring

private lemma f6_derivative : f6.derivative = C 12 * f5 := by
  simp [f6,f5,derivative_add,derivative_sub,derivative_mul,derivative_X_pow,map_ofNat]
  ring

/-- One fraction-free Euclidean step for the fixed-degree resultant. -/
private lemma resultant_step (i : ℕ) (f g h q : ℤ[X]) (a b : ℤ)
    (relation : C a * f = C b * h + g*q) (hq : q.natDegree ≤ 1)
    (hg : g.natDegree ≤ i + 1) (hh : h.natDegree ≤ i) :
    a^(i+1) * resultant f g (i+2) (i+1) =
      b^(i+1) * ((-1:ℤ)^(i+1)*g.coeff (i+1))^2 * (-1)^(i*(i+1)) *
        resultant g h (i+1) i := by
  calc
    _ = resultant (C a*f) g (i+2) (i+1) := (resultant_C_mul_left ..).symm
    _ = resultant (C b*h) g (i+2) (i+1) := by
      rw [relation, resultant_add_mul_left _ _ _ _ _ (by omega) hg]
    _ = _ := by
      rw [resultant_C_mul_left, resultant_succ_left_deg h g (i+1) (i+1) (by omega),
        resultant_succ_left_deg h g i (i+1) hh, resultant_comm h g i (i+1)]
      ring

local macro "poly_degree" : tactic =>
  `(tactic| (try dsimp [f6,f5,f4,f3,f2,f1]) <;> compute_degree!)

local macro "poly_identity" : tactic =>
  `(tactic| norm_num [f6,f5,f4,f3,f2,f1, map_ofNat] <;> ring)

private theorem euclid5 :
    1^5 * (resultant f6 f5 6 5) = 48^5 * ((-1:ℤ)^5 * 1)^2 * (-1)^20 * (resultant f5 f4 5 4) := by
  have lc : f5.coeff 5 = 1 := by poly_degree
  have h := resultant_step 4 f6 f5 f4 (4+2*X) 1 48
    (by poly_identity) (by poly_degree) (by poly_degree) (by poly_degree)
  change _ * _ = _ * ((-1:ℤ)^5 * f5.coeff 5)^2 * _ * _ at h
  rw [lc] at h
  exact h

private theorem euclid4 :
    9^4 * (resultant f5 f4 5 4) = 64^4 * ((-1:ℤ)^4 * 3)^2 * (-1)^12 * (resultant f4 f3 4 3) := by
  have lc : f4.coeff 4 = 3 := by poly_degree
  have h := resultant_step 3 f5 f4 f3 (46+3*X) 9 64
    (by poly_identity) (by poly_degree) (by poly_degree) (by poly_degree)
  change _ * _ = _ * ((-1:ℤ)^4 * f4.coeff 4)^2 * _ * _ at h
  rw [lc] at h
  exact h

private theorem euclid3 :
    1369^3 * (resultant f4 f3 4 3) = 36^3 * ((-1:ℤ)^3 * 37)^2 * (-1)^6 * (resultant f3 f2 3 2) := by
  have lc : f3.coeff 3 = 37 := by poly_degree
  have h := resultant_step 2 f4 f3 f2 (-568+111*X) 1369 36
    (by poly_identity) (by poly_degree) (by poly_degree) (by poly_degree)
  change _ * _ = _ * ((-1:ℤ)^3 * f3.coeff 3)^2 * _ * _ at h
  rw [lc] at h
  exact h

private theorem euclid2 :
    19881^2 * (resultant f3 f2 3 2) = 175232^2 * ((-1:ℤ)^2 * 141)^2 * (-1)^2 * (resultant f2 f1 2 1) := by
  have lc : f2.coeff 2 = 141 := by poly_degree
  have h := resultant_step 1 f3 f2 f1 (-6308+5217*X) 19881 175232
    (by poly_identity) (by poly_degree) (by poly_degree) (by poly_degree)
  change _ * _ = _ * ((-1:ℤ)^2 * f2.coeff 2)^2 * _ * _ at h
  rw [lc] at h
  exact h

private theorem euclid1 :
    289^1 * (resultant f2 f1 2 1) = (-59643)^1 * ((-1:ℤ)^1 * 17)^2 * (-1)^0 * (resultant f1 (1:ℤ[X]) 1 0) := by
  have lc : f1.coeff 1 = 17 := by poly_degree
  have h := resultant_step 0 f2 f1 (1:ℤ[X]) (3931+2397*X) 289 (-59643)
    (by poly_identity) (by poly_degree) (by poly_degree) (by simp)
  change _ * _ = _ * ((-1:ℤ)^1 * f1.coeff 1)^2 * _ * _ at h
  rw [lc] at h
  exact h

private lemma combine (r6 r5 r4 r3 r2 r1 : ℤ)
    (h5 : 1^5 * r6 = 48^5 * ((-1:ℤ)^5 * 1)^2 * (-1)^20 * r5)
    (h4 : 9^4 * r5 = 64^4 * ((-1:ℤ)^4 * 3)^2 * (-1)^12 * r4)
    (h3 : 1369^3 * r4 = 36^3 * ((-1:ℤ)^3 * 37)^2 * (-1)^6 * r3)
    (h2 : 19881^2 * r3 = 175232^2 * ((-1:ℤ)^2 * 141)^2 * (-1)^2 * r2)
    (h1 : 289^1 * r2 = (-59643)^1 * ((-1:ℤ)^1 * 17)^2 * (-1)^0 * r1)
    (h0 : r1 = 1) : 12^6 * r6 = -(2^76 * 3^12) := by
  have z2 : r2 = -59643 := by
    apply mul_left_cancel₀ (show (289^1:ℤ) ≠ 0 by decide)
    rw [h1, h0] <;> norm_num
  have z3 : r3 = -92118761472 := by
    apply mul_left_cancel₀ (show (19881^2:ℤ) ≠ 0 by decide)
    rw [h2, z2] <;> norm_num
  have z4 : r4 = -2293235712 := by
    apply mul_left_cancel₀ (show (1369^3:ℤ) ≠ 0 by decide)
    rw [h3, z3] <;> norm_num
  have z5 : r5 = -52776558133248 := by
    apply mul_left_cancel₀ (show (9^4:ℤ) ≠ 0 by decide)
    rw [h4, z4] <;> norm_num
  have z6 : r6 = -13447676429734263128064 := by
    apply mul_left_cancel₀ (show (1^5:ℤ) ≠ 0 by decide)
    rw [h5, z5] <;> norm_num
  rw [z6] <;> norm_num

/-- Signed Sylvester resultant for the actual integer fibre at s=2. -/
theorem specialized_resultant : parameterResultant (2 : ℤ) = -(2^76 * 3^12) := by
  have h0 : resultant f1 (1:ℤ[X]) 1 0 = 1 := by simp
  change resultant (sextic (2:ℤ)) _ 6 5 = _
  rw [show sextic (2:ℤ) = f6 from at_two, f6_derivative, resultant_C_mul_right]
  exact combine _ _ _ _ _ _ euclid5 euclid4 euclid3 euclid2 euclid1 h0

theorem specialized_discriminant : (sextic (2 : ℤ)).discr = 2^75 * 3^12 := by
  have hdeg : (sextic (2:ℤ)).natDegree = 6 := by rw [at_two]; compute_degree!
  have hlc : (sextic (2:ℤ)).leadingCoeff = 2 := by
    rw [← coeff_natDegree, hdeg, at_two]; compute_degree!
  have hex := resultant_deriv (f:=sextic (2:ℤ)) (natDegree_pos_iff_degree_pos.mp (by omega))
  rw [hdeg,hlc] at hex
  have h := specialized_resultant
  unfold parameterResultant at h
  norm_num at hex h ⊢
  omega

private lemma natCast_small {p n : ℕ} (hn : 0<n) (hlt : n<p) : (n : ZMod p) ≠ 0 := by
  rw [ne_eq, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hn hlt

/-- The fixed-degree resultant in F_p[s] has the displayed nonzero specialization. -/
theorem reduction_at_two (p : ℕ) :
    (parameterResultant (X : (ZMod p)[X])).eval 2 = -((2 : ZMod p)^76 * 3^12) := by
  have h := map_parameterResultant (evalRingHom (2 : ZMod p)) (X : (ZMod p)[X])
  have h2 := map_parameterResultant (Int.castRingHom (ZMod p)) (2:ℤ)
  change (parameterResultant (X : (ZMod p)[X])).eval 2 = parameterResultant ((X : (ZMod p)[X]).eval 2) at h
  rw [eval_X] at h
  rw [specialized_resultant] at h2
  norm_num [map_ofNat] at h2 ⊢
  simpa [h] using h2.symm

theorem reduced_resultant_ne_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    parameterResultant (X : (ZMod p)[X]) ≠ 0 := by
  have h2 := natCast_small (p:=p) (n:=2) (by decide) (by omega)
  have h3 := natCast_small (p:=p) (n:=3) (by decide) (by omega)
  intro he
  have h := reduction_at_two p
  rw [he,eval_zero] at h
  exact (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))) h.symm

/-- Coefficientwise reduction of the integral Sylvester resultant commutes with the parameter. -/
theorem reduce_integer_resultant (p : ℕ) :
    (parameterResultant (X : ℤ[X])).map (Int.castRingHom (ZMod p)) =
      parameterResultant (X : (ZMod p)[X]) := by
  have h := map_parameterResultant (mapRingHom (Int.castRingHom (ZMod p))) (X : ℤ[X])
  simpa using h

/-- The integral resultant has a coefficient prime to p; its Gauss valuation is zero. -/
theorem primitive_at_prime (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    ∃ n, ¬ (p : ℤ) ∣ (parameterResultant (X : ℤ[X])).coeff n := by
  by_contra! h
  apply reduced_resultant_ne_zero p hp
  rw [← reduce_integer_resultant]
  ext n
  rw [coeff_map, coeff_zero]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (h n)

/-- The rational function field over F_p is the residue field of the generic Gauss place. -/
abbrev GaussResidue (p : ℕ) [Fact p.Prime] := FractionRing ((ZMod p)[X])

def genericParameter (p : ℕ) [Fact p.Prime] : GaussResidue p :=
  algebraMap ((ZMod p)[X]) (GaussResidue p) X

theorem generic_resultant_unit (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    IsUnit (parameterResultant (genericParameter p)) := by
  apply isUnit_iff_ne_zero.mpr
  rw [genericParameter, ← map_parameterResultant]
  exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (reduced_resultant_ne_zero p hp)

theorem generic_lead_ne_zero (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    -4+3*genericParameter p ≠ 0 := by
  let f := algebraMap ((ZMod p)[X]) (GaussResidue p)
  have he : -4+3*genericParameter p = f (-4+3*X) := by simp [genericParameter,f,map_ofNat]
  rw [he]
  apply (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
  intro hz
  have hh := congrArg (Polynomial.eval (2:ZMod p)) hz
  have h2 := natCast_small (p:=p) (n:=2) (by decide) (by omega)
  norm_num at hh
  exact h2 (by linear_combination hh)

private lemma six_term_degree {R : Type*} [CommRing R] (a b c d e f g : R) :
    (C a*X^6 + C b*X^5 + C c*X^4 - C d*X^3 + C e*X^2 + C f*X - C g).natDegree ≤ 6 := by
  compute_degree!

private lemma six_term_coeff {R : Type*} [CommRing R] (a b c d e f g : R) :
    (C a*X^6 + C b*X^5 + C c*X^4 - C d*X^3 + C e*X^2 + C f*X - C g).coeff 6 = a := by
  simp [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow]

private lemma sextic_degree_le {R : Type*} [CommRing R] (s : R) : (sextic s).natDegree ≤ 6 := by
  exact six_term_degree ..

private lemma sextic_coeff_six {R : Type*} [CommRing R] (s : R) : (sextic s).coeff 6 = -4+3*s := by
  exact six_term_coeff ..

theorem generic_degree (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (sextic (genericParameter p)).natDegree = 6 :=
  natDegree_eq_of_le_of_coeff_ne_zero (sextic_degree_le _) (by rw [sextic_coeff_six]; exact generic_lead_ne_zero p hp)

theorem generic_separable (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    (sextic (genericParameter p)).Separable := by
  let f := sextic (genericParameter p)
  have hm : f.natDegree = 6 := generic_degree p hp
  have hn : f.derivative.natDegree ≤ 5 := (natDegree_derivative_le _).trans (by omega)
  obtain ⟨a,b,_,_,eq⟩ := exists_mul_add_mul_eq_C_resultant (m:=6) (n:=5) f f.derivative hm.le hn (by decide)
  let r := parameterResultant (genericParameter p)
  have hr : r ≠ 0 := (generic_resultant_unit p hp).ne_zero
  change ∃ c d, c*f+d*f.derivative=1
  refine ⟨C r⁻¹*a, C r⁻¹*b, ?_⟩
  calc
    _ = C r⁻¹ * (f*a+f.derivative*b) := by ring
    _ = _ := by rw [eq]; change C r⁻¹ * C r=1; rw [← C_mul, inv_mul_cancel₀ hr, C_1]

theorem generic_discriminant_unit (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    IsUnit (sextic (genericParameter p)).discr := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have hd := generic_degree p hp
  have h := resultant_deriv (f:=sextic (genericParameter p)) (natDegree_pos_iff_degree_pos.mp (by omega))
  rw [hd,hz,mul_zero] at h
  exact (generic_resultant_unit p hp).ne_zero h

#print axioms at_two
#print axioms map_parameterResultant
#print axioms specialized_resultant
#print axioms specialized_discriminant
#print axioms reduction_at_two
#print axioms reduced_resultant_ne_zero
#print axioms reduce_integer_resultant
#print axioms primitive_at_prime
#print axioms generic_resultant_unit
#print axioms generic_lead_ne_zero
#print axioms generic_degree
#print axioms generic_separable
#print axioms generic_discriminant_unit

end
end ZInQBlueprint.SexticCalibration
