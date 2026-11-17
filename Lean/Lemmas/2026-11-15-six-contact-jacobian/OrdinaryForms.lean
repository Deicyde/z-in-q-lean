import RegularSextic
import FixedCurve
import Mathlib.RingTheory.Polynomial.Basic

/-! The integral unit criterion in the finite chart and the chart at infinity. -/
open Polynomial
open ZInQBlueprint.DirectCharts ZInQBlueprint.IntegralSextic ZInQBlueprint.BinaryCover
namespace ZInQBlueprint.OrdinaryModel
noncomputable section
variable {R : Type} [CommRing R]

def infinityForm (t : R) : R[X] := form 1 (C t) 1 X

theorem infinity_coeffs (t : R) : infinityForm t =
    1+C (9-t)*X+C (27-9*t)*X^2+C (t^2-32*t+27)*X^3+
    C (6*t^2-54*t)*X^4+C (12*t^2-36*t)*X^5+C (8*t^2)*X^6 := by
  simp [infinityForm,form,alpha,beta,gamma,map_ofNat]
  ring

private theorem form_map {S : Type*} [CommRing S] {T : Type*} [CommRing T]
    (h : S →+* T) (a b x z : S) : h (form a b x z) = form (h a) (h b) (h x) (h z) := by
  simp [form,alpha,beta,gamma,map_ofNat]

/-- The reciprocal-coordinate transition is defined even before any localization of the base. -/
theorem overlap (s t : R) : SexticOverlap R (C s*monicSextic t) (C s*infinityForm t) := by
  unfold SexticOverlap monicSextic infinityForm
  simp only [map_mul,form_map,map_one,toLaurent_C,toLaurent_X]
  change LaurentPolynomial.invert.toRingHom (LaurentPolynomial.C s) *
      LaurentPolynomial.invert.toRingHom (form _ _ _ _) = _
  have HC (a : R) : LaurentPolynomial.invert.toRingHom (LaurentPolynomial.C a) =
      LaurentPolynomial.C a := LaurentPolynomial.invert_C a
  have HT : LaurentPolynomial.invert.toRingHom (LaurentPolynomial.T 1 : LaurentPolynomial R) =
      LaurentPolynomial.T (-1) := LaurentPolynomial.invert_T 1
  rw [form_map,HC,HC,map_one,HT]
  let c : LaurentPolynomial R := LaurentPolynomial.T (-1)
  let x : LaurentPolynomial R := LaurentPolynomial.T 1
  have hcx : c*x=1 := by
    change LaurentPolynomial.T (-1) * LaurentPolynomial.T 1 = (1 : LaurentPolynomial R)
    rw [← LaurentPolynomial.T_add,neg_add_cancel,LaurentPolynomial.T_zero]
  have ht : (LaurentPolynomial.T (-3) : LaurentPolynomial R)^2 = c^6 := by
    simp only [c,LaurentPolynomial.T_pow]
    norm_num
  rw [ht]
  have hh := form_homogeneous 1 (LaurentPolynomial.C t) c 1 x
  rw [mul_one,hcx] at hh
  change _ * form 1 _ c 1 = c^6 * (_ * form 1 _ 1 x)
  rw [hh]
  ring

private theorem coprime_of_unit_bezout {f : R[X]} {u : R} (hu : IsUnit u)
    (h : ∃ a b : R[X], a*f + b*f.derivative = C u) : IsCoprime f f.derivative := by
  obtain ⟨a,b,hab⟩ := h
  let v := hu.unit
  refine ⟨C (↑v⁻¹ : R)*a,C (↑v⁻¹ : R)*b,?_⟩
  calc
    _ = C (↑v⁻¹ : R)*(a*f+b*f.derivative) := by ring
    _ = 1 := by rw [hab,← C_mul,← hu.unit_spec]; simp [v]

theorem finite_regular {t : R} (h2 : IsUnit (2:R)) (ht : IsUnit t)
    (hD : IsUnit (t^2+27)) : IsCoprime (monicSextic t) (monicSextic t).derivative := by
  apply coprime_of_unit_bezout (u := 32*t^2*(t^2+27))
  · rw [show (32:R)=2^5 by norm_num]
    exact ((h2.pow 5).mul (ht.pow 2)).mul hD
  · exact ⟨_,_,RegularSextic.bezout t⟩

theorem scale_regular {f : R[X]} (u : Rˣ) (hf : IsCoprime f f.derivative) :
    IsCoprime (C (u:R)*f) (C (u:R)*f).derivative := by
  obtain ⟨a,b,h⟩ := hf
  refine ⟨C (↑u⁻¹ : R)*a,C (↑u⁻¹ : R)*b,?_⟩
  rw [derivative_C_mul]
  calc _ = C ((↑u⁻¹ : R)*(u:R))*(a*f+b*f.derivative) := by rw [C_mul]; ring
       _ = 1 := by simp [h]
private def front (t : R) : R[X] :=
  ((((C (-144*t^2*(17*t^2 - 432*t + 2187))*X + C (-36*t*(53*t^3 - 1659*t^2 + 14499*t - 32805)))*X + C (-36*t*(10*t^3 - 429*t^2 + 6642*t - 28431)))*X + C (-9*(t^4 - 204*t^3 + 5454*t^2 - 43740*t + 59049)))*X + C (9*(17*t^3 - 453*t^2 + 5103*t - 19683)))

private def back (t : R) : R[X] :=
  (((((C (24*t^2*(17*t^2 - 432*t + 2187))*X + C (12*t*(t - 9)*(35*t^2 - 756*t + 2187)))*X + C (6*t*(19*t^3 - 801*t^2 + 11421*t - 45927)))*X + C (3*(t^4 - 254*t^3 + 7074*t^2 - 51030*t + 59049)))*X + C (-18*(7*t^3 - 201*t^2 + 2187*t - 6561)))*X + C (-(t - 27)^2*(2*t - 27)))

/-- Exact Bézout identity at infinity, valid over every coefficient ring. -/
theorem infinity_bezout (t : R) :
    front t*infinityForm t+back t*(infinityForm t).derivative = C (2*t^2*(t^2+27)) := by
  rw [infinity_coeffs]
  simp [front,back,derivative_add,derivative_mul,derivative_pow,map_ofNat]
  ring

theorem infinity_regular {t : R} (h2 : IsUnit (2:R)) (ht : IsUnit t)
    (hD : IsUnit (t^2+27)) : IsCoprime (infinityForm t) (infinityForm t).derivative :=
  coprime_of_unit_bezout ((h2.mul (ht.pow 2)).mul hD) ⟨_,_,infinity_bezout t⟩

def chartPair (s t : R) (i : Bool) : R[X] := C s*(if i then infinityForm t else monicSextic t)

def model (s t : R) := gluedOver R _ _ (overlap s t)

theorem pair_regular {s t : R} (hs : IsUnit s) (h2 : IsUnit (2:R)) (ht : IsUnit t)
    (hD : IsUnit (t^2+27)) (i : Bool) :
    IsCoprime (chartPair s t i) (chartPair s t i).derivative := by
  rcases hs with ⟨u,rfl⟩
  cases i
  · exact scale_regular u (finite_regular h2 ht hD)
  · exact scale_regular u (infinity_regular h2 ht hD)

theorem chart_map {K : Type} [CommRing K] (φ : R →+* K) (s t : R) (i : Bool) :
    (chartPair s t i).map φ = chartPair (φ s) (φ t) i := by
  cases i <;> simp [chartPair,infinityForm,monicSextic,form,alpha,beta,gamma]

theorem pair_degree {K : Type} [Field K] {s t : K} (hs : s≠0) (h2 : (2:K)≠0)
    (ht : t≠0) (i : Bool) : (chartPair s t i).natDegree = 6 := by
  unfold chartPair
  rw [natDegree_C_mul hs]
  cases i
  · exact (monic_six t).2
  · change (infinityForm t).natDegree=6
    rw [infinity_coeffs]
    have e : 8*t^2≠0 := by
      rw [show (8:K) = 2^3 by norm_num]
      exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ ht)
    compute_degree!
    exact ⟨left_ne_zero_of_mul e,ht⟩

end
end ZInQBlueprint.OrdinaryModel
#print axioms ZInQBlueprint.OrdinaryModel.overlap
#print axioms ZInQBlueprint.OrdinaryModel.infinity_bezout
#print axioms ZInQBlueprint.OrdinaryModel.pair_regular
#print axioms ZInQBlueprint.OrdinaryModel.pair_degree
