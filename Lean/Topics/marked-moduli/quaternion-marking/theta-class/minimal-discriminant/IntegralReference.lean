import IntegralDiscriminant

/-! Construction of the integral ideal from finite local minima. An explicit
coordinate scaling makes one equation and its discriminant integral at all
places simultaneously. Only primes of this reference discriminant can occur. -/
namespace ZInQBlueprint.MinimalDiscriminant
open Polynomial IsDedekindDomain NumberField UniqueFactorizationMonoid WithZero
noncomputable section

private def commonDenominator (f : ℚ[X]) : ℕ :=
  f.discr.den * ∏ i : Fin 7, (f.coeff i.val).den

private theorem denominator_pos (f : ℚ[X]) : 0 < commonDenominator f :=
  Nat.mul_pos f.discr.den_pos (Finset.prod_pos fun i _ => (f.coeff i.val).den_pos)

private theorem integral_multiple (x : ℚ) {D : ℕ} (h : x.den ∣ D) :
    ∃ z : ℤ, (z : ℚ) = (D : ℚ)*x := by
  obtain ⟨k,rfl⟩ := h
  refine ⟨(k:ℤ)*x.num,?_⟩
  push_cast
  have hn : (x.den:ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have eq := (div_eq_iff hn).mp (Rat.num_div_den x)
  linear_combination (k:ℚ)*eq

private def coefficientsPolynomial {R : Type*} [CommRing R] (a : Coefficients R) : R[X] :=
  ∑ i : Fin 7, monomial i.val (a i)

private theorem ordinary_coeff {R : Type*} [CommRing R] (a : Coefficients R) (i : Fin 7) :
    (coefficientsPolynomial a).coeff i.val = a i := by
  simp [coefficientsPolynomial,coeff_monomial,Fin.val_inj]

private theorem ordinary_degree {R : Type*} [CommRing R] (a : Coefficients R) :
    (coefficientsPolynomial a).natDegree ≤ 6 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_monomial_le _).trans (by omega)

private theorem form_scalar {F : Type*} [Field F] [CharZero F] (s : F) (a : Coefficients F) (x z : F) :
    form (fun i => s*a i) x z = s*form a x z := by
  unfold form
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

variable {F : Type*} [Field F] [CharZero F] (v : Valuation F ℤᵐ⁰)

private theorem scaled_integral (f : ℚ[X]) (i : Fin 7) :
    ∃ z : ℤ, (z:F) = (commonDenominator f:F)^2*(f.coeff i.val:F) := by
  let D := commonDenominator f
  have dvd : (f.coeff i.val).den ∣ D :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j : Fin 7 => (f.coeff j.val).den) (Finset.mem_univ i)) _
  obtain ⟨z,hz⟩ := integral_multiple _ dvd
  refine ⟨(D:ℤ)*z,?_⟩
  have hF : (z:F) = (D:F)*(f.coeff i.val:F) := by exact_mod_cast hz
  push_cast
  rw [hF]
  change _ = (D:F)^2*_
  ring

private def integralCoefficient (f : ℚ[X]) (i : Fin 7) : v.integer :=
  (Classical.choose (scaled_integral (F:=F) f i) : ℤ)

private theorem coe_integralCoefficient (f : ℚ[X]) (i : Fin 7) :
    ((integralCoefficient v f i : v.integer) : F) = (commonDenominator f:F)^2*(f.coeff i.val:F) := by
  simpa only [integralCoefficient,SubringClass.coe_intCast] using
    Classical.choose_spec (scaled_integral (F:=F) f i)

/-- This integral model uses denominator clearing only on the ordinate. -/
def integralReference (f : ℚ[X]) : IntegralEquation v f where
  P := coefficientsPolynomial (integralCoefficient v f)
  Q := 0
  degreeP := ordinary_degree _
  degreeQ := by simp
  a := 1
  b := 0
  c := 0
  d := 1
  e := (commonDenominator f:F)⁻¹
  det_ne := by norm_num
  e_ne := inv_ne_zero (by exact_mod_cast (denominator_pos f).ne')
  change := by
    intro x z
    have h (i : Fin 7) : (((4*coefficientsPolynomial (integralCoefficient v f)+(0:v.integer[X])^2).coeff i.val : v.integer) : F) =
        (4*(commonDenominator f:F)^2)*(f.coeff i.val:F) := by
      simp only [zero_pow (by decide : 2≠0),add_zero,coeff_ofNat_mul,ordinary_coeff]
      change 4*((integralCoefficient v f i:v.integer):F) = _
      rw [coe_integralCoefficient]
      ring
    simp only [h,form_scalar,one_mul,zero_mul,add_zero,zero_add,inv_pow,div_inv_eq_mul]

/-- A single nonzero rational integral discriminant works over every local
completion. Its value is 2^8 D^20 disc(f). -/
theorem reference_integer (f : ℚ[X]) (nz : f.discr ≠ 0) :
    ∃ z : ℤ, z ≠ 0 ∧ ∀ (F : Type) [Field F] [CharZero F] (v : Valuation F ℤᵐ⁰),
      (integralReference v f).discriminant = (z:F) := by
  let D := commonDenominator f
  obtain ⟨k,hk⟩ := integral_multiple f.discr (dvd_mul_right f.discr.den _ :
    f.discr.den ∣ commonDenominator f)
  change (k:ℚ) = (D:ℚ)*f.discr at hk
  have hn : (D:ℚ) ≠ 0 := by exact_mod_cast (denominator_pos f).ne'
  have hk' : k ≠ 0 := by
    intro h
    apply mul_ne_zero hn nz
    simpa only [h,Int.cast_zero] using hk.symm
  refine ⟨256*(D:ℤ)^19*k,by exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by exact_mod_cast (denominator_pos f).ne'))) hk',?_⟩
  intro F _ _ v
  have hF : (k:F) = (D:F)*(f.discr:F) := by exact_mod_cast hk
  change (4/((D:F)⁻¹)^2)^10*((1: F)*1-0*0)^30*((f.discr:F)/4096) = _
  push_cast
  rw [hF]
  simp only [inv_pow,div_inv_eq_mul]
  ring

end
end ZInQBlueprint.MinimalDiscriminant
#print axioms ZInQBlueprint.MinimalDiscriminant.integralReference
#print axioms ZInQBlueprint.MinimalDiscriminant.reference_integer
