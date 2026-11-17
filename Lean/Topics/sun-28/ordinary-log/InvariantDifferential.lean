import OrdinaryIndex
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Data.Nat.Choose.Central

/-! Recover all coefficients of the normalized invariant differential from
the differential equation satisfied in the short Weierstrass parameter. -/
namespace Sun28.Ordinary
open PowerSeries
open scoped PowerSeries
variable {L : Type*} [Field L] [CharZero L]

/-- The short differential equation forces every coefficient, not just the
sixteen coefficients retained in the ordinary certificate. -/
theorem short_differential_coefficients (b : L) (F : PowerSeries L)
    (normalized : coeff 0 F=1)
    (ode : derivative F - C (4*b)*(X^4*derivative F)=C (8*b)*(X^3*F)) :
    ∀ n : ℕ, coeff n F=shortDifferential b (n+1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa [shortDifferential] using normalized
    | succ j =>
      have rel := congrArg (coeff j) ode
      simp only [map_sub,coeff_C_mul,coeff_X_pow_mul',coeff_derivative] at rel
      by_cases small : j<3
      · have h4 : ¬4≤j := by omega
        have h3 : ¬3≤j := by omega
        simp only [ite_eq_right h4,ite_eq_right h3,mul_zero,sub_zero] at rel
        have nz : (j:L)+1≠0 := by exact_mod_cast (show j+1≠0 by omega)
        have zero := (mul_eq_zero.mp rel).resolve_right nz
        rw [zero]
        simp [shortDifferential,show (j+1+1)%4≠1 by omega]
      · obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le (by omega : 3≤j)
        have shift : 3+n-3=n := by omega
        have base := ih n (by omega)
        have mulshift : (if 4≤3+n then coeff (3+n-4+1) F*((↑(3+n-4):L)+1) else 0)=
            coeff n F*(n:L) := by
          cases n with
          | zero => simp
          | succ n =>
            rw [ite_eq_left (by omega),show 3+(n+1)-4+1=n+1 by omega,show 3+(n+1)-4=n by omega]
            push_cast
            ring
        rw [ite_eq_left (by omega : 3≤3+n),shift,mulshift] at rel
        have nz : (3:L)+(n:L)+1≠0 := by exact_mod_cast (show 3+n+1≠0 by omega)
        apply (mul_right_cancel₀ nz)
        push_cast at rel ⊢
        rw [base] at rel
        by_cases four : n%4=0
        · obtain ⟨i,ii⟩ := (Nat.dvd_iff_mod_eq_zero.mpr four : 4∣n)
          subst n
          have b0 : (4*i+1)%4=1 := by omega
          have b1 : (3+4*i+1+1)%4=1 := by omega
          have q0 : (4*i+1)/4=i := by omega
          have q1 : (3+4*i+1+1)/4=i+1 := by omega
          simp only [shortDifferential,ite_eq_left b0,ite_eq_left b1,q0,q1] at rel ⊢
          have cb := congrArg (fun t:ℕ => (t:L)) (Nat.succ_mul_centralBinom_succ i)
          simp only [Nat.centralBinom_eq_two_mul_choose] at cb
          push_cast at cb rel ⊢
          rw [pow_succ]
          linear_combination rel - 4*b^(i+1)*cb
        · have n0 : (n+1)%4≠1 := by omega
          have n1 : (3+n+1+1)%4≠1 := by omega
          simp only [shortDifferential,ite_eq_right n0,ite_eq_right n1,zero_mul,mul_zero,sub_zero] at rel ⊢
          exact rel

/-- The bounded chart U=x*z² has U(0)=1 and U²-U+bz⁴=0.
For the normalized differential F dz=dx/(2y), the defining identity is
2UF=2U-zU'. These two polynomial identities force its entire series. -/
theorem short_chart_differential_ode (b : L) (U F : PowerSeries L)
    (unit : coeff 0 U=1) (model : U^2-U+C b*X^4=0)
    (invariant : 2*U*F=2*U-X*derivative U) :
    coeff 0 F=1 ∧ derivative F-C (4*b)*(X^4*derivative F)=C (8*b)*(X^3*F) := by
  have dmodel := congrArg derivative model
  norm_num [derivative_pow] at dmodel
  have two : (2:PowerSeries L)≠0 := by
    intro zero
    have eq := congrArg (constantCoeff (R:=L)) zero
    rw [map_ofNat,map_zero] at eq
    norm_num at eq
  have U0 : U≠0 := by intro h; rw [h] at unit; simp at unit
  have inverse : (2*U-1)*F=1 := by
    apply mul_left_cancel₀ (mul_ne_zero two U0)
    linear_combination (2*U-1)*invariant - X*dmodel +4*model
  have norm : (1-C (4*b)*X^4)*F^2=1 := by
    have sq := congrArg (fun t:PowerSeries L => t^2) inverse
    rw [map_mul,map_ofNat]
    linear_combination sq -4*F^2*model
  have df := congrArg derivative norm
  norm_num [derivative_pow,map_ofNat] at df
  have d4 : derivative (4:PowerSeries L)=0 := by
    rw [←map_ofNat (C (R:=L)) 4,derivative_C]
  rw [d4] at df
  have nf : F≠0 := by intro h; rw [h] at inverse; simp at inverse
  have scaled : (2*F)*(derivative F-C (4*b)*(X^4*derivative F)-C (8*b)*(X^3*F))=0 := by
    rw [map_mul,map_ofNat,map_mul,map_ofNat]
    linear_combination df
  have result := (mul_eq_zero.mp scaled).resolve_left (mul_ne_zero two nf)
  have un : constantCoeff U=1 := by simpa only [coeff_zero_eq_constantCoeff_apply] using unit
  have atzero := congrArg (constantCoeff (R:=L)) inverse
  rw [map_mul,map_sub,map_mul,map_ofNat,un,map_one] at atzero
  refine ⟨?_,sub_eq_zero.mp result⟩
  rw [coeff_zero_eq_constantCoeff_apply]
  linear_combination atzero

theorem short_chart_differential_coefficients (b : L) (U F : PowerSeries L)
    (unit : coeff 0 U=1) (model : U^2-U+C b*X^4=0)
    (invariant : 2*U*F=2*U-X*derivative U) :
    ∀ n : ℕ, coeff n F=shortDifferential b (n+1) := by
  obtain ⟨h,ode⟩ := short_chart_differential_ode b U F unit model invariant
  exact short_differential_coefficients b F h ode

end Sun28.Ordinary
#print axioms Sun28.Ordinary.short_differential_coefficients
#print axioms Sun28.Ordinary.short_chart_differential_ode
#print axioms Sun28.Ordinary.short_chart_differential_coefficients
