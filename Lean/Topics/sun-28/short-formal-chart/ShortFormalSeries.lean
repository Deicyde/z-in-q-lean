import ZInQKernel.Multiplication.Local.LogSeries
import OrdinaryChart

/-! The normalized abscissa and invariant differential in the short Weierstrass parameter. -/
namespace Sun28.ShortFormal
open PowerSeries ZInQ.Mult Sun28.Ordinary
open scoped PowerSeries
variable {R : Type*} [CommRing R]

/-- U=xz². Since u=1/x satisfies u=z²(1+bu²), one has U=1-bz²u. -/
noncomputable def shortU (b : R) : PowerSeries R := 1-C b*X^2*uSeries b
def shortF (b : R) : PowerSeries R := invDiffSeries b

theorem map_shortU {S : Type*} [CommRing S] (f : R →+* S) (b : R) :
    PowerSeries.map f (shortU b)=shortU (f b) := by
  have hu : PowerSeries.map f (uSeries b)=uSeries (f b) := by
    ext n
    rw [coeff_map,uSeries,coeff_mk,uSeries,coeff_mk,omegaCoeff_map]
  simp [shortU,hu]

theorem map_shortF {S : Type*} [CommRing S] (f : R →+* S) (b : R) :
    PowerSeries.map f (shortF b)=shortF (f b) := by
  ext n
  rw [shortF,shortF,coeff_map,invDiffSeries,invDiffSeries,coeff_mk,coeff_mk]
  simp [invDiffCoeff,apply_ite f]

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
theorem unit_model (b : L) :
    coeff 0 (shortU b)=1 ∧ shortU b^2-shortU b+C b*X^4=0 := by
  constructor
  · simp [shortU,coeff_zero_eq_constantCoeff_apply]
  · unfold shortU
    linear_combination -C b*X^2*(uSeries_eq b)

theorem inverse_diff (b : L) :
    shortF b*(2*shortU b-1)=1 := by
  convert invDiffSeries_mul b using 1
  simp only [shortF,shortU,map_mul,map_ofNat]
  ring

theorem differential (b : L) :
    2*shortU b*shortF b=2*shortU b-X*derivative (shortU b) := by
  have model := (unit_model b).2
  have dm := congrArg derivative model
  norm_num [derivative_pow] at dm
  have h := inverse_diff b
  linear_combination (2*shortU b-X*derivative (shortU b))*h + X*(shortF b)*dm - (4*shortF b)*model

theorem coefficients (b : L) (n : ℕ) : coeff n (shortF b)=shortDifferential b (n+1) :=
  short_chart_differential_coefficients b _ _ (unit_model b).1 (unit_model b).2 (differential b) n

/-- Both normalized power series are defined over every coefficient ring and base change
commutes with the construction. In particular they lift to the valuation ring of b. -/
theorem defined_over {S : Type*} [CommRing S] (f : R →+* S) (b : R) :
    ∃ U F : PowerSeries R, PowerSeries.map f U=shortU (f b) ∧ PowerSeries.map f F=shortF (f b) :=
  ⟨shortU b,shortF b,map_shortU f b,map_shortF f b⟩

#print axioms unit_model
#print axioms differential
#print axioms coefficients
#print axioms defined_over
end Sun28.ShortFormal
