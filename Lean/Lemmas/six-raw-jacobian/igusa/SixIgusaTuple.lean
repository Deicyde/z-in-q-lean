import SexticIgusaPole

/-! Arithmetic Igusa coordinates of the signed sextic, in the binary-form
normalization. The conventional curve input for Magma uses the form 4f. -/
namespace ZInQBlueprint.SexticInvariants
open Polynomial JacobianHeight DirectCharts BinaryCover SexticIgusaChart SexticThetaHeight
noncomputable section
set_option maxHeartbeats 4000000

/-- The normalized fourth transvectant of a binary quartic and its
second self-transvectant, with ordinary (non-binomial) coefficients. -/
def quarticC (a b c d e : ℚ) : ℚ :=
  (72*a*c*e - 27*a*d^2 - 27*b^2*e + 9*b*c*d - 2*c^3)/72

/-- The preceding scalar applied to q = (f,f)₄. -/
def sexticC (a : ℕ → ℚ) : ℚ :=
  quarticC
    ((10*a 0*a 4-5*a 1*a 3+2*(a 2)^2)/75)
    (2*(25*a 0*a 5-5*a 1*a 4+a 2*a 3)/75)
    ((50*a 0*a 6-2*a 2*a 4+(a 3)^2)/25)
    (2*(25*a 1*a 6-5*a 2*a 5+a 3*a 4)/75)
    ((10*a 2*a 6-5*a 3*a 5+2*(a 4)^2)/75)

def igusaI6 (f : ℚ[X]) : ℚ :=
  8640*(sexticA f.coeff)^3-108000*sexticA f.coeff*sexticB f.coeff+202500*sexticC f.coeff

def igusaJ4 (f : ℚ[X]) : ℚ := (4*(igusaJ2 f)^2-igusaI4 f)/96
def igusaJ6 (f : ℚ[X]) : ℚ := (8*(igusaJ2 f)^3-160*igusaJ2 f*igusaJ4 f-igusaI6 f)/576
def igusaJ8 (f : ℚ[X]) : ℚ := (igusaJ2 f*igusaJ6 f-(igusaJ4 f)^2)/4

private theorem coefficientForm (t : ℚ) (n : ℕ) :
    (monicSextic t).coeff n =
      (if n=6 then 1 else 0) + (if n=5 then 9-t else 0) +
      (if n=4 then 27-9*t else 0) + (if n=3 then t^2-32*t+27 else 0) +
      (if n=2 then 6*t^2-54*t else 0) + (if n=1 then 12*t^2-36*t else 0) +
      (if n=0 then 8*t^2 else 0) := by
  rw [monic_coeffs]
  simp only [coeff_add, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_X_pow, coeff_C]

private theorem clebschC_family (s t : ℚ) :
    sexticC (C s*monicSextic t).coeff =
    -s^6*(t^12+450*t^10+10807*t^8-295300*t^6+7878303*t^4+239148450*t^2+387420489)/562500 := by
  simp only [sexticC, coeff_C_mul, coefficientForm]
  norm_num
  unfold quarticC
  ring

/-- The sixth Igusa–Clebsch invariant on every scalar twist of the family. -/
theorem igusaI6_family (s t : ℚ) :
    igusaI6 (C s*monicSextic t) = -288*s^6*t^2*(t^2+27)^2*(t^4-26*t^2+729) := by
  let f := C s * monicSextic t
  have a : sexticA f.coeff = -(3*s^2*((t^2+27)^2-64*t^2)/4)/15 := by
    have h := igusaJ2_family s t
    change -15*sexticA f.coeff = _ at h
    linarith
  have b : sexticB f.coeff = (-144*s^4*t^2*(t^2+27)^2+720*(sexticA f.coeff)^2)/6750 := by
    have h := igusaI4_family s t
    change -720*(sexticA f.coeff)^2+6750*sexticB f.coeff = _ at h
    linarith
  change 8640*(sexticA f.coeff)^3-108000*sexticA f.coeff*sexticB f.coeff+202500*sexticC f.coeff = _
  rw [b,a,show sexticC f.coeff = _ from clebschC_family s t]
  ring

/-- All five arithmetic Igusa coordinates at their common half-weight scale. -/
def HasBGTuple (f : ℚ[X]) (j b : ℚ) : Prop :=
  igusaJ2 f = b*(12*(j+1)) ∧ igusaJ4 f = b^2*(6*(j^2+j+1)) ∧
  igusaJ6 f = b^3*(4*(j^3-2*j^2+1)) ∧
  igusaJ8 f = b^4*((12*(j+1)*(4*(j^3-2*j^2+1))-(6*(j^2+j+1))^2)/4) ∧
  igusaJ10 f = b^5*j^3

theorem igusa_tuple_family (s t : ℚ) (hs : s ≠ 0) :
    HasBGTuple (C s * monicSextic t) (-64*t^2/(t^2+27)^2) ((s*(t^2+27))^2/16) := by
  have ht : t^2+27 ≠ 0 := by nlinarith [sq_nonneg t]
  unfold HasBGTuple igusaJ8 igusaJ6 igusaJ4 igusaJ10
  rw [igusaJ2_family,igusaI4_family,igusaI6_family,discr_family _ _ hs]
  repeat' constructor
  all_goals
    field_simp [ht]
    ring

/-- The affine polynomial of the actual signed rational curve has the full
weighted tuple of Baba--Granath Proposition 3.6, with a nonzero scale. -/
theorem signed_igusa_tuple {u : ℚ} (hu : u ∉ ZInQ.contactSet) :
    ∃ b : ℚ, b ≠ 0 ∧ HasBGTuple (paper ℚ u false) (SixContact.J u) b := by
  have hδ : (GlobalTwist.delta u : ℚ) ≠ 0 := by exact_mod_cast (GlobalTwist.delta_pos u).ne'
  obtain ⟨_,hs,ht,hj⟩ := unmarked hu hδ
  let s := CurveChart.yScale u ^ 2 * scalar u (GlobalTwist.delta u : ℚ)
  have hs' : s ≠ 0 := mul_ne_zero (pow_ne_zero _ (CurveChart.yScale_ne hu)) hs
  refine ⟨(s*((parameter u)^2+27))^2/16, div_ne_zero (pow_ne_zero _ (mul_ne_zero hs' ht)) (by norm_num), ?_⟩
  rw [paper_affine_eq_sextic hu, sextic, ← map_pow, ← mul_assoc, ← C_mul,hj]
  exact igusa_tuple_family s (parameter u) hs'

end
end ZInQBlueprint.SexticInvariants

#print axioms ZInQBlueprint.SexticInvariants.igusaI6_family
#print axioms ZInQBlueprint.SexticInvariants.igusa_tuple_family
#print axioms ZInQBlueprint.SexticInvariants.signed_igusa_tuple
