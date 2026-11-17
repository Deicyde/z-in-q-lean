import Mathlib.Tactic

/-! Explicit normalized error from truncating uneven residue intervals in the
localized Gowers-norm identity. All cube averages here are real. -/
namespace ZInQBlueprint.AffineIntervals
noncomputable section

/-- Removing one endpoint from each long residue interval leaves mass A.
S is the mass satisfying the residue condition before truncation. -/
theorem interval_mass_gap {h k b J : ℝ} (hh : 1 ≤ h) (hk : 1 ≤ k) (hb : 0 ≤ b)
    (small : b < h) (whole : b<1 → b=0) (length : J=h*k+b) :
    let A := h*k^2/J^2
    let S := (h*k^2+(2*k+1)*b)/J^2
    0 ≤ A ∧ A≤S ∧ S≤1 ∧ A≤1/h ∧ 1/h≤1 ∧ S-A≤2/J ∧ 1/h-A≤2/J := by
  dsimp only
  have hp : 0<h := by linarith
  have jp : 0<J := by rw [length]; positivity
  have sp : 0<J^2 := sq_pos_of_pos jp
  have hk0 : 0≤k := by linarith
  have unit : b*(1-b) ≤ h*(h-1)*k^2 := by
    by_cases big : 1≤b
    · have L : b*(1-b)≤0 := mul_nonpos_of_nonneg_of_nonpos hb (by linarith)
      exact L.trans (mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hh)) (sq_nonneg k))
    · -- Integer residue counts are used only here.
      have zero : b=0 := by exact whole (by linarith)
      simpa [zero] using mul_nonneg (mul_nonneg hp.le (sub_nonneg.mpr hh)) (sq_nonneg k)
  have residual : (2*k+1)*b ≤ 2*J := by nlinarith [mul_nonneg hk0 (sub_nonneg.mpr small.le)]
  have aJ : h*k≤J := by linarith
  have sinv : 1/h≤1 := (div_le_one hp).2 hh
  have Sq : h*k^2+(2*k+1)*b ≤ J^2 := by
    rw [length]
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (mul_nonneg hk0 hb)]
  have inv : h*k^2/J^2≤1/h := by
    rw [div_le_div_iff₀ sp hp]
    nlinarith [sq_le_sq' (by nlinarith [mul_nonneg hp.le hk0] : -J≤h*k) aJ]
  refine ⟨by positivity, (div_le_div_iff_of_pos_right sp).2 (by nlinarith), 
    (div_le_one sp).2 Sq,inv,sinv,?_,?_⟩
  · rw [←sub_div]
    have eqv : 2/J=2*J/J^2 := by field_simp
    rw [eqv,div_le_div_iff_of_pos_right sp]
    linarith
  · have pos : 0≤J+h*k := by nlinarith [mul_nonneg hp.le hk0]
    have aux : J^2-(h*k)^2 ≤ 2*h*J := by
      rw [length]
      nlinarith [mul_nonneg (sub_nonneg.mpr small.le) pos, mul_nonneg hp.le (sub_nonneg.mpr aJ)]
    have eqv : 1/h-h*k^2/J^2=(J^2-(h*k)^2)/(h*J^2) := by field_simp
    have eqr : 2/J=2*h*J/(h*J^2) := by field_simp
    rw [eqv,eqr,div_le_div_iff_of_pos_right (mul_pos hp sp)]
    exact aux
theorem power_mass_gap {A S d : ℝ} (ha : 0≤A) (hs : S≤1) (as' : A≤S) (delta : S-A≤d) (a : ℕ) :
    S^a-A^a≤a*d := by
  induction a with
  | zero => simp
  | succ a ih =>
    have dn : 0≤d := (sub_nonneg.mpr as').trans delta
    have ap := pow_le_one₀ ha (as'.trans hs) (n:=a)
    have an := pow_nonneg ha a
    have sn := ha.trans as'
    rw [pow_succ,pow_succ,Nat.cast_succ]
    nlinarith [mul_nonneg sn (sub_nonneg.mpr ih),mul_nonneg (sub_nonneg.mpr hs) (mul_nonneg (Nat.cast_nonneg a) dn),
      mul_nonneg an (sub_nonneg.mpr delta), mul_nonneg (sub_nonneg.mpr ap) dn]

/-- The discarded mass and the correction of the main coefficient each cost
at most 2a/J. The bound is uniform in the step and in the residue count. -/
theorem normalized_cube_error {A S H J E M B T Z : ℝ} (a:ℕ) (ep:0<E) (jp:0<J)
    (ha:0≤A) (s:S≤1) (as':A≤S) (h:H≤1) (ah:A≤H) (ds:S-A≤2/J) (dh:H-A≤2/J)
    (mn:0≤M) (box:|B|≤M) (truncated:|T|≤(S^a-A^a)*M)
    (split:E*Z=A^a*B+T) : |Z-H^a*B/E| ≤ 4*a*M/(E*J) := by
  have u:=power_mass_gap ha s as' ds a
  have v:=power_mass_gap ha h ah dh a
  have hv : A^a≤H^a:=pow_le_pow_left₀ ha ah a
  have eqn : Z-H^a*B/E=(T-(H^a-A^a)*B)/E := by
    field_simp
    linarith
  rw [eqn,abs_div,abs_of_pos ep,div_le_div_iff₀ ep (mul_pos ep jp)]
  have p:= mul_le_mul v box (abs_nonneg B)
    (mul_nonneg (Nat.cast_nonneg a) (div_nonneg (by norm_num) jp.le))
  have v2 := abs_sub T ((H^a-A^a)*B)
  rw [abs_mul,abs_of_nonneg (sub_nonneg.mpr hv)] at v2
  have endp : |T-(H^a-A^a)*B|≤2*(a*(2/J))*M := by
    linarith [mul_le_mul_of_nonneg_right u mn]
  have endq:=mul_le_mul_of_nonneg_right endp (mul_nonneg ep.le jp.le)
  convert endq using 1
  field_simp
  ring

/-- Use the two interval sizes directly at arbitrary positive step index h.
Z is the enlarged-group average and B the truncated target cube average. -/
theorem uneven_intervals {h k b J : ℕ} (hp : 0<h) (kp : 0<k) (small : b<h)
    (length : J=h*k+b) {E M B T Z : ℝ} (a : ℕ) (ep:0<E) (mn:0≤M) (box:|B|≤M)
    (truncated : |T| ≤ (((h:ℝ)*k^2+(2*k+1)*b)/J^2)^a*M - (((h:ℝ)*k^2/J^2)^a)*M)
    (split : E*Z=(((h:ℝ)*k^2/J^2)^a)*B+T) :
    |Z-(1/(h:ℝ))^a*B/E| ≤ 4*a*M/(E*J) := by
  have counts:=interval_mass_gap (h:=(h:ℝ)) (k:=(k:ℝ)) (b:=(b:ℝ)) (J:=(J:ℝ))
    (by exact_mod_cast hp) (by exact_mod_cast kp) (Nat.cast_nonneg _) (by exact_mod_cast small)
    (fun v=>by
      have bz : b<1 := by exact_mod_cast v
      exact_mod_cast (show b=0 by omega))
    (by exact_mod_cast length)
  obtain ⟨ha,as',ss,ah,hh,ds,dh⟩:=counts
  have jp : 0<J := by rw [length]; positivity
  apply normalized_cube_error a ep (by exact_mod_cast jp) ha ss as' hh ah ds dh mn box _ split
  exact (by simpa only [sub_mul] using truncated)

end
end ZInQBlueprint.AffineIntervals
#print axioms ZInQBlueprint.AffineIntervals.interval_mass_gap

#print axioms ZInQBlueprint.AffineIntervals.power_mass_gap
#print axioms ZInQBlueprint.AffineIntervals.normalized_cube_error

#print axioms ZInQBlueprint.AffineIntervals.uneven_intervals
