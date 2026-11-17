import ContactDiscriminant

/-! The original bound as an inequality for closed points of a single fixed curve. -/
namespace Sun28.FiveDescent.ResidueField
open Sun28.Ordinary Sun28.FiveMarkUnits ZInQ.RouteK Height
noncomputable section

/-- Only the first coordinate squared is required to be rational. The equation
makes the second square rational automatically. -/
def FieldHeight (H : ℝ) : Prop :=
  ∀ (z v : Omega) (t : ℚ), z≠0 → v≠0 → z^2=algebraMap ℚ Omega t →
    v^2=(1-z^2)*(2401*z^2-2400)*(375-343*z^2) →
    logHeight₁ ((1-t)⁻¹)≤H*(primeProduct (fieldPrimes z v):ℝ)^24

theorem original_iff_fieldHeight (H : ℝ) : OriginalFiveHeight H oldCutoff ↔ FieldHeight H := by
  rw [original_iff_twist H]
  constructor
  · intro bound z v t nz nv hz hv
    have cubic_eq : v^2=algebraMap ℚ Omega (cubic t) := by
      rw [hv,hz]
      simp [cubic]
    have tn : t≠0 := by
      rintro rfl
      rw [map_zero] at hz
      exact pow_ne_zero 2 nz hz
    have cn : cubic t≠0 := by
      intro zero
      rw [zero,map_zero] at cubic_eq
      exact pow_ne_zero 2 nv cubic_eq
    obtain ⟨sd,x,nx,ht⟩ := sqf_spec tn
    obtain ⟨se,y,ny,hc⟩ := sqf_spec cn
    let d:=sqf t
    let e:=sqf (cubic t)
    have sx : (d:ℚ)*x^2=t := ht.symm
    have sy : (e:ℚ)*y^2=cubic t := hc.symm
    have pt : (e:ℚ)*y^2=sextic d x := by simp only [sextic,sx,sy]
    let r:=z/algebraMap ℚ Omega x
    let w:=v/algebraMap ℚ Omega y
    have xn : algebraMap ℚ Omega x≠0 := (map_ne_zero (algebraMap ℚ Omega)).mpr nx
    have yn : algebraMap ℚ Omega y≠0 := (map_ne_zero (algebraMap ℚ Omega)).mpr ny
    have algx := congrArg (algebraMap ℚ Omega) sx
    have algy := congrArg (algebraMap ℚ Omega) sy
    simp only [map_mul,map_intCast,map_pow] at algx algy
    have hr : r^2=(d:Omega) := by
      rw [show r^2=z^2/(algebraMap ℚ Omega x)^2 from div_pow ..,hz]
      exact (div_eq_iff (pow_ne_zero 2 xn)).mpr algx.symm
    have hw : w^2=(e:Omega) := by
      rw [show w^2=v^2/(algebraMap ℚ Omega y)^2 from div_pow ..,cubic_eq]
      exact (div_eq_iff (pow_ne_zero 2 yn)).mpr algy.symm
    have same := generated_coordinates r w nx ny
    change coords ((z/algebraMap ℚ Omega x)*algebraMap ℚ Omega x)
      ((v/algebraMap ℚ Omega y)*algebraMap ℚ Omega y)=coords r w at same
    rw [div_mul_cancel₀ _ xn,div_mul_cancel₀ _ yn] at same
    have primes : fieldPrimes z v=twistPrimes d e := by
      calc
        _ = fieldPrimes r w := by unfold fieldPrimes; rw [NumberField.discr_eq_discr_of_algEquiv _ (IntermediateField.equivOfEq same)]
        _ = _ := fieldPrimes_eq sd se hr hw
    rw [primes]
    simpa only [parameter,sx] using bound d e sd se x y nx ny pt
  · intro bound d e sd se x y nx ny pt
    obtain ⟨r,hr⟩ := IsAlgClosed.exists_pow_nat_eq (d:Omega) (by decide : 0<2)
    obtain ⟨w,hw⟩ := IsAlgClosed.exists_pow_nat_eq (e:Omega) (by decide : 0<2)
    let z:=r*algebraMap ℚ Omega x
    let v:=w*algebraMap ℚ Omega y
    let t:ℚ:=(d:ℚ)*x^2
    have rn : r≠0 := by
      rintro rfl
      simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at hr
      exact sd.ne_zero (by exact_mod_cast hr.symm)
    have wn : w≠0 := by
      rintro rfl
      simp only [ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,zero_pow] at hw
      exact se.ne_zero (by exact_mod_cast hw.symm)
    have zn : z≠0 := mul_ne_zero rn ((map_ne_zero (algebraMap ℚ Omega)).mpr nx)
    have vn : v≠0 := mul_ne_zero wn ((map_ne_zero (algebraMap ℚ Omega)).mpr ny)
    have hz : z^2=algebraMap ℚ Omega t := by simp [z,t,mul_pow,hr]
    have curve := (fixed_point_iff Omega d e r w (by simpa using hr) (by simpa using hw) x y).mp pt
    have out := bound z v t zn vn hz curve
    have same : coords z v=coords r w := generated_coordinates r w nx ny
    have primes : fieldPrimes z v=twistPrimes d e := by
      calc
        _ = fieldPrimes r w := by unfold fieldPrimes; rw [NumberField.discr_eq_discr_of_algEquiv _ (IntermediateField.equivOfEq same)]
        _ = _ := fieldPrimes_eq sd se hr hw
    rw [primes] at out
    exact out

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.original_iff_fieldHeight
