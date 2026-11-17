import WitnessCoordinates
import CharacterProduct

/-! A height bound stated with the size of the absolute field discriminant. -/
namespace Sun28.FiveDescent.ResidueField
open Sun28.Ordinary Sun28.FiveMarkUnits ZInQ.RouteK Height
open Sun28.HeightFibres.Sharp (QuadraticCharacterDiscriminants conductor_from_characters)
noncomputable section

theorem discr_upper (formula : QuadraticCharacterDiscriminants)
    {d e : ℤ} {r w : Omega} (nd : d≠0) (ne : e≠0) (hr:r^2=(d:Omega)) (hw:w^2=(e:Omega)) :
    (NumberField.discr (coords r w)).natAbs ≤64*(primeProduct (parameterPrimes d e))^2 := by
  have pr (p : ℕ) (hp : p∈parameterPrimes d e) : p.Prime :=
    (Finset.mem_union.mp hp).elim Nat.prime_of_mem_primeFactors Nat.prime_of_mem_primeFactors
  exact conductor_from_characters formula _ 1 d e r w pr one_ne_zero nd ne
    (by simp) Finset.subset_union_left Finset.subset_union_right (by simpa using hr) (by simpa using hw)

/-- One absolute-discriminant estimate for the fixed geometric locus.
The displayed exponent is twelve and no cutoff occurs in this estimate. -/
def DiscriminantHeight : Prop :=
  ∀ (z v : Omega) (t : ℚ), z≠0 → v≠0 → z^2=algebraMap ℚ Omega t →
    v^2=(1-z^2)*(2401*z^2-2400)*(375-343*z^2) →
    logHeight₁ ((1-t)⁻¹)≤2^512*((NumberField.discr (coords z v)).natAbs:ℝ)^12+128

theorem original_of_discriminantHeight (formula : QuadraticCharacterDiscriminants)
    (bound : DiscriminantHeight) : OriginalFiveHeight glazerConstant24 oldCutoff := by
  apply glazer_of_full_support
  intro d e sd se x y nx ny pt
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
  have h := bound z v t zn vn hz curve
  have efield : coords z v=coords r w := generated_coordinates r w nx ny
  rw [NumberField.discr_eq_discr_of_algEquiv _ (IntermediateField.equivOfEq efield)] at h
  let U:ℝ:=primeProduct (parameterPrimes d e)
  have budget : ((NumberField.discr (coords r w)).natAbs:ℝ)≤64*U^2 := by
    dsimp only [U]
    exact_mod_cast discr_upper formula sd.ne_zero se.ne_zero hr hw
  have power:=pow_le_pow_left₀ (Nat.cast_nonneg _) budget 12
  have eq : (2:ℝ)^512*(64*U^2)^12 = 2^584*U^24 := by
    rw [show (64:ℝ)=2^6 by norm_num,mul_pow,←pow_mul,←pow_mul,←mul_assoc,←pow_add]
  have coeff : (2:ℝ)^584≤4608^165888 :=
    (pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) (by norm_num : (2:ℝ)≤4608) 584).trans
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤4608) (by decide : 584≤165888))
  have enlarged : (2:ℝ)^584≤2*(4608^165888+6^100) := by
    have h1 : (4608:ℝ)^165888≤4608^165888+6^100 := le_add_of_nonneg_right (by positivity)
    exact coeff.trans (h1.trans (le_mul_of_one_le_left (by positivity) (by norm_num)))
  have cost := mul_le_mul_of_nonneg_left power (show (0:ℝ)≤2^512 by positivity)
  rw [eq] at cost
  exact h.trans (add_le_add (cost.trans (mul_le_mul_of_nonneg_right enlarged (by positivity))) le_rfl)

end
end Sun28.FiveDescent.ResidueField
#print axioms Sun28.FiveDescent.ResidueField.discr_upper
#print axioms Sun28.FiveDescent.ResidueField.original_of_discriminantHeight
