import FamilyGuards
import Mathlib.Data.ZMod.Basic

/-! A rational obstruction at 5 for divisors used in the 66-variable reduction.
The row numbers refer to the original 222-coordinate table. -/
namespace FamilyWidth222

def octic {R : Type*} [CommRing R] (a b : R) : R :=
  35893742479489*a^8 - 122376041313918*a^6*b^2 +
  192222345736537*a^4*b^4 - 141822723674536*a^2*b^6 + 39896049934224*b^8

private theorem mod_five : ∀ a b : ZMod 5, octic a b = 0 → a = 0 ∧ b = 0 := by decide

theorem octic_no_rational_root (x : ℚ) : octic x 1 ≠ 0 := by
  intro h
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
  have hn : (x.num : ℚ) = x*(x.den : ℚ) := (div_eq_iff hd).mp x.num_div_den
  have hQ : octic (x.num : ℚ) (x.den : ℚ) = 0 := by
    rw [hn]
    unfold octic at *
    linear_combination (x.den : ℚ)^8 * h
  have hZ : octic x.num (x.den : ℤ) = 0 := by
    unfold octic at hQ ⊢
    exact_mod_cast hQ
  have red := congrArg (fun z : ℤ => (z : ZMod 5)) hZ
  have hz : octic (x.num : ZMod 5) ((x.den : ℤ) : ZMod 5) = 0 := by
    simpa [octic] using red
  obtain ⟨ha,hb⟩ := mod_five _ _ hz
  have ha' := (ZMod.intCast_zmod_eq_zero_iff_dvd x.num 5).mp ha
  have hb' := (ZMod.intCast_zmod_eq_zero_iff_dvd (x.den : ℤ) 5).mp hb
  have a5 : 5 ∣ x.num.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ha')
  have b5 : 5 ∣ x.den := Int.natCast_dvd_natCast.mp hb'
  have contra := Nat.dvd_gcd a5 b5
  rw [x.reduced.gcd_eq_one] at contra
  norm_num at contra

theorem second_detector (v92 v93 v94 v95 v96 h v122 : ℚ) (hh : h ≠ 0)
    (r43 : v92^2 - 2*v92*h - v93*h + h^2 = 0)
    (r44 : v93^2 - v94*h = 0)
    (r73 : v93*v94 - h*v122 = 0)
    (r45 : -141822723674536*v93*h + 35893742479489*v93*v122 +
      192222345736537*v94*h - 3813373161796*v95*v96 + 39896049934224*h*h -
      122376041313918*h*v122 = 0) : v96 ≠ 0 := by
  let t := (v92-h)/h
  have hd : v92 = (t+1)*h := by dsimp [t]; field_simp; ring
  have h93 : v93 = t^2*h := by
    apply mul_right_cancel₀ hh
    rw [hd] at r43
    linear_combination -r43
  have h94 : v94 = t^4*h := by
    apply mul_right_cancel₀ hh
    rw [h93] at r44
    linear_combination -r44
  have h122 : v122 = t^6*h := by
    apply mul_right_cancel₀ hh
    rw [h93,h94] at r73
    linear_combination -r73
  intro he
  rw [h93,h94,h122,he] at r45
  have hzero : octic t 1 * h^2 = 0 := by
    unfold octic
    linear_combination r45
  exact octic_no_rational_root t ((mul_eq_zero.mp hzero).resolve_right (pow_ne_zero _ hh))

end FamilyWidth222
#print axioms FamilyWidth222.octic_no_rational_root
#print axioms FamilyWidth222.second_detector
