import DirectCharts
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The lower Newton polygon at the zero centre of the monic contact sextic. -/

namespace ZInQBlueprint.OddContact
open Polynomial IsLocalRing IsDiscreteValuationRing ZInQBlueprint.DirectCharts
open ZInQBlueprint.IntegralSextic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- In a zero sum of three terms, a single term cannot have strictly lowest order. -/
private theorem no_unique_min {a b c : R} (hs : a + b + c = 0)
    (hab : addVal R a < addVal R b) (hac : addVal R a < addVal R c) : False := by
  have ha : a = -(b+c) := by linear_combination hs
  have hneg : addVal R a = addVal R (b+c) := by rw [ha,AddValuation.map_neg]
  have hlt : addVal R a < addVal R (b+c) :=
    lt_of_lt_of_le (lt_min hab hac) addVal_add
  exact hlt.ne hneg

/-- The three orders at a root near zero are 3d, n+d and 2n.
When n is odd the only integral tie at their minimum occurs at d=n. -/
theorem odd_orders {d n : ℕ} (hn : Odd n)
    (hA : ¬(3*d < n+d ∧ 3*d < 2*n))
    (hB : ¬(n+d < 3*d ∧ n+d < 2*n))
    (hC : ¬(2*n < 3*d ∧ 2*n < n+d)) : d = n := by
  obtain ⟨k,hk⟩ := hn
  omega

/-- Every root reducing to zero in the DVR has precisely the odd order of t. -/
theorem root_valuation (h₂ : IsUnit (2 : R)) (h₃ : IsUnit (3 : R))
    {t x : R} {n : ℕ} (hn : Odd n) (ht : addVal R t = (n : ℕ∞))
    (hx : (monicSextic t).IsRoot x) (hres : residue R x = 0) :
    addVal R x = (n : ℕ∞) := by
  have hu₂ := (residue_ne_zero_iff_isUnit (2:R)).mpr h₂
  have hu₃ := (residue_ne_zero_iff_isUnit (3:R)).mpr h₃
  have h₆ : IsUnit (6:R) := by convert h₂.mul h₃ using 1; norm_num
  have hu₆ := (residue_ne_zero_iff_isUnit (6:R)).mpr h₆
  have ux₂ : IsUnit (x+2) := (residue_ne_zero_iff_isUnit _).mp (by simpa [hres] using hu₂)
  have ux₃ : IsUnit (x+3) := (residue_ne_zero_iff_isUnit _).mp (by simpa [hres] using hu₃)
  have ux₆ : IsUnit (x^2+4*x+6) :=
    (residue_ne_zero_iff_isUnit _).mp (by simpa [hres] using hu₆)
  let A := (x*(x+3))^3
  let B := t*(x*(x+3))*(x+2)*(x^2+4*x+6)
  let C := t^2*(x+2)^3
  have hs : A + -B + C = 0 := by
    change (monicSextic t).eval x = 0 at hx
    rw [monic_eval] at hx
    simpa [form,alpha,beta,gamma,sub_eq_add_neg,A,B,C] using hx
  have ht0 : t ≠ 0 := by
    intro H
    simp [H] at ht
  have hx0 : x ≠ 0 := by
    intro H
    have h : t^2 * (2:R)^3 = 0 := by simpa [A,B,C,H] using hs
    exact (mul_ne_zero (pow_ne_zero _ ht0) (pow_ne_zero _ h₂.ne_zero)) h
  obtain ⟨d,hd'⟩ := ENat.ne_top_iff_exists.mp (mt addVal_eq_top_iff.mp hx0)
  have hd : addVal R x = (d:ℕ∞) := hd'.symm
  have va : addVal R A = ((3*d:ℕ):ℕ∞) := by
    simp [A,hd,addVal_eq_zero_iff.mpr ux₃,nsmul_eq_mul]
  have vb : addVal R (-B) = ((n+d:ℕ):ℕ∞) := by
    simp [B,hd,ht,addVal_eq_zero_iff.mpr ux₃,
      addVal_eq_zero_iff.mpr ux₂,addVal_eq_zero_iff.mpr ux₆]
  have vc : addVal R C = ((2*n:ℕ):ℕ∞) := by
    simp [C,ht,addVal_eq_zero_iff.mpr ux₂,nsmul_eq_mul]
  have hab : ¬(3*d < n+d ∧ 3*d < 2*n) := by
    rintro ⟨h₁,h₂'⟩
    apply no_unique_min hs
    · rw [va,vb]; exact_mod_cast h₁
    · rw [va,vc]; exact_mod_cast h₂'
  have hbc : ¬(n+d < 3*d ∧ n+d < 2*n) := by
    rintro ⟨h₁,h₂'⟩
    apply no_unique_min (a := -B) (b := A) (c := C) (by linear_combination hs)
    · rw [va,vb]; exact_mod_cast h₁
    · rw [vb,vc]; exact_mod_cast h₂'
  have hca : ¬(2*n < 3*d ∧ 2*n < n+d) := by
    rintro ⟨h₁,h₂'⟩
    apply no_unique_min (a := C) (b := A) (c := -B) (by linear_combination hs)
    · rw [va,vc]; exact_mod_cast h₁
    · rw [vb,vc]; exact_mod_cast h₂'
  simpa [odd_orders hn hab hbc hca] using hd

#print axioms ZInQBlueprint.OddContact.odd_orders
#print axioms ZInQBlueprint.OddContact.root_valuation
end ZInQBlueprint.OddContact
