import ApplicationLemmas
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.IntervalCases

namespace ZInQBlueprint

/-- The rational covering in x-coordinates, including its points at infinity. -/
def Cover (d a b : ℚ) : Prop :=
  (IsSquare a ∧ IsSquare b) ∨
    ∃ x : ℚ, IsSquare (x/a) ∧ IsSquare ((x-d)/b) ∧ IsSquare ((x+d)/(a*b))

/-- A square integer never has absolute value seven modulo eight. -/
theorem square_abs_mod_eight (a : ℤ) (seven : a.natAbs % 8=7) :
    ¬ IsSquare (a : ℚ) ∧ ¬ IsSquare (-(a : ℚ)) := by
  have noNat : ¬ IsSquare a.natAbs := by
    rintro ⟨r,hr⟩
    rw [hr, Nat.mul_mod] at seven
    have lt := Nat.mod_lt r (by decide : 0<8)
    interval_cases h : r%8 <;> norm_num at seven
  have descend (b : ℤ) (hb : IsSquare (b : ℚ)) : IsSquare b.natAbs := by
    obtain ⟨r,hr⟩ := Rat.isSquare_intCast_iff.mp hb
    exact ⟨r.natAbs, by rw [hr, Int.natAbs_mul]⟩
  refine ⟨fun h => noNat (descend a h), fun h => ?_⟩
  apply noNat
  simpa using descend (-a) (by simpa using h)

/-- For a signed class outside ±1, a point on the covering gives the prescribed
abscissa. At x=0 the other two square roots would make -a a rational square. -/
theorem point_of_cover {d a b : ℚ} (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (noSquare : ¬ IsSquare a) (noNegSquare : ¬ IsSquare (-a))
    (cover : Cover d a b) :
    ∃ x y : ℚ, y^2=x^3-d^2*x ∧ x ≠ 0 ∧ IsSquare (x/a) := by
  rcases cover with ⟨h,_⟩ | ⟨x,⟨r,hr⟩,⟨s,hs⟩,⟨t,ht⟩⟩
  · exact (noSquare h).elim
  have eqr : x=(r*r)*a := (div_eq_iff ha).mp hr
  have eqs : x-d=(s*s)*b := (div_eq_iff hb).mp hs
  have eqt : x+d=(t*t)*(a*b) := (div_eq_iff (mul_ne_zero ha hb)).mp ht
  have hx : x ≠ 0 := by
    rintro rfl
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp_all
    apply noNegSquare
    refine ⟨s/t, ?_⟩
    field_simp
    apply mul_right_cancel₀ hb
    linear_combination eqs + eqt
  refine ⟨x,a*b*r*s*t,?_,hx,⟨r,hr⟩⟩
  calc (a*b*r*s*t)^2 = (r*r*a)*(s*s*b)*(t*t*(a*b)) := by ring
       _ = x*(x-d)*(x+d) := by rw [←eqr,←eqs,←eqt]
       _ = _ := by ring

/-- Final step of certified rank for the exact signed congruence class. -/
theorem prescribed_class_of_cover {d : ℕ} {a b : ℤ} (hd : d%8=5) (ha : a.natAbs%8=7)
    (hb : b≠0) (cover : Cover d a b) :
    ∃ x y : ℚ, y^2=x^3-(d:ℚ)^2*x ∧ x≠0 ∧ IsSquare (x/a) := by
  have hd0 : d≠0 := by omega
  have ha0 : a≠0 := by rintro rfl; norm_num at ha
  have hs := square_abs_mod_eight a ha
  exact point_of_cover (by exact_mod_cast hd0) (by exact_mod_cast ha0)
    (by exact_mod_cast hb) hs.1 hs.2 cover

#print axioms square_abs_mod_eight
#print axioms point_of_cover
#print axioms prescribed_class_of_cover
end ZInQBlueprint
