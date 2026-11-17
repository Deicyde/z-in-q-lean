import ReducedNorm
import ZInQKernel.Hypotheses.JHeight

/-! Exact rational height of the published Hauptmodul in terms of a positive integer. -/
namespace ZInQBlueprint.PoleNorm
open ZInQ
noncomputable section

def parameter (u : ℚ) : ℚ := 5+120/u
def denominatorRoot (u : ℚ) : ℤ := reduced (parameter u).num (parameter u).den

private theorem primitive (t : ℚ) : IsCoprime t.num (t.den:ℤ) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  exact t.reduced

theorem root_pos (u : ℚ) : 0 < denominatorRoot u :=
  reduced_pos (primitive _) (by exact_mod_cast (parameter u).den_pos)

private def coordinateSine (x : ℚ) : ℚ := 8*x*(x^2-1)*(x^2-9)/(x^2+3)^3

theorem coordinate_identity (u : ℚ) (hu : u ≠ 0) :
    JHeight.Jmap u = -(coordinateSine (parameter u))^2 := by
  have hG : 7*u^2+300*u+3600 ≠ 0 := JHeight.G_ne_zero u
  have hN : (parameter u)^2+3 = 4*(7*u^2+300*u+3600)/u^2 := by
    unfold parameter
    field_simp [hu]
    ring
  have hU : 8*(parameter u)*((parameter u)^2-1)*((parameter u)^2-9) =
      15360*(u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60))/u^6 := by
    unfold parameter
    field_simp [hu]
    ring
  unfold JHeight.Jmap coordinateSine
  rw [hU,hN]
  generalize u*(u+15)*(u+20)*(u+24)*(u+30)*(u+60)=f
  generalize hg : 7*u^2+300*u+3600=g at *
  field_simp [hu,hG]
  ring

private theorem sine_of_fraction (p q : ℤ) (hq : 0 < q) :
    coordinateSine ((p:ℚ)/q) = sine p q := by
  have hq' : (q:ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have npos : 0 < (p:ℚ)^2+3*(q:ℚ)^2 := by positivity
  have xpos : 0 < ((p:ℚ)/q)^2+3 := by positivity
  unfold coordinateSine sine sineNumerator norm
  push_cast
  field_simp [hq',npos.ne',xpos.ne']

theorem j_eq_signed_square (u : ℚ) (hu : u ≠ 0) :
    JHeight.Jmap u = -(sine (parameter u).num (parameter u).den)^2 := by
  rw [coordinate_identity u hu]
  congr 2
  set t := parameter u
  have h := sine_of_fraction t.num t.den (by exact_mod_cast t.den_pos)
  simpa only [Int.cast_natCast,Rat.num_div_den] using h

theorem j_denominator (u : ℚ) (hu : u ≠ 0) :
    ((JHeight.Jmap u).den:ℤ) = denominatorRoot u ^6 := by
  rw [j_eq_signed_square u hu,Rat.neg_den,Rat.den_pow,Nat.cast_pow]
  rw [sine_den (primitive _) (by exact_mod_cast (parameter u).den_pos)]
  unfold denominatorRoot
  ring

/-- The reduced denominator gives the entire height at every unmarked input. -/
theorem j_height_exact (u : ℚ) (hu : u ≠ 0) :
    ratHeight (JHeight.Jmap u) = 6*Real.log (denominatorRoot u:ℝ) := by
  let j := JHeight.Jmap u
  have habs : |j| ≤ 1 := by
    dsimp [j]
    rw [j_eq_signed_square u hu,abs_neg,abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (sine_abs_le_one (by exact_mod_cast (parameter u).den_pos))
  have hdq : (0:ℚ) < j.den := by exact_mod_cast j.den_pos
  have hle : |(j.num:ℚ)| ≤ j.den := by
    rw [← Rat.num_div_den j,abs_div,abs_of_pos hdq,div_le_one hdq] at habs
    exact habs
  have hR : |(j.num:ℝ)| ≤ j.den := by exact_mod_cast hle
  change Real.log (max |(j.num:ℝ)| (j.den:ℝ))=_
  rw [max_eq_right hR]
  have hden : (j.den:ℝ)=(denominatorRoot u:ℝ)^6 := by exact_mod_cast j_denominator u hu
  rw [hden,Real.log_pow]
  norm_num

/-- All quantitative constants in the public j-height hypothesis are preserved. -/
theorem jHeight_iff_denominator (S : Finset ℕ) : JHeight.JHeightBound S ↔
    ∀ u : ℚ, u ∉ contactSet →
      6*Real.log (denominatorRoot u:ℝ) ≤ (40*10000*2^24+22:ℝ) *
        JHeight.heightX heightD * (contactSupport S u:ℝ)^24 := by
  have at_u (u : ℚ) (h : u ∉ contactSet) := j_height_exact u (by
    rintro rfl
    exact h (by norm_num [contactSet]))
  unfold JHeight.JHeightBound
  constructor
  · intro H u hu
    rw [← at_u u hu]
    exact H u hu
  · intro H u hu
    rw [at_u u hu]
    exact H u hu

theorem sixContact_of_denominator
    (h : ∀ u : ℚ, u ∉ contactSet →
      6*Real.log (denominatorRoot u:ℝ) ≤ (40*10000*2^24+22:ℝ) *
        JHeight.heightX heightD * (contactSupport Mult.S_mul u:ℝ)^24) : SixContactMin :=
  JHeight.sixContactMin_of_jHeightBound ((jHeight_iff_denominator _).mpr h)

end
end ZInQBlueprint.PoleNorm
#print axioms ZInQBlueprint.PoleNorm.j_eq_signed_square
#print axioms ZInQBlueprint.PoleNorm.j_denominator
#print axioms ZInQBlueprint.PoleNorm.j_height_exact
#print axioms ZInQBlueprint.PoleNorm.jHeight_iff_denominator
#print axioms ZInQBlueprint.PoleNorm.sixContact_of_denominator
