import PoleHeightExact
import PoleDiscriminant

/-! The two small primes divide the numerator of the six-contact modular parameter. -/
namespace ZInQBlueprint.JacobianHeight.ExactFinite
open ZInQ PoleNorm
noncomputable section

private theorem three_dvd_pair (a b : ℤ) : (3:ℤ) ∣ a*b*(a^2-b^2) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp
  push_cast
  generalize (a : ZMod 3) = x
  generalize (b : ZMod 3) = y
  fin_cases x <;> fin_cases y <;> decide

private theorem extra_two (m n : ℤ) : 2*dyadicFactor m n^3 ∣ sineNumerator m n := by
  unfold dyadicFactor
  split
  · rename_i ho
    let a := m/2
    let b := n/2
    have ha : m=2*a+1 := by dsimp [a]; omega
    have hb : n=2*b+1 := by dsimp [b]; omega
    let v := a^2+a-b^2-b
    let w := a^2+a-9*b^2-9*b-2
    have he : m^2-n^2=4*v := by rw [ha,hb]; dsimp [v]; ring
    have hf : m^2-9*n^2=4*w := by rw [ha,hb]; dsimp [w]; ring
    exact ⟨m*n*v*w, by unfold sineNumerator; rw [he,hf]; ring⟩
  · exact ⟨4*m*n*(m^2-n^2)*(m^2-9*n^2), by unfold sineNumerator; ring⟩

private theorem extra_three (m n : ℤ) : 3*triadicFactor m^3 ∣ sineNumerator m n := by
  unfold triadicFactor
  split
  · rename_i ho
    obtain ⟨a,rfl⟩ := Int.dvd_of_emod_eq_zero ho
    obtain ⟨b,h⟩ := three_dvd_pair a n
    refine ⟨8*b*(9*a^2-n^2), ?_⟩
    unfold sineNumerator
    linear_combination 216*(9*a^2-n^2)*h
  · obtain ⟨b,h⟩ := three_dvd_pair m n
    refine ⟨8*b*(m^2-9*n^2), ?_⟩
    unfold sineNumerator
    linear_combination 8*(m^2-9*n^2)*h

/-- Cancelling the cubic content leaves both 2 and 3 in the integral numerator. -/
theorem small_dvd_reduced (m n : ℤ) :
    (2:ℤ) ∣ reducedNumerator m n ∧ (3:ℤ) ∣ reducedNumerator m n := by
  obtain ⟨x,hx⟩ := extra_two m n
  obtain ⟨y,hy⟩ := extra_three m n
  have he := numerator_eq m n
  unfold factor at he
  have hd : dyadicFactor m n=1 ∨ dyadicFactor m n=4 := by unfold dyadicFactor; split <;> decide
  have ht : triadicFactor m=1 ∨ triadicFactor m=3 := by unfold triadicFactor; split <;> decide
  rcases hd with hd|hd <;> rcases ht with ht|ht <;> rw [hd,ht] at he <;>
    rw [hd] at hx <;> rw [ht] at hy <;> norm_num at he hx hy <;> constructor <;> omega

private theorem signed_square_positive {p : ℕ} [hp : Fact p.Prime] {a b : ℤ}
    (ha : a ≠ 0) (hb : b ≠ 0) (ad : (p:ℤ) ∣ a) (bu : ¬(p:ℤ) ∣ b) :
    0 < padicValRat p (-((a:ℚ)/(b:ℚ)^3)^2) := by
  have va : 0 < padicValRat p (a:ℚ) := by
    have had : p ∣ a.natAbs := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr ad)
    have h := one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr ha) had
    rw [padicValRat.of_int]
    change 0 < (padicValNat p a.natAbs : ℤ)
    exact_mod_cast h
  have vb : padicValRat p (b:ℚ) = 0 := by
    rw [padicValRat.of_int]
    have nd : ¬p ∣ b.natAbs := fun d => bu (Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr d))
    change (padicValNat p b.natAbs : ℤ)=0
    rw [padicValNat.eq_zero_of_not_dvd nd]
    rfl
  have a' : (a:ℚ) ≠ 0 := by exact_mod_cast ha
  have b' : (b:ℚ) ≠ 0 := by exact_mod_cast hb
  rw [padicValRat.neg, padicValRat.pow, padicValRat.div a' (pow_ne_zero 3 b'),
    padicValRat.pow, vb]
  omega

/-- On an unmarked rational fibre both exceptional valuations of j are strictly positive. -/
theorem small_orders {u : ℚ} (hu : u ∉ contactSet) :
    0 < padicValRat 2 (SixContact.J u) ∧ 0 < padicValRat 3 (SixContact.J u) := by
  have hu0 : u ≠ 0 := fun e => hu (e ▸ (by decide : (0 : ℚ) ∈ contactSet))
  let t := parameter u
  have hc : IsCoprime t.num (t.den:ℤ) := by rw [Int.isCoprime_iff_gcd_eq_one]; exact t.reduced
  have he : SixContact.J u = -((reducedNumerator t.num t.den:ℚ)/(reduced t.num t.den:ℚ)^3)^2 :=
    (j_eq_signed_square u hu0).trans (by rw [sine_fraction hc])
  have ha : reducedNumerator t.num t.den ≠ 0 := by
    intro h
    have h' : SixContact.J u=0 := by simp [he,h]
    exact (CoarseConic.unmarked_range hu).2.ne h'
  have hb := (reduced_pos hc (by exact_mod_cast t.den_pos)).ne'
  rw [he]
  exact ⟨signed_square_positive ha hb (small_dvd_reduced _ _).1 (reduced_units hc).1,
     signed_square_positive ha hb (small_dvd_reduced _ _).2 (reduced_units hc).2⟩

end
end ZInQBlueprint.JacobianHeight.ExactFinite
#print axioms ZInQBlueprint.JacobianHeight.ExactFinite.small_dvd_reduced
#print axioms ZInQBlueprint.JacobianHeight.ExactFinite.small_orders
