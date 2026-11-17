import ZInQKernel.Multiplication.Completeness.PoleValuationsAux
import Mathlib.Tactic

/-! Five transported ordinary contacts and the rational detector of Sun, section 4. -/
open ZInQ.Mult
namespace Sun28.Ordinary

def marks : Finset ℚ := {0,-1/2,-1,1/2399,-32/407}
def separation : ℕ := 9432571507590

def fiveProduct (t : ℚ) := ∏ a ∈ marks, (t-a)
def detector (A t : ℚ) := fiveProduct t/(A^5*(t-3)^6)

/-- All numerators and denominators of pairwise differences are supported
at 2,3,5,7,11,37,179,257,2399, including differences from the guard point 3. -/
theorem separation_arithmetic : separation=2*3*5*7*11*37*179*257*2399 ∧
    ∀ a ∈ insert 3 marks, ∀ b ∈ insert 3 marks, a≠b →
      (a-b).num.natAbs ∣ separation^5 ∧ (a-b).den ∣ separation^5 := by
  norm_num [marks,separation,Nat.dvd_iff_mod_eq_zero]

theorem mark_difference_unit {p : ℕ} [hp : Fact p.Prime] (good : ¬p ∣ separation)
    {a b : ℚ} (ha : a ∈ insert 3 marks) (hb : b ∈ insert 3 marks) (hne : a≠b) :
    padicValRat p (a-b)=0 := by
  obtain ⟨num,den⟩ := separation_arithmetic.2 a ha b hb hne
  have too : ¬p ∣ separation^5 := fun h => good (hp.out.dvd_of_dvd_pow h)
  have nnum : ¬p ∣ (a-b).num.natAbs := fun h => too (h.trans num)
  have nden : ¬p ∣ (a-b).den := fun h => too (h.trans den)
  simp only [padicValRat_def,padicValInt,padicValNat.eq_zero_of_not_dvd nnum,
    padicValNat.eq_zero_of_not_dvd nden,Nat.cast_zero,sub_self]

theorem other_marks_unit {p : ℕ} [Fact p.Prime] (good : ¬p ∣ separation)
    {t a b : ℚ} (ha : a ∈ marks) (hb : b ∈ insert 3 marks) (ab : a≠b)
    (tb : t≠b) (pos : 0<padicValRat p (t-a)) : padicValRat p (t-b)=0 := by
  have un := mark_difference_unit good (Finset.mem_insert_of_mem ha) hb ab
  have nz : t-a ≠ 0 := by intro h; simp [h] at pos
  have eqn : t-b=(a-b)+(t-a) := by ring
  rw [eqn,padicValRat.add_eq_of_lt (eqn ▸ sub_ne_zero.mpr tb) (sub_ne_zero.mpr ab) nz (un ▸ pos),un]

/-- The original scale A must be a nonzero square, as in all three ordinary detectors. -/
theorem detector_contact {p : ℕ} [Fact p.Prime] (good : ¬p ∣ separation)
    {t a s : ℚ} (unmarked : t ∉ marks) (guard : t ≠ 3) (scale : s≠0)
    (ha : a ∈ marks) (pos : 0<padicValRat p (t-a)) (odd : Odd (padicValRat p (t-a))) :
    detector (s^2) t≠0 ∧ padicValRat p (t-3)=0 ∧ Odd (padicValRat p (detector (s^2) t)) := by
  have live (b : ℚ) (hb : b ∈ marks) : t-b≠0 := fun h => unmarked (sub_eq_zero.mp h ▸ hb)
  have a3 : a≠3 := fun h => (by norm_num [marks] : (3:ℚ)∉marks) (h ▸ ha)
  have gu := other_marks_unit good ha (Finset.mem_insert_self ..) a3 guard pos
  have prod : padicValRat p (fiveProduct t)=padicValRat p (t-a) := by
    rw [fiveProduct,padicValRat_finset_prod marks live,Finset.sum_eq_single a]
    · intro b hb ba
      exact other_marks_unit good ha (Finset.mem_insert_of_mem hb) ba.symm (sub_ne_zero.mp (live b hb)) pos
    · intro h
      exact (h ha).elim
  have num : fiveProduct t≠0 := Finset.prod_ne_zero_iff.mpr live
  have den := mul_ne_zero (pow_ne_zero 5 (pow_ne_zero 2 scale)) (pow_ne_zero 6 (sub_ne_zero.mpr guard))
  unfold detector
  refine ⟨div_ne_zero num den,gu,?_⟩
  rw [padicValRat.div num den,padicValRat.mul (pow_ne_zero 5 (pow_ne_zero 2 scale))
    (pow_ne_zero 6 (sub_ne_zero.mpr guard)),padicValRat.pow,padicValRat.pow,padicValRat.pow,gu,prod]
  obtain ⟨j,hj⟩ := odd
  exact ⟨j-5*padicValRat p s,by omega⟩

end Sun28.Ordinary
#print axioms Sun28.Ordinary.separation_arithmetic
#print axioms Sun28.Ordinary.mark_difference_unit
#print axioms Sun28.Ordinary.detector_contact
