import ZInQKernel.Multiplication.Completeness.PoleValuationsAux
import Mathlib.Data.Nat.Squarefree

/-! The parity of the six-contact product, including the denominator primes,
and the only possible cancellations of odd contact orders. -/
open ZInQ ZInQ.Mult
namespace ZInQBlueprint.OddSupport
noncomputable section
variable {p : ℕ} [hp : Fact p.Prime] {u : ℚ}

/-- A denominator prime contributes six times the same negative order. At every
other prime, a product of odd order has at least one positive odd contact. -/
theorem odd_poly_contact (hu : u ∉ contactSet) (h : Odd (padicValRat p (contactPoly u))) :
    IsOddContactPrime u p := by
  apply Classical.byContradiction
  intro hnone
  have hn (c : ℚ) (hc : c ∈ contactSet) : u-c ≠ 0 := fun hz => hu (sub_eq_zero.mp hz ▸ hc)
  rw [contactPoly_eq_prod,padicValRat_finset_prod _ hn] at h
  apply (Int.not_even_iff_odd.mpr h)
  by_cases hneg : padicValRat p u < 0
  · have same (c : ℚ) (hc : c ∈ contactSet) : padicValRat p (u-c) = padicValRat p u := by
      obtain ⟨z,_,rfl⟩ := mem_contactSet_iff.mp hc
      exact padicValRat_sub_int_of_neg hneg z
    rw [Finset.sum_congr rfl same,Finset.sum_const,show contactSet.card=6 by decide]
    exact ⟨3*padicValRat p u,by simp only [nsmul_eq_mul]; push_cast; ring⟩
  · apply Finset.even_sum
    intro c hc
    obtain ⟨z,hz,rfl⟩ := mem_contactSet_iff.mp hc
    have le := padicValRat.min_le_padicValRat_add (p:=p) (q:=u) (r:=-(z:ℚ))
      (by rw [← sub_eq_add_neg]; exact hn _ hc)
    rw [padicValRat.neg,←sub_eq_add_neg] at le
    have hnn := padicValRat_intCast_nonneg (p:=p) z
    have nonneg : 0 ≤ padicValRat p (u-z) := (le_min (le_of_not_gt hneg) hnn).trans le
    by_contra nev
    have o := Int.not_even_iff_odd.mp nev
    have ne : padicValRat p (u-z) ≠ 0 := fun e => nev (e ▸ Even.zero)
    exact hnone ⟨hp.out,z,hc,lt_of_le_of_ne nonneg ne.symm,o⟩

/-- Distinct marked integers remain distinct modulo every prime greater than five. -/
theorem contact_difference_unit (h5 : 5<p) {a b : ℚ} (ha : a ∈ contactSet)
    (hb : b ∈ contactSet) (hne : a ≠ b) : padicValRat p (a-b)=0 := by
  obtain ⟨a,hai,rfl⟩ := mem_contactSet_iff.mp ha
  obtain ⟨b,hbi,rfl⟩ := mem_contactSet_iff.mp hb
  have catalog : ∀ a ∈ contactInts, ∀ b ∈ contactInts, a≠b → (a-b).natAbs ∣ 120^2 := by decide
  have hab : a≠b := fun e => hne (by rw [e])
  have ndiv : ¬(p:ℤ) ∣ a-b := by
    intro hd
    have hn : p ∣ (a-b).natAbs := by exact Int.natAbs_dvd_natAbs.mpr hd
    have bad := hp.out.dvd_of_dvd_pow (hn.trans (catalog a hai b hbi hab))
    have hfac : p ∣ Nat.factorial 5 := by simpa only [show Nat.factorial 5=120 by decide] using bad
    exact (not_le_of_gt h5) ((hp.out.dvd_factorial).mp hfac)
  rw [←Int.cast_sub,padicValRat.of_int,padicValInt.eq_zero_of_not_dvd ndiv]
  rfl

/-- Beyond 2,3,5, a single positive contact accounts for the valuation of the whole product. -/
theorem contact_order_eq (hu : u ∉ contactSet) (h5 : 5<p) {a : ℚ}
    (ha : a ∈ contactSet) (oa : 0 < padicValRat p (u-a)) :
    padicValRat p (contactPoly u) = padicValRat p (u-a) := by
  have hn (c : ℚ) (hc : c ∈ contactSet) : u-c ≠ 0 := fun hz => hu (sub_eq_zero.mp hz ▸ hc)
  rw [contactPoly_eq_prod,padicValRat_finset_prod _ hn,Finset.sum_eq_single a _ (fun h => (h ha).elim)]
  intro b hb hba
  have eqn : u-b=(a-b)+(u-a) := by ring
  rw [eqn,padicValRat.add_eq_of_lt (eqn ▸ hn b hb) (sub_ne_zero.mpr hba.symm) (hn a ha) (by
    rw [contact_difference_unit h5 ha hb hba.symm]; exact oa),contact_difference_unit h5 ha hb hba.symm]

theorem odd_poly_iff (hu : u ∉ contactSet) (h5 : 5<p) :
    Odd (padicValRat p (contactPoly u)) ↔ IsOddContactPrime u p := by
  refine ⟨odd_poly_contact hu,?_⟩
  rintro ⟨_,a,ha,pos,odd⟩
  rwa [contact_order_eq hu h5 ha pos]

#print axioms odd_poly_contact
#print axioms contact_difference_unit
#print axioms contact_order_eq
#print axioms odd_poly_iff
end
end ZInQBlueprint.OddSupport
