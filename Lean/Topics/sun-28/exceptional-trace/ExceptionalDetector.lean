import PoleParameters
import ZInQKernel.Multiplication.Completeness.PoleLocal

/-! The rational valuation of the five factors at each fixed preparation prime. -/
namespace Sun28.Exceptional
open Sun28.Ordinary ZInQ.Mult

/-- All five marked abscissas and the guard 3 have order at least −1 at the
nine fixed rational primes. We leave zero in the catalogue using padicValRat p 0=0. -/
theorem marks_order {p : ℕ} [hp : Fact p.Prime] (fixed : p∈({2,3,5,7,11,13,17,19,23}:Finset ℕ))
    {b : ℚ} (mark : b∈insert 3 marks) : -1≤padicValRat p b := by
  have den : b.den=1 ∨ b.den=2 ∨ b.den=2399 ∨ b.den=407 := by
    simp only [marks,Finset.mem_insert,Finset.mem_singleton] at mark
    rcases mark with h|h|h|h|h|h <;> subst b <;> norm_num
  have sq : ¬p^2∣b.den := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at fixed
    rcases fixed with h|h|h|h|h|h|h|h|h <;> subst p <;> rcases den with h|h|h|h <;> rw [h] <;> decide
  have less : padicValNat p b.den<2 := lt_of_not_ge (fun h => sq ((padicValNat_dvd_iff_le b.den_ne_zero).mpr h))
  rw [padicValRat_def]
  omega

theorem detector_orders {p : ℕ} [Fact p.Prime] {A u w t : ℚ}
    (an : A≠0) (un : u≠0) (wn : w≠0) (slope : t=A*u/w^2) (unit : padicValRat p u=0)
    (lower : padicValRat p A-padicValRat p (w^2)< -1)
    (marksBound : ∀ b∈insert 3 marks,-1≤padicValRat p b) :
    t∉marks ∧ t≠3 ∧ detector A t≠0 ∧
    padicValRat p (t-3)=padicValRat p A-padicValRat p (w^2) ∧
    padicValRat p (detector A t)=padicValRat p (w^2)-6*padicValRat p A := by
  have tn : t≠0 := slope ▸ div_ne_zero (mul_ne_zero an un) (pow_ne_zero _ wn)
  have tv : padicValRat p t=padicValRat p A-padicValRat p (w^2) := by
    rw [slope,padicValRat.div (mul_ne_zero an un) (pow_ne_zero _ wn),padicValRat.mul an un,unit,add_zero]
  have diff (b : ℚ) (member : b∈insert 3 marks) : t≠b ∧ padicValRat p (t-b)=padicValRat p t := by
    have lt : padicValRat p t<padicValRat p b := lt_of_lt_of_le (tv ▸ lower) (marksBound _ member)
    have ne : t≠b := fun e=> (e ▸ lt).false
    refine ⟨ne,?_⟩
    by_cases z : b=0
    · simp [z]
    · rw [sub_eq_add_neg,padicValRat.add_eq_of_lt (by simpa only [←sub_eq_add_neg] using sub_ne_zero.mpr ne) tn (neg_ne_zero.mpr z)]
      rw [padicValRat.neg];exact lt
  have guard := diff 3 (Finset.mem_insert_self ..)
  have ns (b : ℚ) (m : b∈marks) := diff b (Finset.mem_insert_of_mem m)
  have num : fiveProduct t≠0 := Finset.prod_ne_zero_iff.mpr (fun b m => sub_ne_zero.mpr (ns b m).1)
  have denom := mul_ne_zero (pow_ne_zero 5 an) (pow_ne_zero 6 (sub_ne_zero.mpr guard.1))
  have card : marks.card=5 := by norm_num [marks,Finset.card_insert_of_notMem]
  have numerator : padicValRat p (fiveProduct t)=5*padicValRat p t := by
    rw [fiveProduct,padicValRat_finset_prod marks (fun b m=>sub_ne_zero.mpr (ns b m).1)]
    have rr : (∑ b∈marks,padicValRat p (t-b))=∑ _∈marks,padicValRat p t :=
      Finset.sum_congr rfl (fun b m=>(ns b m).2)
    rw [rr,Finset.sum_const,card,nsmul_eq_mul];rfl
  refine ⟨fun m=> (ns t m).1 rfl,guard.1,div_ne_zero num denom,guard.2.trans tv,?_⟩
  rw [detector,padicValRat.div num denom,padicValRat.mul (pow_ne_zero 5 an) (pow_ne_zero 6 (sub_ne_zero.mpr guard.1)),
    padicValRat.pow,padicValRat.pow,numerator,guard.2,tv]
  push_cast
  ring

#print axioms marks_order
#print axioms detector_orders
end Sun28.Exceptional
