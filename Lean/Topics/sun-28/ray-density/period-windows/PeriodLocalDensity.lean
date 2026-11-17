import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

namespace Sun28.PeriodWindows
open Finset

/-- An odd split prime has exactly two bad pairs (x,y), with x=0 and y²=−1.
Each is a unit of the split Gaussian algebra since its norm is −1. -/
theorem self_residue_count {p : ℕ} [Fact p.Prime] (odd : p≠2) :
    ((Finset.univ : Finset (ZMod p × ZMod p)).filter (fun z=>z.1=0 ∧ z.2^2= -1)).card =
      if p%4=1 then 2 else 0 := by
  classical
  let B:=(Finset.univ : Finset (ZMod p × ZMod p)).filter (fun z=>z.1=0 ∧ z.2^2= -1)
  change B.card=_
  have pp:=(Fact.out : p.Prime)
  have parity:=pp.eq_two_or_odd.resolve_left odd
  by_cases split:p%4=1
  · rw [ite_eq_left split]
    obtain ⟨a,ra⟩:=ZMod.exists_sq_eq_neg_one_iff.mpr (show p%4≠3 by omega)
    have sq:a^2= -1:=by simpa [pow_two] using ra.symm
    have nn:a≠0:=by intro h; simp [h] at sq
    have t:(2:ZMod p)≠0:=by
      rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
      exact fun h=>odd ((Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).mp h)
    have dn:a≠ -a:=by
      intro e
      exact (mul_ne_zero t nn) (by linear_combination e)
    have form : B = {(0,a),(0,-a)} := by
      ext ⟨x,y⟩
      simp only [B,mem_filter,mem_univ,true_and,mem_insert,mem_singleton,Prod.mk.injEq]
      rw [←sq,sq_eq_sq_iff_eq_or_eq_neg]
      tauto
    rw [form]
    simp [dn]
  · rw [ite_eq_right split,card_eq_zero]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z mem
    have hz: z.2^2= -1:=(Finset.mem_filter.mp mem).2.2
    have h:=ZMod.mod_four_ne_three_of_sq_eq_neg_one hz
    omega

private theorem partial_sq (n : ℕ) :
    ∑ j∈Finset.range n, (1:ℝ)/((j:ℝ)+2)^2 ≤ 1-1/(n+1:ℝ) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    push_cast
    have np : (0:ℝ)<n+1:=by positivity
    have le : (1:ℝ)/((n:ℝ)+2)^2 ≤ 1/((n:ℝ)+1)-1/((n:ℝ)+2) := by
      field_simp
      nlinarith only [np]
    rw [show (n:ℝ)+1+1=n+2 by ring]
    linarith

/-- Codes j enumerate every possible split odd prime q=4(j+1)+1. Bounding
all codes at once permits deleting two residue classes per prime. -/
theorem split_loss_quarter (n : ℕ) :
    ∑ j∈Finset.range n,(2:ℝ)/(4*((j:ℝ)+1))^2 ≤ 1/4 := by
  have partialSum : ∑ j∈Finset.range n,(1:ℝ)/((j:ℝ)+1)^2 ≤ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
      rw [Finset.sum_range_succ']
      have h:=partial_sq n
      simp only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] at *
      have divn:(0:ℝ)≤1/(n+1:ℝ):=by positivity
      norm_num
      simp only [one_div] at h divn
      linarith
  have eq (j:ℕ) : (2:ℝ)/(4*((j:ℝ)+1))^2 = (1/8:ℝ)*(1/((j:ℝ)+1)^2) := by
    field_simp
    ring
  simp_rw [eq,←Finset.mul_sum]
  linarith

end Sun28.PeriodWindows
#print axioms Sun28.PeriodWindows.self_residue_count
#print axioms Sun28.PeriodWindows.split_loss_quarter
