import InertDensity
import DiagonalBias

namespace Sun28.CommonRows
open Finset Sun28.MixedSieve Sun28.PrimeLower Sun28.PrimeValues Sun28.ContactFactors
open Sun28.MediumSieve
open scoped Classical
noncomputable section
variable {p:ℕ} [Fact p.Prime] {ι:Type*} [Fintype ι] [DecidableEq ι]

private theorem split_size (split:p%4=1) {r:ZMod p} (unit:r≠0) :
    Fintype.card (Circle p r)=p-1 := by
  have odd : p≠2:=by omega
  have count:=circle_card odd unit
  rw [legendreSym.at_neg_one odd,ZMod.χ₄_nat_eq_if_mod_four] at count
  have parity:p%2≠0:=by omega
  simp [parity,split] at count
  omega

private def singleBad (t:ZMod p) : ℕ := if t=1 then 1 else 2

private theorem two_sign_card (split:p%4=1) (t:ZMod p) :
    (bad p t true ∪ bad p t false).card =
      (if t=(-1:ZMod p) then 2 else 2*singleBad t) := by
  have card:=Finset.card_union_add_card_inter (bad p t true) (bad p t false)
  simp_rw [split_bad_card split] at card
  by_cases neg:t=(-1:ZMod p)
  · subst t
    have two:(2:ZMod p)≠0:=by
      rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
      exact fun h=>(show p≠2 by omega) ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp h)
    have ne:(-1:ZMod p)≠1:=fun h=>two (by linear_combination -h)
    rw [split_diagonal split,ite_eq_right ne] at card
    simp only [ite_true];omega
  · have both:bad p t true ∩ bad p t false=∅:=by
      apply eq_empty_iff_forall_notMem.mpr
      intro z h
      exact neg (diagonal_norm (by omega:p≠2) (mem_inter.mp h).1 (mem_inter.mp h).2)
    rw [both,Finset.card_empty] at card
    simp only [ite_eq_right neg,singleBad];omega

/-- A single word in the normalized fibres is allowed if either sign is
absent at every position. This formula charges a diagonal collision once. -/
theorem split_safe_count (split:p%4=1) (t:ι→ZMod p) (units:∀i,t i≠0) :
    (((obstructed t)ᶜ.card:ℤ)) =
    2*∏i,((p-1-(if t i=1 then 1 else 2):ℕ):ℤ)-
      ∏i,((p-1-(if t i=(-1:ZMod p) then 2 else 2*(if t i=1 then 1 else 2)):ℕ):ℤ) := by
  classical
  let P:=Fintype.piFinset (fun i => (bad p (t i) true)ᶜ)
  let M:=Fintype.piFinset (fun i => (bad p (t i) false)ᶜ)
  have cover:(obstructed t)ᶜ=P∪M:=by
    ext z;rw [mem_compl,obstructed_iff,mem_union]
    simp only [P,M,Fintype.mem_piFinset,mem_compl]
    constructor
    · intro no;by_cases plus:∃i,z i∈bad p (t i) true
      · obtain ⟨i,hit⟩:=plus;exact Or.inr (fun j other=>no ⟨i,j,hit,other⟩)
      · exact Or.inl (fun i hit=>plus ⟨i,hit⟩)
    · rintro (nop|nom) ⟨i,j,pi,pj⟩
      · exact nop i pi
      · exact nom j pj
  have joint:P∩M=Fintype.piFinset (fun i=>(bad p (t i) true ∪ bad p (t i) false)ᶜ):=by
    ext z
    simp only [P,M,mem_inter,Fintype.mem_piFinset,mem_compl,mem_union,not_or]
    exact forall_and.symm
  have count:=card_union_add_card_inter P M
  rw [joint] at count
  simp only [P,M,Fintype.card_piFinset,card_compl,split_bad_card split,two_sign_card split,
    split_size split (units _),singleBad] at count
  have fin:=congrArg (fun a:ℕ=>(a:ℤ)) count
  push_cast at fin
  rw [cover]
  linarith only [fin]

/-- Normalized finite-model rate for the actual manuscript positions. -/
theorem fixed_inert_rate {A:Fin 3→ℚ} {d:ℕ} (pos:0<d) (large:exceptionalBound A d<p)
    (inert:p%4=3) (room:26≤p) :
    relativeLoss (coefficients A p) ≤ 312/(((p:ℝ)+1)^2*(p:ℝ)^2) := by
  let c:=coefficients A p
  have inj:Function.Injective c:=by
    intro i j eq
    by_contra diff
    apply Sun28.ConeFibres.reduced_gap_ne_zero pos large diff
    simpa [c,Sun28.SieveTail.gap,coefficients,Int.cast_sub] using sub_eq_zero.mpr eq
  have k:Fintype.card ↥(shifts A)≤13:=by simpa using Sun28.GaussianSelection.shifts_card_le A
  have kr:(Fintype.card ↥(shifts A):ℝ)≤13:=by exact_mod_cast k
  have kp:0≤(Fintype.card ↥(shifts A):ℝ):=by positivity
  have product:(Fintype.card ↥(shifts A):ℝ)*(Fintype.card ↥(shifts A)-1)≤156:=by
    nlinarith only [mul_nonneg kp (sub_nonneg.mpr kr),kr]
  have half:1/2≤unitRate c:=(inert_relative_loss_le c (by omega)).1
  have halfPos:0<unitRate c:=by linarith
  have pp:0<(p:ℝ):=by exact_mod_cast (Fact.out:p.Prime).pos
  have den:0<(((p:ℝ)+1)^2*(p:ℝ)^2):=by positivity
  apply (div_le_iff₀ halfPos).mpr
  calc
    _ ≤ _:=inert_average_bound c inert inj
    _ ≤ 156/(((p:ℝ)+1)^2*(p:ℝ)^2):=div_le_div_of_nonneg_right product den.le
    _ = 312/(((p:ℝ)+1)^2*(p:ℝ)^2)*(1/2):=by ring
    _ ≤ _:=mul_le_mul_of_nonneg_left half (by positivity)

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.split_safe_count
#print axioms Sun28.CommonRows.fixed_inert_rate
