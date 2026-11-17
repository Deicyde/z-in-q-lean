import MarkedFactors

namespace Sun28.MixedSieve
open Finset

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two position-wise events for one sign. -/
noncomputable def safeBox (t : ι→F p) (e : Bool) : Finset ((i : ι)→Circle p (t i)) :=
  Fintype.piFinset (fun i => (bad p (t i) e)ᶜ)

theorem good_iff_union (t : ι→F p) (z : (i : ι)→Circle p (t i)) :
    z∉obstructed t ↔ z∈safeBox t true ∪ safeBox t false := by
  classical
  simp only [obstructed_iff,Finset.mem_union,safeBox,Fintype.mem_piFinset,Finset.mem_compl]
  constructor
  · intro clear
    by_cases plus : ∀ i,z i∉bad p (t i) true
    · exact Or.inl plus
    · obtain ⟨i,hi⟩:=not_forall.mp plus
      have hi:=Classical.not_not.mp hi
      exact Or.inr fun j hj => clear ⟨i,j,hi,hj⟩
  · rintro (a|b) ⟨i,j,hi,hj⟩
    · exact a i hi
    · exact b j hj

/-- One negative rectangle subtracts the overlap of the two good rectangles. -/
def signedBox (safe : Bool→ι→Prop) [∀ e i,Decidable (safe e i)] (j : Fin 3) (i : ι) : ℤ :=
  if j=0 then (if safe true i then 1 else 0)
  else if j=1 then (if safe false i then 1 else 0)
  else (if safe true i ∧ safe false i then 1 else 0)

def sign (j : Fin 3) : ℤ := if j=2 then -1 else 1

omit [DecidableEq ι] in
private theorem indicator_product (P : ι→Prop) [DecidablePred P] :
    (∏ i,(if P i then 1 else 0 : ℤ))=if ∀i,P i then 1 else 0 := by
  classical
  by_cases all : ∀i,P i
  · simp [all]
  · obtain ⟨i,hi⟩ := not_forall.mp all
    have zero := Finset.prod_eq_zero (s:=univ) (f:=fun j => if P j then (1:ℤ) else 0) (mem_univ i) (by simp [hi])
    simp [zero,all]

omit [DecidableEq ι] in
/-- The three rectangles at a single prime. -/
theorem one_prime_expansion (safe : Bool→ι→Prop) [∀ e i,Decidable (safe e i)] :
    (if (∀i,safe true i) ∨ (∀i,safe false i) then (1:ℤ) else 0)=
       ∑ j : Fin 3,sign j * ∏ i,signedBox safe j i := by
  classical
  rw [Fin.sum_univ_three]
  simp only [signedBox,sign]
  norm_num only [Fin.isValue,Fin.reduceEq,reduceIte,one_mul,neg_one_mul]
  simp_rw [indicator_product]
  have all : (∀ i,safe true i ∧ safe false i) ↔ (∀ i,safe true i) ∧ (∀ i,safe false i) :=
    forall_and
  by_cases plus : ∀ i,safe true i <;> by_cases minus : ∀ i,safe false i <;> simp [all,plus,minus]

omit [DecidableEq ι] in
/-- At any fixed finite cutoff the joint condition is a finite signed sum of
products over the prime positions. Each position receives its own ray-class test. -/
theorem finite_expansion {P : Type*} [Fintype P] [DecidableEq P] (safe : P→Bool→ι→Prop)
    [∀ l e i,Decidable (safe l e i)] :
    (∏ l, if (∀i,safe l true i) ∨ (∀i,safe l false i) then (1:ℤ) else 0)=
    ∑ j : P→Fin 3,(∏ l,sign (j l)) * ∏ i, ∏ l,signedBox (safe l) (j l) i := by
  classical
  simp_rw [one_prime_expansion]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.prod_mul_distrib,Finset.prod_comm (f:=fun l i => signedBox (safe l) (j l) i)]

open scoped Classical in
/-- Subtract the one-prime bad masses in one and the same weighted sample. -/
theorem surviving_mass {P B : Type*} (places : Finset P) (box : Finset B)
    (bad : P→B→Prop) (w : B→ℝ) (non : ∀ b∈box,0≤w b) :
    (∑ b∈box,w b) - (∑ p∈places,∑ b∈box,if bad p b then w b else 0) ≤
      ∑ b∈box,if ∀ p∈places,¬bad p b then w b else 0 := by
  classical
  rw [Finset.sum_comm (s:=places) (t:=box),←Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro b hb
  by_cases good : ∀ p∈places,¬bad p b
  · rw [ite_eq_left good,Finset.sum_eq_zero (fun p hp => ite_eq_right (good p hp)),sub_zero]
  · obtain ⟨p,hp,fail⟩ : ∃ p∈places,bad p b := by simpa using good
    have bound := Finset.single_le_sum (f:=fun p => if bad p b then w b else 0)
      (fun p _ => by split <;> first | exact non b hb | exact le_rfl) hp
    rw [ite_eq_right good]
    rw [ite_eq_left fail] at bound
    exact sub_nonpos.mpr bound

end Sun28.MixedSieve
#print axioms Sun28.MixedSieve.good_iff_union
#print axioms Sun28.MixedSieve.one_prime_expansion
#print axioms Sun28.MixedSieve.finite_expansion
#print axioms Sun28.MixedSieve.surviving_mass
