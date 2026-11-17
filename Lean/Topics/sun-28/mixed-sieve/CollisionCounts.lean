import NormCircles
import Mathlib.Algebra.BigOperators.Field

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

namespace Sun28.MixedSieve
open Finset
variable {p : ℕ} [Fact p.Prime]

/-- Residues on the specified norm fibre at which one of the adjacent norms vanishes. -/
def bad (p : ℕ) [Fact p.Prime] (t : F p) (e : Bool) : Finset (Circle p t) :=
  univ.filter fun z => (z.val.1+(if e then 1 else -1))^2+z.val.2^2=0

theorem bad_card (odd : p≠2) (t : F p) (e : Bool) : (bad p t e).card≤2 := by
  have h : (bad p t e).card≤(Sun28.NormSieve.badFibre p t e).card := by
    apply Finset.card_le_card_of_injOn (fun z => z.val)
    · intro z hz
      exact Finset.mem_filter.mpr ⟨mem_univ _,z.property,(mem_filter.mp hz).2⟩
    · exact fun _ _ _ _ h => Subtype.ext h
  exact h.trans (Sun28.NormSieve.two_residues odd t e)

/-- A collision at a single shift must lie over the one norm value -1. -/
theorem diagonal_norm (odd : p≠2) {t : F p} {z : Circle p t}
    (a : z∈bad p t true) (b : z∈bad p t false) : t= -1 := by
  have ha : (z.val.1+1)^2+z.val.2^2=0 := (mem_filter.mp a).2
  have hb : (z.val.1-1)^2+z.val.2^2=0 := by simpa [sub_eq_add_neg] using (mem_filter.mp b).2
  have two : (2:F p)≠0 := by
    rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
    exact fun d => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp d)
  have x : z.val.1=0 := (mul_eq_zero.mp (show ((2:F p)*2)*z.val.1=0 by linear_combination ha-hb)).resolve_left (mul_ne_zero two two)
  have n:=z.property
  rw [x] at n ha
  linear_combination ha-n

private theorem bad_rate {t : F p} (ht : t≠0) (hp : 2<p) (e : Bool) :
    ((bad p t e).card:ℝ)/(Fintype.card (Circle p t):ℝ) ≤ 2/((p:ℝ)-1) := by
  have low:=circle_card_lower (by omega : p≠2) ht
  have N : 0<(Fintype.card (Circle p t):ℝ) := by exact_mod_cast (show 0<Fintype.card (Circle p t) by omega)
  have h : (p:ℝ)-1≤(Fintype.card (Circle p t):ℝ) := by
    have e : p≤Fintype.card (Circle p t)+1 := by omega
    apply sub_le_iff_le_add.mpr
    exact_mod_cast e
  have cap : ((bad p t e).card:ℝ)≤2 := by exact_mod_cast bad_card (by omega : p≠2) t e
  have pos : 0<(p:ℝ)-1 := by
    have q : (2:ℝ)<p := by exact_mod_cast hp
    linarith
  apply (div_le_div_iff₀ N pos).mpr
  calc
    (((bad p t e).card:ℝ))*((p:ℝ)-1) ≤ 2*((p:ℝ)-1) := mul_le_mul_of_nonneg_right cap pos.le
    _ ≤ 2*Fintype.card (Circle p t) := by linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Independent choices at the k marked positions with the indicated restrictions. -/
noncomputable def boxMass (t : ι→F p) (s : (i : ι)→Finset (Circle p (t i))) : ℝ :=
  ((Fintype.piFinset s).card:ℝ)/Fintype.card ((i : ι)→Circle p (t i))

theorem box_product (t : ι→F p) (s : (i : ι)→Finset (Circle p (t i))) :
    boxMass t s=∏ i, ((s i).card:ℝ)/Fintype.card (Circle p (t i)) := by
  classical
  dsimp [boxMass]
  rw [Fintype.card_piFinset,Fintype.card_pi,Finset.prod_div_distrib]
  push_cast
  rfl

noncomputable def pairSets (t : ι→F p) (i j : ι) (k : ι) : Finset (Circle p (t k)) :=
  if k=i then (if k=j then bad p (t k) true ∩ bad p (t k) false else bad p (t k) true)
  else if k=j then bad p (t k) false else univ

theorem pairSets_mem (t : ι→F p) (i j : ι) (z : (k : ι)→Circle p (t k)) :
    z∈Fintype.piFinset (pairSets t i j) ↔ z i∈bad p (t i) true ∧ z j∈bad p (t j) false := by
  rw [Fintype.mem_piFinset]
  constructor
  · intro h
    by_cases eq : i=j
    · subst j; simpa [pairSets] using h i
    · exact ⟨by simpa [pairSets,eq] using h i,by simpa [pairSets,Ne.symm eq] using h j⟩
  · rintro ⟨a,b⟩ k
    by_cases eq : k=i
    · subst k
      by_cases e : i=j
      · subst j; simpa [pairSets] using And.intro a b
      · simpa [pairSets,e] using a
    · by_cases e : k=j
      · subst k; simpa [pairSets,eq] using b
      · simp [pairSets,eq,e]

noncomputable def pairMass (t : ι→F p) (i j : ι) : ℝ := boxMass t (pairSets t i j)

theorem offdiag (hp : 2<p) (t : ι→F p) (nz : ∀ i,t i≠0) {i j : ι} (ne : i≠j) :
    pairMass t i j ≤ (2/((p:ℝ)-1))^2 := by
  classical
  have pos (k : ι) : (Fintype.card (Circle p (t k)):ℝ)≠0 := by
    have := circle_card_lower (by omega : p≠2) (nz k)
    exact_mod_cast (show Fintype.card (Circle p (t k))≠0 by omega)
  rw [pairMass,box_product]
  have eq (k : ι) : (((pairSets t i j k).card:ℝ)/Fintype.card (Circle p (t k)))=
      (if k=i then ((bad p (t i) true).card:ℝ)/Fintype.card (Circle p (t i)) else 1)*
      (if k=j then ((bad p (t j) false).card:ℝ)/Fintype.card (Circle p (t j)) else 1) := by
    by_cases h : k=i
    · subst k; simp [pairSets,ne]
    by_cases v : k=j
    · subst k; simp [pairSets,h]
    simp [pairSets,h,v,pos]
  simp_rw [eq]
  rw [Finset.prod_mul_distrib]
  simp only [Fintype.prod_ite_eq']
  rw [pow_two]
  exact mul_le_mul (bad_rate (nz i) hp true) (bad_rate (nz j) hp false) (by positivity)
    (by
      have h : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
      exact div_nonneg (by norm_num) (by linarith))

theorem diagonal (hp : 2<p) (t : ι→F p) (nz : ∀ i,t i≠0) (i : ι) :
    pairMass t i i ≤ if t i= -1 then 2/((p:ℝ)-1) else 0 := by
  classical
  have pos (k : ι) : (Fintype.card (Circle p (t k)):ℝ)≠0 := by
    have := circle_card_lower (by omega : p≠2) (nz k)
    exact_mod_cast (show Fintype.card (Circle p (t k))≠0 by omega)
  let s:=bad p (t i) true ∩ bad p (t i) false
  have eq (k : ι) : ((pairSets t i i k).card:ℝ)/Fintype.card (Circle p (t k))=
      (if k=i then (s.card:ℝ)/Fintype.card (Circle p (t i)) else 1) := by
    by_cases h : k=i
    · subst k; simp [pairSets,s]
    simp [pairSets,h,pos]
  rw [pairMass,box_product]
  simp_rw [eq]
  rw [Fintype.prod_ite_eq']
  by_cases n : t i= -1
  · have bnd : (s.card:ℝ)/Fintype.card (Circle p (t i)) ≤ 2/((p:ℝ)-1) := by
      have le : (s.card:ℝ) ≤ ((bad p (t i) true).card:ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.inter_subset_left (s₂:=bad p (t i) false) (s₁:=bad p (t i) true))
      exact (div_le_div_of_nonneg_right le (by positivity)).trans (bad_rate (nz i) hp true)
    simpa only [n,reduceIte] using bnd
  · simp only [n,reduceIte]
    have empty : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr fun z hz =>
      n (diagonal_norm (by omega : p≠2) (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hz).2)
    simp [empty]

end Sun28.MixedSieve
#print axioms Sun28.MixedSieve.bad_card
#print axioms Sun28.MixedSieve.diagonal_norm
#print axioms Sun28.MixedSieve.box_product
#print axioms Sun28.MixedSieve.pairSets_mem
#print axioms Sun28.MixedSieve.offdiag
#print axioms Sun28.MixedSieve.diagonal
