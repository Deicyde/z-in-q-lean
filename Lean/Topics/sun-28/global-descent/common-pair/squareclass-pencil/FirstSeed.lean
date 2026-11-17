import PeriodAbscissaProjection
import WordCharacters

namespace Sun28.Abscissa
open Sun28.NormPartners Sun28.PairedClasses Sun28.SeededPartners Sun28.GlobalSections Sun28.MarkedOdd
open Sun28.FixedLocalRows ZInQ.RouteK
noncomputable section

private abbrev twist : ℕ := 55431283575645791

private theorem squarefree_twist : Squarefree twist := by
  change Squarefree (11*(59*(109*(439*(3389*526681)))) : ℕ)
  simp only [Nat.squarefree_mul_iff]
  repeat' first | constructor | exact (by norm_num : Nat.Prime _).squarefree

private theorem three_factors {m : ℕ} (div : m∣twist) (split : ∀p∈m.primeFactors,p%3=1) :
    m∣109*(439*526681) := by
  rw [← Nat.prod_primeFactors_of_squarefree (squarefree_twist.squarefree_of_dvd div),
    Nat.prod_primeFactors_dvd_iff (by norm_num : 109*(439*526681)≠0)]
  intro p hp
  have pr:=Nat.prime_of_mem_primeFactors hp
  have all:=dvd_trans (Nat.dvd_of_mem_primeFactors hp) div
  change p∣11*(59*(109*(439*(3389*526681)))) at all
  simp only [pr.dvd_mul] at all
  have modp:=split p hp
  apply Nat.mem_primeFactors.mpr
  refine ⟨pr,?_,by norm_num⟩
  rcases all with h|h|h|h|h|h <;>
    have e := (Nat.prime_dvd_prime_iff_eq pr (by norm_num)).mp h <;>
    subst p <;> norm_num at *

private theorem divisor_step {p m n : ℕ} (pr:p.Prime) (h:m∣p*n) :
    m∣n ∨ ∃ a, a∣n ∧ m=p*a := by
  by_cases pm : p∣m
  · obtain ⟨a,rfl⟩:=pm
    exact Or.inr ⟨a,(Nat.mul_dvd_mul_iff_left pr.pos).mp h,rfl⟩
  · exact Or.inl ((pr.coprime_iff_not_dvd.mpr pm).symm.dvd_of_dvd_mul_left h)

private theorem two {p m : ℕ} (pr : p.Prime) (h : m∣p) : m=1 ∨ m=p :=
  pr.eq_one_or_self_of_dvd m h

private theorem incompatible {p m : ℕ} (hp:p.Prime)
    (test : parity (symbol p (primeUnit p m)) ≠ (exponent p m : ZMod 2)*
      parity (symbol p (-((twist:ℤ)/p)))) : ¬unitRow twist m p := by
  have : Fact p.Prime := ⟨hp⟩
  intro row
  apply test
  simpa only [parity_symbol] using row hp

/-- The smallest seed in the archived survey has no nontrivial second label. -/
theorem first_seed_empty : labels twist = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro m mem
  obtain ⟨div,large,_,split,_⟩ := Finset.mem_filter.mp mem
  have h:=three_factors (Nat.mem_divisors.mp div).1 split
  have test (p m : ℕ) (pr:p.Prime) (dvd:p∣twist)
      (r : parity (symbol p (primeUnit p m)) ≠ (exponent p m : ZMod 2)*
        parity (symbol p (-((twist:ℤ)/p)))) : m∉labels twist := by
    intro mem
    have rr := (Finset.mem_filter.mp mem).2.2.2.2 p (Nat.mem_primeFactors.mpr ⟨pr,dvd,by decide⟩)
    exact incompatible pr r rr
  rcases divisor_step (by norm_num : Nat.Prime 109) h with h₁|⟨a,h₁,rfl⟩ <;>
    rcases divisor_step (by norm_num : Nat.Prime 439) h₁ with h₂|⟨c,h₂,rfl⟩ <;>
    rcases two (by norm_num : Nat.Prime 526681) h₂ with rfl|rfl
  · omega
  · exact test 59 _ (by norm_num) (by decide) (by norm_num [parity,symbol,primeUnit,exponent,twist]) mem
  · exact test 11 _ (by norm_num) (by decide) (by norm_num [parity,symbol,primeUnit,exponent,twist]) mem
  · exact test 11 _ (by norm_num) (by decide) (by norm_num [parity,symbol,primeUnit,exponent,twist]) mem
  · exact test 11 _ (by norm_num) (by decide) (by norm_num [parity,symbol,primeUnit,exponent,twist]) mem
  · exact test 11 _ (by norm_num) (by decide) (by norm_num [parity,symbol,primeUnit,exponent,twist]) mem
  · exact test 59 _ (by norm_num) (by decide) (by norm_num [parity,symbol,primeUnit,exponent,twist]) mem
  · exact test 109 _ (by norm_num) (by decide) (by norm_num [parity,symbol,primeUnit,exponent,twist]) mem

theorem first_seed_forces_old_family (ad : AdmissiblePair 526361 526681)
    (C : Candidate 526361 526681 199951) (hit : strictPoint 526361 (526361*199951*526681)) :
    CancelledFactors 526361 526681 := by
  by_contra outside
  obtain ⟨m,mem,_⟩ := (strict_iff_label ad C outside).mp hit
  change m ∈ labels twist at mem
  rw [first_seed_empty] at mem
  exact Finset.notMem_empty _ mem

end
end Sun28.Abscissa
#print axioms Sun28.Abscissa.first_seed_empty
#print axioms Sun28.Abscissa.first_seed_forces_old_family
