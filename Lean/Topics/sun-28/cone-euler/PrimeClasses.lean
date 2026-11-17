import FactorialCost
import Mathlib.Analysis.PSeries

namespace Sun28.ConeEuler
open Finset Filter Topology
noncomputable section

def primesUpTo (n : ℕ) : Finset ℕ := (range (n+1)).filter Nat.Prime

def auxPrimes (B n p : ℕ) : Finset ℕ := ((primesUpTo n).filter (B<·)).erase p

@[simp] theorem mem_primesUpTo {q n : ℕ} : q∈primesUpTo n ↔ q.Prime ∧ q≤n := by
  simp [primesUpTo, and_comm]

@[simp] theorem mem_auxPrimes {q B n p : ℕ} : q∈auxPrimes B n p ↔
    q.Prime ∧ B<q ∧ q≤n ∧ q≠p := by
  simp [auxPrimes, and_comm, and_left_comm, and_assoc]

def classWeight (a q : ℕ) : ℝ := if q%4=a then 1/(q:ℝ) else 0

def classSum (a : ℕ) (P : Finset ℕ) : ℝ := ∑ q∈P, classWeight a q

/-- Languasco--Zaccagnini, Experiment. Math. 19 (2010), equation (1), for modulus four. -/
def PublishedMertensFour : Prop :=
  ∀ a : ℕ, a=1 ∨ a=3 → ∃ m : ℝ, Tendsto
    (fun n : ℕ => classSum a (primesUpTo n) - Real.log (Real.log n)/2) atTop (𝓝 m)

/-- The cost of discarding the initial primes and one further index is uniform in that index. -/
theorem trimmed_class_sum (a B n p : ℕ) :
    classSum a (primesUpTo n) ≤ classSum a (auxPrimes B n p) + B + 2 := by
  let S:=primesUpTo n
  let P:=auxPrimes B n p
  have sub : P⊆S := by
    intro q h
    obtain ⟨prime,_,bound,_⟩:=mem_auxPrimes.mp h
    exact mem_primesUpTo.mpr ⟨prime,bound⟩
  have lost : S\P ⊆ insert p (range (B+1)) := by
    intro q h
    obtain ⟨hq,miss⟩:=mem_sdiff.mp h
    obtain ⟨prime,bound⟩:=mem_primesUpTo.mp hq
    by_cases e:q=p
    · simp [e]
    · have hq' : q≤B := by
        by_contra! too
        exact miss (mem_auxPrimes.mpr ⟨prime,too,bound,e⟩)
      exact mem_insert_of_mem (mem_range.mpr (by omega))
  have card : (S\P).card≤B+2 := (card_le_card lost).trans (by
    simpa using card_insert_le p (range (B+1)))
  have small : (∑ q∈ S\P,classWeight a q)≤(S\P).card := by
    calc _ ≤ ∑ _q∈ S\P,(1:ℝ) := by
              apply sum_le_sum;intro q h
              have hq : (1:ℝ)≤q := by exact_mod_cast (mem_primesUpTo.mp (mem_sdiff.mp h).1).1.one_lt.le
              unfold classWeight;split_ifs
              · exact (div_le_one (by linarith)).mpr hq
              · norm_num
         _ = _ := by simp
  have eq:=sum_sdiff (f:=classWeight a) sub
  change (∑ q∈S,classWeight a q)≤(∑ q∈P,classWeight a q)+_+_
  have c : ((S\P).card:ℝ)≤(B:ℝ)+2 := by exact_mod_cast card
  linarith only [eq,small,c]

theorem mertens_trimmed (mertens : PublishedMertensFour) (B a : ℕ) (ha : a=1 ∨ a=3) :
    ∃ D : ℝ, ∀ᶠ n : ℕ in atTop, ∀ p : ℕ,
      Real.log (Real.log n)/2 - D ≤ classSum a (auxPrimes B n p) := by
  obtain ⟨m,lim⟩:=mertens a ha
  refine ⟨(B:ℝ)+3-m,?_⟩
  have gap : m-1 < m := by linarith
  filter_upwards [lim.eventually_const_lt gap] with n hn
  intro p
  change m-1<classSum a (primesUpTo n)-Real.log (Real.log n)/2 at hn
  linarith only [trimmed_class_sum a B n p,hn]

end
end Sun28.ConeEuler
#print axioms Sun28.ConeEuler.trimmed_class_sum
#print axioms Sun28.ConeEuler.mertens_trimmed
