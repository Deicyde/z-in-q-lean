import AuxiliaryPrime
import Mathlib.Tactic.NormNum.LegendreSymbol

namespace Sun28.AuxiliaryPrimes
noncomputable section

def value (bit : Bool) : ℤ := if bit then -1 else 1

/-- Simultaneous prime types and the two directed symbols. For type seven,
the reverse symbol changes sign precisely at support primes three modulo four. -/
theorem fresh_prime (S : Finset ℕ) (hs : ∀ p ∈ S, p.Prime ∧ 3<p)
    (bits : ℕ → Bool) (special : Bool) (bound : ℕ) :
    ∃ q > bound, q.Prime ∧ 3 < q ∧ q ∉ S ∧ q % 12 = (if special then 7 else 1) ∧
      jacobiSym (-1) q = value special ∧ jacobiSym 3 q = value special ∧
      ∀ p ∈ S, jacobiSym q p = value (bits p) ∧
        jacobiSym p q = (if special && decide (p % 4 = 3) then -value (bits p) else value (bits p)) := by
  let r : ℕ := if special then 7 else 1
  have hr : r.Coprime 12 := by cases special <;> decide
  obtain ⟨q,big,pr,qr,forward⟩ := prime_with_symbols S hs bits hr (max bound (max 3 (S.sup id)))
  have q3 : 3 < q := lt_of_le_of_lt ((le_max_left ..).trans (le_max_right ..)) big
  have q2 : q≠2 := by omega
  have odd := pr.odd_of_ne_two q2
  have eq : q%12=r := by simpa only [Nat.ModEq, Nat.mod_eq_of_lt (show r<12 by cases special <;> decide)] using qr
  have q4 : q%4=if special then 3 else 1 := by cases special <;> dsimp [r] at eq ⊢ <;> omega
  have sign : jacobiSym (-1) q = value special := by
    rw [jacobiSym.mod_right (-1) odd]
    change jacobiSym (-1) (q%4)=_
    rw [q4]
    cases special <;> norm_num [value]
  have three : jacobiSym 3 q = value special := by
    rw [jacobiSym.mod_right (3:ℤ) odd]
    change jacobiSym 3 (q%12)=_
    rw [eq]
    cases special <;> norm_num [value,r]
  refine ⟨q,lt_of_le_of_lt (le_max_left ..) big,pr,q3,?_,eq,sign,three,?_⟩
  · intro mem
    have small : q≤S.sup id := Finset.le_sup (f:=id) mem
    exact (not_lt_of_ge (small.trans ((le_max_right ..).trans (le_max_right ..)))) big
  · intro p hp
    have pp := hs p hp
    have po := pp.1.odd_of_ne_two (by omega)
    have rev := jacobiSym.quadratic_reciprocity_if (a:=p) (b:=q) (Nat.odd_iff.mp po) (Nat.odd_iff.mp odd)
    rw [forward p hp,q4] at rev
    refine ⟨forward p hp,?_⟩
    cases special <;> by_cases H : p%4=3 <;> simpa [H,value] using rev.symm

/-- A construction depending on the previously selected primes. The prime at
stage i realizes the whole row requested on the initial and all earlier primes.
The list of stages may encode the star columns followed by the free row. -/
theorem extend_support (S : Finset ℕ) (hs : ∀ p ∈ S, p.Prime ∧ 3<p)
    (k : ℕ) (kind : ℕ → Bool) (row : ℕ → List ℕ → ℕ → Bool) (bound : ℕ) :
    ∃ primes : List ℕ, primes.length=k ∧ primes.Nodup ∧
      (∀ q ∈ primes, bound < q ∧ q.Prime ∧ 3 < q ∧ q ∉ S) ∧
      ∀ i (hi : i < primes.length),
        let q := primes[i]
        let prev := primes.take i
        q % 12 = (if kind i then 7 else 1) ∧
        jacobiSym (-1) q = value (kind i) ∧ jacobiSym 3 q = value (kind i) ∧
        ∀ p ∈ S ∪ prev.toFinset, jacobiSym q p = value (row i prev p) ∧
          jacobiSym p q = (if kind i && decide (p%4=3) then -value (row i prev p) else value (row i prev p)) := by
  classical
  induction k with
  | zero => exact ⟨[],rfl,by simp,by simp,by simp⟩
  | succ k ih =>
    obtain ⟨l,len,nd,each,earlier⟩ := ih
    let T := S ∪ l.toFinset
    have good (p : ℕ) (hp : p∈T) : p.Prime ∧ 3<p := by
      rcases Finset.mem_union.mp hp with h|h
      · exact hs p h
      · obtain ⟨_,pr,lo,_⟩ := each p (List.mem_toFinset.mp h)
        exact ⟨pr,lo⟩
    obtain ⟨q,large,pr,lo,fresh,ty,sg,th,sy⟩ := fresh_prime T good (row k l) (kind k) bound
    have newS : q∉S := fun h => fresh (Finset.mem_union_left _ h)
    have newL : q∉l := fun h => fresh (Finset.mem_union_right _ (List.mem_toFinset.mpr h))
    refine ⟨l++[q],by simp [len],?_,?_,?_⟩
    · simp only [List.nodup_append,nd,List.nodup_singleton,true_and,List.mem_singleton]
      rintro x hx y rfl rfl
      exact newL hx
    · intro v hv
      rcases List.mem_append.mp hv with h|h
      · exact each v h
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨large,pr,lo,newS⟩
    · intro i hi
      by_cases old : i<l.length
      · simpa only [List.getElem_append_left old, List.take_append_of_le_length old.le] using earlier i old
      · have last : i=l.length := by simp only [List.length_append,List.length_singleton] at hi; omega
        subst i
        simpa [len,T] using (show q%12=(if kind k then 7 else 1) ∧
          jacobiSym (-1) q=value (kind k) ∧ jacobiSym 3 q=value (kind k) ∧
          ∀ p∈T,jacobiSym q p=value (row k l p) ∧
            jacobiSym p q=(if kind k && decide (p%4=3) then -value (row k l p) else value (row k l p)) from ⟨ty,sg,th,sy⟩)

end
end Sun28.AuxiliaryPrimes
#print axioms Sun28.AuxiliaryPrimes.fresh_prime
#print axioms Sun28.AuxiliaryPrimes.extend_support
