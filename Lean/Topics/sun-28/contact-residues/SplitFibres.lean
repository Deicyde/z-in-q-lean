import NormCollision

namespace Sun28.NormSieve
open Finset ManuscriptV15.Arithmetic
variable {p : ℕ} [Fact p.Prime]

private theorem two_unit (odd : p≠2) : (2:ZMod p)≠0 := by
  rw [←Nat.cast_ofNat,Ne,ZMod.natCast_eq_zero_iff]
  exact fun d => odd ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp d)

def signedCoordinate (t : ZMod p) (plus : Bool) : ZMod p :=
  if plus then -(t+1)/2 else (t+1)/2

/-- In either sign branch the bad real coordinate on a given norm fibre is fixed. -/
theorem fixed_real (odd : p≠2) (x y t : ZMod p) (fibre : x^2+y^2=t)
    (plus : Bool) (bad : (x+(if plus then 1 else -1))^2+y^2=0) :
    x=signedCoordinate t plus := by
  cases plus
  · change x=(t+1)/2
    apply (eq_div_iff (two_unit odd)).mpr
    simp only [Bool.false_eq_true,ite_false] at bad
    linear_combination fibre-bad
  · change x=-(t+1)/2
    apply (eq_div_iff (two_unit odd)).mpr
    simp only [ite_true] at bad
    linear_combination bad-fibre

def badFibre (p : ℕ) [NeZero p] (t : ZMod p) (plus : Bool) : Finset (ZMod p × ZMod p) :=
  Finset.univ.filter fun u => u.1^2+u.2^2=t ∧ (u.1+(if plus then 1 else -1))^2+u.2^2=0

/-- A given norm and sign have at most two bad Gaussian residues. -/
theorem two_residues (odd : p≠2) (t : ZMod p) (plus : Bool) :
    (badFibre p t plus).card≤2 := by
  classical
  let S:=badFibre p t plus
  by_cases non : S.Nonempty
  · obtain ⟨⟨a,b⟩,hm⟩ := non
    have vals {x y : ZMod p} (inc : (x,y)∈S) :
        x^2+y^2=t ∧ (x+(if plus then 1 else -1))^2+y^2=0 := (Finset.mem_filter.mp inc).2
    have xval := fixed_real odd a b t (vals hm).1 plus (vals hm).2
    have inc : S ⊆ {(a,b),(a,-b)} := by
      rintro ⟨x,y⟩ h
      have xeq := (fixed_real odd x y t (vals h).1 plus (vals h).2).trans xval.symm
      subst x
      have equal : y^2=b^2 := by linear_combination (vals h).1-(vals hm).1
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp equal with rfl|rfl <;> simp
    have cards:=Finset.card_le_card inc
    exact cards.trans (Finset.card_insert_le _ _ |>.trans (by simp))
  · change S.card≤2
    simp [Finset.not_nonempty_iff_eq_empty.mp non]

theorem four_residues (odd : p≠2) (t : ZMod p) :
    ((badFibre p t true) ∪ (badFibre p t false)).card≤4 :=
  (Finset.card_union_le _ _).trans (by have := two_residues odd t true; have := two_residues odd t false; omega)

/-- Finite-field formula on the actual Gaussian tuple, with no condition on distinctness. -/
theorem adjacent_iff (odd : p≠2) (z : Gaussian) (plus : Bool) :
    p∣adjacentNorm z plus ↔ realResidue p z = signedCoordinate (gaussianNorm z) plus := by
  let x:=realResidue p z
  let y:=imagResidue p z
  have n : x^2+y^2=(gaussianNorm z:ZMod p) := (gaussian_residue z).symm
  have e : (adjacentNorm z plus : ZMod p)=(x+(if plus then 1 else -1))^2+y^2 := by
    cases plus <;> simp [x,y,adjacentNorm,realResidue,imagResidue,gaussian_residue]
  rw [←ZMod.natCast_eq_zero_iff,e]
  refine ⟨fixed_real odd x y _ n plus,?_⟩
  intro h
  change x=signedCoordinate (gaussianNorm z) plus at h
  cases plus
  · change x=((gaussianNorm z:ZMod p)+1)/2 at h
    have d := (eq_div_iff (two_unit odd)).mp h
    change (x+ -1)^2+y^2=0
    linear_combination n-d
  · change x=-((gaussianNorm z:ZMod p)+1)/2 at h
    have d := (eq_div_iff (two_unit odd)).mp h
    change (x+1)^2+y^2=0
    linear_combination n+d

end Sun28.NormSieve
#print axioms Sun28.NormSieve.fixed_real
#print axioms Sun28.NormSieve.two_residues
#print axioms Sun28.NormSieve.four_residues
#print axioms Sun28.NormSieve.adjacent_iff
