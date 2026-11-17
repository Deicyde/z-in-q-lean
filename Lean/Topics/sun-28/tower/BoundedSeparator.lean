import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-! A fixed finite list of integer linear forms separates any finite set of tuples. -/
open Polynomial Finset
namespace ZInQBlueprint.SunTower
noncomputable section
variable {L : Type*} [Field L] {n : ℕ}

/-- Evaluate a tuple as the coefficient vector of a polynomial of degree less than its length. -/
def separator (z : L) (x : Fin n → L) : L := ∑ i, x i * z ^ (i : ℕ)

private theorem eval_coeffs [DecidableEq L] (z : L) (x : Fin n → L) :
    (ofFn n x).eval z = separator z x := by
  simp [ofFn_eq_sum_monomial,eval_finsetSum,separator]

/-- All collisions of a finite tuple set occur in a set of size at most
the degree bound per pair times the number of unordered pairs. -/
theorem collision_bound (S : Finset (Fin n → L)) :
    ∃ bad : Finset L, bad.card ≤ S.card.choose 2 * (n-1) ∧
      ∀ b ∉ bad, Set.InjOn (separator b) (S : Set (Fin n → L)) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅,by simp,by simp⟩
  | @insert x S hx ih =>
    obtain ⟨old,ho,hin⟩ := ih
    let pairs (y : Fin n → L) := (ofFn n (x-y)).roots.toFinset
    have hc (y : Fin n → L) (_ : y ∈ S) : (pairs y).card ≤ n-1 := by
      by_cases hn : n = 0
      · subst n; simp [pairs]
      have deg := ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr hn) (x-y)
      exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (by omega))
    refine ⟨old ∪ S.biUnion pairs, ?_, ?_⟩
    · have hu := Finset.card_union_le old (S.biUnion pairs)
      have hv := Finset.card_biUnion_le_card_mul S pairs (n-1) hc
      rw [card_insert_of_notMem hx, Nat.choose_succ_succ S.card 1, Nat.choose_one_right, add_mul]
      exact hu.trans ((Nat.add_le_add ho hv).trans_eq (Nat.add_comm _ _))
    · intro b hb
      have hold : b ∉ old := fun h => hb (mem_union_left _ h)
      have no (y : Fin n → L) (hy : y ∈ S) : separator b x ≠ separator b y := by
        intro he
        have hxy : x ≠ y := fun h => hx (h ▸ hy)
        have hp : ofFn n (x-y) ≠ 0 := by
          intro eq
          apply hxy
          exact sub_eq_zero.mp ((injective_ofFn n) (eq.trans (ofFn_zero n).symm))
        have ev : (ofFn n (x-y)).eval b = 0 := by
          rw [map_sub,eval_sub,eval_coeffs,eval_coeffs,he,sub_self]
        exact hb (mem_union_right _ (mem_biUnion.mpr ⟨y,hy,
          Multiset.mem_toFinset.mpr ((mem_roots hp).mpr ev)⟩))
      intro a ha c hc he
      rcases (Finset.mem_insert.mp ha : a = x ∨ a ∈ S) with hax | has
      · rcases (Finset.mem_insert.mp hc : c = x ∨ c ∈ S) with hcx | hcs
        · exact hax.trans hcx.symm
        · exact (no c hcs (hax ▸ he)).elim
      · rcases (Finset.mem_insert.mp hc : c = x ∨ c ∈ S) with hcx | hcs
        · exact (no a has (hcx ▸ he.symm)).elim
        · exact hin b hold has hcs he

/-- At most 1+(n−1)·binom(d,2) candidates are needed for d points. The list starts at
zero and is independent of the coordinates and the ambient characteristic-zero field. -/
theorem exists_bounded_separator [CharZero L] (S : Finset (Fin n → L)) :
    ∃ b : ℕ, b ≤ S.card.choose 2 * (n-1) ∧ Set.InjOn (separator (b:L)) (S : Set (Fin n → L)) := by
  classical
  obtain ⟨bad,hb,h⟩ := collision_bound S
  let d := S.card.choose 2 * (n-1)
  let inc : ℕ ↪ L := ⟨Nat.cast, Nat.cast_injective⟩
  have hc : bad.card < ((Finset.range (d+1)).map inc).card := by
    rw [Finset.card_map,Finset.card_range]
    omega
  obtain ⟨v,hv,hv'⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hv
  exact ⟨b,Nat.le_of_lt_succ (Finset.mem_range.mp hb),h _ hv'⟩

end
end ZInQBlueprint.SunTower
#print axioms ZInQBlueprint.SunTower.collision_bound
#print axioms ZInQBlueprint.SunTower.exists_bounded_separator
