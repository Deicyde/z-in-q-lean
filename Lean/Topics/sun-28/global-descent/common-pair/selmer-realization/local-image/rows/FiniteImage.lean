import FixedPointCriterion
import Mathlib.Data.Set.Card

namespace Sun28.MarkedDescent
open Sun28.SelmerRealization
noncomputable section

/-- In a finitely generated group an infinite-order point already gives
eight distinct marked labels. Thus an upper bound is sufficient. -/
theorem local_count_of_upper [AddGroup.FG (RationalPoint n)]
    (point : ∃ P : RationalPoint n, ¬ IsOfFinAddOrder P)
    (upper : ∃ c : Finset (ℤ × ℤ), c.card ≤ 8 ∧ localClasses n ⊆ (c : Set (ℤ × ℤ))) :
    (localClasses n).ncard = 8 := by
  classical
  obtain ⟨c, size, sub⟩ := upper
  have fin := c.finite_toSet.subset sub
  obtain ⟨e⟩ := eight_of_infinite_point (by decide : 0<n) point
  choose rep eq_rep using fun i : Fin 8 => QuotientAddGroup.mk_surjective (e i)
  let f (i : Fin 8) := labels n (rep i)
  have inj : Function.Injective f := by
    intro i j eq
    exact e.injective ((eq_rep i).symm.trans ((kummer_separation (by decide) _ _ eq).trans (eq_rep j)))
  have lower : Set.range f ⊆ localClasses n := by
    rintro _ ⟨i,rfl⟩
    exact labels_local (by decide) _
  have h := Set.ncard_le_ncard lower fin
  have g := Set.ncard_le_ncard sub c.finite_toSet
  rw [Set.ncard_range_of_injective inj] at h
  simp at h g
  omega

theorem prepared_scalar_of_upper [AddGroup.FG (RationalPoint n)]
    (upper : ∃ c : Finset (ℤ × ℤ), c.card ≤ 8 ∧ localClasses n ⊆ (c : Set (ℤ × ℤ)))
    (point : ∃ P : RationalPoint n, ¬ IsOfFinAddOrder P) :
    ∃ e z : ℚ, Sun28.Ordinary.poleBranch 15 Sun28.PointFibres.pole e z :=
  prepared_scalar_of_card (local_count_of_upper point upper) point

end
end Sun28.MarkedDescent
#print axioms Sun28.MarkedDescent.local_count_of_upper
#print axioms Sun28.MarkedDescent.prepared_scalar_of_upper
