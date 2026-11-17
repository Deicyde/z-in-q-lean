import PrimaryLayers
import FixedLocalCount

namespace Sun28.Corank
open Sun28.SelmerRealization
noncomputable section

/-- The only identification required with a computed local Selmer set.
It is a set bijection; no group structure is imposed on the signed labels. -/
def LocalComparison (l : ℕ) (K : PrimaryData (RationalPoint l)) : Prop :=
  Nonempty (K.sel 1 ≃ (localClasses l))

theorem card_first {l : ℕ} (K : PrimaryData (RationalPoint l))
    (comparison : LocalComparison l K) (size : (localClasses l).ncard=8) :
    Nat.card (K.sel 1)=8 := by
  obtain ⟨e⟩ := comparison
  exact (Nat.card_congr e).trans ((Nat.card_coe_set_eq _).trans size)

/-- The exact corank alternatives for the eight literal everywhere-local
coverings. Both alternatives give the same higher Selmer cardinalities. -/
theorem fixed_dichotomy [AddGroup.FG (RationalPoint n)] (K : PrimaryData (RationalPoint n))
    (comparison : LocalComparison n K) :
    Subsingleton K.reduced ∧
    (∃ (r : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      Nonempty (RationalPoint n ≃+ (Fin r → ℤ) × T) ∧ r+K.d=1) ∧
    ∀ j : ℕ, Nat.card (K.sel j) = Nat.card (torsionAt (RationalPoint n) (2^j)) * 2^j := by
  obtain ⟨r,T,_,_,⟨f⟩⟩ := split_finitely_generated (RationalPoint n)
  have tors := four_torsion (l:=n) (by decide)
  have eight := card_first K comparison Sun28.FixedLocalRows.local_class_count
  obtain ⟨triv,rank⟩ := corank_one K f tors eight
  exact ⟨triv,⟨r,T,inferInstance,inferInstance,⟨f⟩,rank⟩,all_higher_card K f tors eight⟩

theorem eight_rational_iff {l : ℕ} (hl : 0<l) [AddGroup.FG (RationalPoint l)]
    (K : PrimaryData (RationalPoint l)) (comparison : LocalComparison l K)
    (size : (localClasses l).ncard=8) : EightPointClasses l ↔ K.d=0 := by
  classical
  obtain ⟨r,T,_,_,⟨f⟩⟩ := split_finitely_generated (RationalPoint l)
  have tors := four_torsion hl
  have eight := card_first K comparison size
  have H := corank_one K f tors eight
  have all := quotient_growth f (by decide : 2≠0)
  rw [tors] at all
  change Nat.card (ModTwo l) = _ at all
  have fin : Finite (ModTwo l) := Nat.finite_of_card_ne_zero (by rw [all]; positivity)
  let : Fintype (ModTwo l) := Fintype.ofFinite _
  constructor
  · rintro ⟨i⟩
    have bound := Fintype.card_le_of_injective i i.injective
    rw [Fintype.card_fin,←Nat.card_eq_fintype_card,all] at bound
    by_contra hn
    have rz : r=0 := by omega
    simp [rz] at bound
  · intro dz
    have ro : r=1 := by omega
    apply Function.Embedding.nonempty_of_card_le
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,Nat.card_fin,all,ro]
    decide

theorem fixed_scalar_of_no_divisible [AddGroup.FG (RationalPoint n)]
    (K : PrimaryData (RationalPoint n)) (comparison : LocalComparison n K) (none : K.d=0) :
    ∃ e z : ℚ, Sun28.Ordinary.poleBranch 15 Sun28.PointFibres.pole e z :=
  prepared_scalar_of_eight (Sun28.MarkedDescent.kummer_separation (by decide))
    Sun28.FixedLocalRows.fixed_descent
    ((eight_rational_iff (by decide) K comparison Sun28.FixedLocalRows.local_class_count).mpr none)

end
end Sun28.Corank

#print axioms Sun28.Corank.card_first
#print axioms Sun28.Corank.fixed_dichotomy
#print axioms Sun28.Corank.eight_rational_iff
#print axioms Sun28.Corank.fixed_scalar_of_no_divisible
