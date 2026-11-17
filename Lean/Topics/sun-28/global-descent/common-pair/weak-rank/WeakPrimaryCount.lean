import WeakLocalCount
import Mathlib.GroupTheory.PGroup

namespace Sun28.WeakRank
open Sun28.SelmerRealization Sun28.Corank Sun28.PairedClasses Sun28.SeededPartners Sun28.GlobalSections
noncomputable section

/-- The previously specified exact primary Kummer data imply that the
finite label count is a power of two. -/
theorem local_power {l : ℕ} (lp : 0<l) [AddGroup.FG (RationalPoint l)]
    (K : PrimaryData (RationalPoint l)) (cmp : LocalComparison l K) :
    ∃ j:ℕ,(localClasses l).ncard=2^j := by
  let G := torsionAt K.reduced 2
  have killed (x : G) : (2:ℕ) • x=0 := by
    apply Subtype.ext
    exact x.property
  have pg : IsPGroup 2 (Multiplicative G) := by
    intro g
    refine ⟨1,?_⟩
    rw [pow_one]
    exact congrArg Multiplicative.ofAdd (killed g.toAdd)
  obtain ⟨i,ci⟩ := pg.exists_card_eq
  change Nat.card (torsionAt K.reduced 2) = 2^i at ci
  obtain ⟨r,T,_,_,⟨f⟩⟩ := split_finitely_generated (RationalPoint l)
  obtain ⟨e⟩ := cmp
  have count := layer_count K f 1
  rw [pow_one,four_torsion lp,ci,Nat.card_congr e,Nat.card_coe_set_eq] at count
  exact ⟨2+(r+K.d)+i,by rw [count];simp only [pow_add];norm_num⟩

theorem sixteen_of_primary {b d q : ℕ} (ad : AdmissiblePair b d) (C : Candidate b d q)
    (outside : ¬CancelledFactors b d) (hit : strictPoint b ((b*q)*d))
    [AddGroup.FG (RationalPoint ((b*q)*d))] (K : PrimaryData (RationalPoint ((b*q)*d)))
    (cmp : LocalComparison ((b*q)*d) K) : 16 ≤ (localClasses ((b*q)*d)).ncard := by
  have p := ad.1
  have dpos := ad.2.1
  have qp := C.nontrivial
  exact sixteen_of_power_of_two ad C outside hit (local_power (by positivity) K cmp)

end
end Sun28.WeakRank
#print axioms Sun28.WeakRank.local_power
#print axioms Sun28.WeakRank.sixteen_of_primary
