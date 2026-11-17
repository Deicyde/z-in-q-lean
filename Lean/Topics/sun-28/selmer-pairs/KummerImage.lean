import Mathlib.GroupTheory.Coset.Card
import Mathlib.Algebra.Group.Subgroup.Finite

namespace Sun28.SupportMatrix

/-- Once a group of order eight contains the four torsion classes, a single
image class outside torsion suffices to realize every marked class. -/
theorem image_eq_top {G : Type*} [AddGroup G] [Finite G] (T I : AddSubgroup G)
    (cardG : Nat.card G = 8) (cardT : Nat.card T = 4) (incl : T ≤ I)
    (extra : ∃ z : G, z ∈ I ∧ z ∉ T) : I = ⊤ := by
  have gap : 4 < Nat.card I := by
    by_contra! h
    obtain ⟨z, hz, hn⟩ := extra
    have eq := AddSubgroup.eq_of_le_of_card_ge incl (cardT ▸ h)
    exact hn (eq ▸ hz)
  have bound := Nat.le_of_dvd (show 0 < Nat.card G by omega) (AddSubgroup.card_addSubgroup_dvd_card I)
  have div := AddSubgroup.card_dvd_of_le incl
  rw [cardT] at div
  apply AddSubgroup.eq_top_of_card_eq
  omega

/-- Equivalence for any selected class outside the four torsion classes. -/
theorem marked_iff {G : Type*} [AddGroup G] [Finite G] (T I : AddSubgroup G) {m : G}
    (cardG : Nat.card G = 8) (cardT : Nat.card T = 4) (incl : T ≤ I) (outside : m ∉ T) :
    m ∈ I ↔ ∃ z : G, z ∈ I ∧ z ∉ T := by
  constructor
  · exact fun hm => ⟨m, hm, outside⟩
  · intro extra
    rw [image_eq_top T I cardG cardT incl extra]
    exact AddSubgroup.mem_top _

end Sun28.SupportMatrix
#print axioms Sun28.SupportMatrix.image_eq_top
#print axioms Sun28.SupportMatrix.marked_iff
