import LocalKummerFibre
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.QuotientGroup.Basic

namespace Sun28.SelmerRealization
noncomputable section

def doubles (G : Type*) [AddCommGroup G] : AddSubgroup G where
  carrier := Set.range (fun x : G => (2:ℕ) • x)
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩;exact ⟨a+b,by simp⟩
  neg_mem' := by rintro _ ⟨a,rfl⟩;exact ⟨-a,by simp⟩

abbrev ModTwo (l : ℕ) := RationalPoint l ⧸ doubles (RationalPoint l)

/-- Classical full two-descent, in the direction of injectivity only. -/
def KummerSeparation (l : ℕ) : Prop :=
  ∀ P Q : RationalPoint l, labels l P = labels l Q →
    (QuotientAddGroup.mk P : ModTwo l) = QuotientAddGroup.mk Q

/-- The point group modulo doubles, as supplied at rank one by the
Mordell--Weil theorem and full rational two-torsion. -/
def EightPointClasses (l : ℕ) : Prop := Nonempty (Fin 8 ↪ ModTwo l)

/-- A concrete local Descent computation. The hypotheses refer only to the
real place and rational p-adic places, and contain no rational solubility test. -/
def FiniteDescent (l : ℕ) (a b : ℤ) : Prop :=
  (localClasses l).ncard = 8 ∧ (a,b) ∈ localClasses l

theorem all_classes_realized {l : ℕ} (lp : 0<l) (separates : KummerSeparation l)
    (eight : EightPointClasses l) (size : (localClasses l).ncard=8) :
    ∀ ab ∈ localClasses l, Cover ℚ l ab.1 ab.2 := by
  classical
  obtain ⟨j⟩:=eight
  choose rep eq_rep using (fun i : Fin 8 =>
    (QuotientAddGroup.mk_surjective (j i)))
  let f (i : Fin 8) := labels l (rep i)
  have inj : Function.Injective f := by
    intro i i' eq
    exact j.injective ((eq_rep i).symm.trans ((separates _ _ eq).trans (eq_rep i')))
  have sub : Set.range f ⊆ localClasses l := by
    rintro _ ⟨i,rfl⟩
    exact labels_local lp _
  have card : (Set.range f).ncard = 8 := by simp [Set.ncard_range_of_injective inj]
  have eq := Set.eq_of_subset_of_ncard_le sub (by omega)
    (Set.finite_of_ncard_pos (by omega))
  intro ab h
  rw [←eq] at h
  obtain ⟨i,rfl⟩:=h
  exact labels_cover lp (rep i)

theorem marked_of_descent {l : ℕ} {b : ℤ} (lp : 0<l) (separates : KummerSeparation l)
    (eight : EightPointClasses l) (finite : FiniteDescent l b 1) :
    Sun28.SupportMatrix.MarkedCover (b:ℚ) (l:ℚ) :=
  (rational_cover l b).mp (all_classes_realized lp separates eight finite.1 _ finite.2)

end
end Sun28.SelmerRealization
#print axioms Sun28.SelmerRealization.all_classes_realized
#print axioms Sun28.SelmerRealization.marked_of_descent
