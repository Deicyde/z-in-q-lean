import NormCircles

namespace Sun28.QuadricSieve
open Finset
open scoped Classical
noncomputable section

/-- The two Gaussian points and the step on the affine five-variable cone. -/
abbrev Coordinates (R : Type*) := (R × R) × (R × R) × R

def onCone {R : Type*} [CommRing R] (κ : R) (x : Coordinates R) : Prop :=
  x.1.1^2+x.1.2^2-x.2.1.1^2-x.2.1.2^2=κ*x.2.2^2

def roots (p : ℕ) [Fact p.Prime] (t : ZMod p) : Finset (ZMod p) :=
  univ.filter fun y => y^2=t

theorem roots_card_le (p : ℕ) [Fact p.Prime] (t : ZMod p) : (roots p t).card ≤ 2 := by
  classical
  by_cases h : (roots p t).Nonempty
  · obtain ⟨b,hb⟩:=h
    have eqb := (mem_filter.mp hb).2
    have incl : roots p t ⊆ {b,-b} := by
      intro a ha
      have eqa := (mem_filter.mp ha).2
      have eq : (a-b)*(a+b)=0 := by linear_combination eqa-eqb
      rcases mul_eq_zero.mp eq with e|e
      · simp [sub_eq_zero.mp e]
      · simp [eq_neg_of_add_eq_zero_left e]
    exact (card_le_card incl).trans card_le_two
  · simp [not_nonempty_iff_eq_empty.mp h]

def diagonalSet (p : ℕ) [Fact p.Prime] (κ : ZMod p) : Finset (Coordinates (ZMod p)) :=
  univ.filter fun x => onCone κ x ∧ x.1.1=0 ∧ x.1.2^2= -1

/-- All five-coordinate self-collision classes satisfy the same 4p² bound as
the off-diagonal classes. Singular fibres of the second norm are included. -/
theorem diagonal_card_le (p : ℕ) [Fact p.Prime] (κ : ZMod p) :
    (diagonalSet p κ).card ≤ 4*p^2 := by
  classical
  let I : Finset (ZMod p) := univ
  let rows := (roots p (-1) ×ˢ I) ×ˢ I
  let choices := fun u : (ZMod p × ZMod p) × ZMod p => roots p (-1-κ*u.1.2^2-u.2^2)
  let assemble := fun (u : (ZMod p × ZMod p) × ZMod p) (b : ZMod p) =>
    (((0,u.1.1),(u.2,b),u.1.2) : Coordinates (ZMod p))
  have incl : diagonalSet p κ ⊆ rows.biUnion (fun u => (choices u).image (assemble u)) := by
    rintro ⟨⟨a,b⟩,⟨c,e⟩,w⟩ h
    obtain ⟨cone,ha,hb⟩ := (mem_filter.mp h).2
    change a=0 at ha
    change b^2= -1 at hb
    change a^2+b^2-c^2-e^2=κ*w^2 at cone
    subst a
    apply mem_biUnion.mpr
    refine ⟨((b,w),c),?_,mem_image.mpr ⟨e,?_,rfl⟩⟩
    · exact mem_product.mpr ⟨mem_product.mpr ⟨mem_filter.mpr ⟨mem_univ _,hb⟩,mem_univ _⟩,mem_univ _⟩
    · apply mem_filter.mpr
      exact ⟨mem_univ _,by change e^2= -1-κ*w^2-c^2; linear_combination hb-cone⟩
  have upper (u) : ((choices u).image (assemble u)).card ≤ 2 :=
    card_image_le.trans (roots_card_le _ _)
  calc
    _ ≤ _ := card_le_card incl
    _ ≤ ∑ u∈rows,((choices u).image (assemble u)).card := card_biUnion_le
    _ ≤ ∑ _∈rows,2 := sum_le_sum fun u _=>upper u
    _ = (roots p (-1)).card*p*p*2 := by simp [rows,I,mul_assoc]
    _ ≤ 2*p*p*2 := by gcongr; exact roots_card_le _ _
    _ = _ := by ring

theorem diagonal_nonzero {p : ℕ} [Fact p.Prime] {κ : ZMod p} {x}
    (h : x∈diagonalSet p κ) : x≠0 := by
  intro e
  have hb := (mem_filter.mp h).2.2.2
  subst x
  change (0:ZMod p)^2= -1 at hb
  simp at hb

theorem diagonal_empty_of_nonsquare {p : ℕ} [Fact p.Prime] (κ : ZMod p)
    (h : ¬ IsSquare (-1 : ZMod p)) : diagonalSet p κ=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  apply h
  refine ⟨x.1.2,?_⟩
  simpa [pow_two] using (mem_filter.mp hx).2.2.2.symm

theorem diagonal_empty_inert {p : ℕ} [Fact p.Prime] (κ : ZMod p) (hi : p%4=3) :
    diagonalSet p κ=∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact ZMod.mod_four_ne_three_of_sq_eq_neg_one (mem_filter.mp hx).2.2.2 hi

end
end Sun28.QuadricSieve
#print axioms Sun28.QuadricSieve.roots_card_le
#print axioms Sun28.QuadricSieve.diagonal_card_le
#print axioms Sun28.QuadricSieve.diagonal_nonzero
#print axioms Sun28.QuadricSieve.diagonal_empty_of_nonsquare
#print axioms Sun28.QuadricSieve.diagonal_empty_inert
