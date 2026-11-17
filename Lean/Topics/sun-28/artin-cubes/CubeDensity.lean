import WrappedCube

namespace Sun28.ArtinCube
open Finset
open scoped Classical
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} [Fact p.Prime]

/-- The number of forbidden first coordinates, summed over all cube steps. -/
def occupied (S : Finset (Finset ι)) (q : ZMod p) (b : Finset ι → ZMod p) : ℕ :=
  ∑ h : ι → ZMod p, (S.image (fun v => shift q b v h)).card

def totalSteps (ι : Type*) [Fintype ι] [DecidableEq ι] (p : ℕ) [NeZero p] := Fintype.card (ι → ZMod p)

theorem occupied_le (S : Finset (Finset ι)) (q : ZMod p) (b : Finset ι → ZMod p) :
    occupied S q b ≤ totalSteps ι p * S.card := by
  unfold occupied
  exact (sum_le_sum fun _ _ => card_image_le).trans_eq (by simp [totalSteps,Nat.mul_comm])

/-- Second Bonferroni bound. Every pair of distinct vertices coincides on at most
one p-th of the step tuples. Ordered insertion counts each pair just once. -/
theorem occupied_lower (S : Finset (Finset ι)) (q : ZMod p) (hq : q ≠ 0)
    (b : Finset ι → ZMod p) :
    totalSteps ι p * S.card * p ≤ p * occupied S q b + totalSteps ι p * S.card.choose 2 := by
  classical
  let D := totalSteps ι p
  induction S using Finset.induction_on with
  | empty => simp [occupied]
  | @insert v S hv ih =>
    let H := fun w : Finset ι => univ.filter (fun h : ι → ZMod p => shift q b v h = shift q b w h)
    let B := S.biUnion H
    have bad : p * B.card ≤ D * S.card := calc
      _ ≤ p * ∑ w ∈ S,(H w).card := Nat.mul_le_mul_left _ card_biUnion_le
      _ = ∑ w ∈ S,p * (H w).card := mul_sum ..
      _ ≤ ∑ _ ∈ S,D := sum_le_sum fun w hw => equal_slices q hq b (ne_of_mem_of_not_mem hw hv).symm
      _ = _ := by simp [Nat.mul_comm]
    have one (h : ι → ZMod p) :
        ((insert v S).image (fun w => shift q b w h)).card + (if h ∈ B then 1 else 0) =
        (S.image (fun w => shift q b w h)).card + 1 := by
      have iff : h ∈ B ↔ shift q b v h ∈ S.image (fun w => shift q b w h) := by
        simp [B,H,eq_comm]
      rw [image_insert]
      by_cases yes : h ∈ B
      · simp [yes,insert_eq_of_mem (iff.mp yes)]
      · have no := mt iff.mpr yes
        simp [yes,no]
    have steps : occupied (insert v S) q b + B.card = occupied S q b + D := by
      have hs := sum_congr (s₁:=univ) rfl (fun h _ => one h)
      simpa [occupied,sum_add_distrib,D,totalSteps] using hs
    have recu : (S.card+1).choose 2 = S.card + S.card.choose 2 := by
      rw [Nat.choose_succ_succ]; simp
    rw [card_insert_of_notMem hv,recu]
    change D*S.card*p ≤ p*occupied S q b+D*S.card.choose 2 at ih
    change D*(S.card+1)*p ≤ p*occupied (insert v S) q b + D*(S.card+S.card.choose 2)
    nlinarith only [ih,bad,congrArg (fun z : ℕ => p*z) steps]

/-- The fraction of permissible first coordinates in the complete cube. -/
def rate (S : Finset (Finset ι)) (q : ZMod p) (b : Finset ι → ZMod p) : ℝ :=
  1-(occupied S q b : ℝ)/((totalSteps ι p : ℝ)*p)

theorem rate_bounds (S : Finset (Finset ι)) (q : ZMod p) (b : Finset ι → ZMod p) :
    1-(S.card:ℝ)/p ≤ rate S q b ∧ rate S q b ≤ 1 := by
  have pos : 0 < (totalSteps ι p : ℝ) := by exact_mod_cast Fintype.card_pos (α:=ι → ZMod p)
  have pp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have h : (occupied S q b:ℝ) ≤ (totalSteps ι p:ℝ)*S.card := by exact_mod_cast occupied_le S q b
  unfold rate
  constructor
  · apply sub_le_sub_left
    apply (div_le_iff₀ (mul_pos pos pp)).mpr
    convert h using 1; field_simp
  · exact sub_le_self _ (by positivity)

theorem rate_good (S : Finset (Finset ι)) (q : ZMod p) (hq : q ≠ 0)
    (b : Finset ι → ZMod p) :
    rate S q b ≤ 1-(S.card:ℝ)/p+(S.card.choose 2:ℝ)/(p:ℝ)^2 := by
  have pos : 0 < (totalSteps ι p : ℝ) := by exact_mod_cast Fintype.card_pos (α:=ι → ZMod p)
  have pp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have h : (totalSteps ι p:ℝ)*S.card*p ≤ (p:ℝ)*occupied S q b+(totalSteps ι p:ℝ)*(S.card.choose 2) := by
    exact_mod_cast occupied_lower S q hq b
  unfold rate
  field_simp
  nlinarith only [h]

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.occupied_le
#print axioms Sun28.ArtinCube.occupied_lower
#print axioms Sun28.ArtinCube.rate_bounds
#print axioms Sun28.ArtinCube.rate_good
