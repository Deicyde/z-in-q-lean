import OrdinaryFactors

namespace Sun28.ArtinCube
open Finset
noncomputable section
open scoped Classical
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {p : ℕ} [Fact p.Prime]

/-- Displacement of a vertex. Arbitrary shifts include the multiples of the period
subtracted when the cyclic cube is cut into wrap cells. -/
def shift (q : ZMod p) (b : Finset ι → ZMod p) (v : Finset ι) (h : ι → ZMod p) :=
  q * (∑ i ∈ v, h i) + b v

/-- If the step coefficient is a unit, varying one coordinate on which the
vertices differ gives at most one coincidence per choice of all other steps. -/
theorem equal_slices (q : ZMod p) (hq : q ≠ 0) (b : Finset ι → ZMod p)
    {v w : Finset ι} (vw : v ≠ w) :
    p * (univ.filter (fun h : ι → ZMod p => shift q b v h = shift q b w h)).card
      ≤ Fintype.card (ι → ZMod p) := by
  classical
  obtain ⟨i,diff⟩ : ∃ i : ι, ¬(i ∈ v ↔ i ∈ w) := by
    by_contra! h
    exact vw (Finset.ext h)
  let H := univ.filter (fun h : ι → ZMod p => shift q b v h = shift q b w h)
  let F := fun h : ι → ZMod p => (fun j : {j : ι // j ≠ i} => h j)
  have inj : (H : Set (ι → ZMod p)).InjOn F := by
    intro h hh g hg rest
    have hother (j : ι) (hn : j ≠ i) : h j = g j := congrFun rest ⟨j,hn⟩
    have sub (z : Finset ι) : (∑ j ∈ z.erase i,h j) = ∑ j ∈ z.erase i,g j :=
      sum_congr rfl fun j hmem => hother j (ne_of_mem_erase hmem)
    have sum_out (z : Finset ι) (out : i ∉ z) : (∑ j ∈ z,h j) = ∑ j ∈ z,g j :=
      by simpa only [erase_eq_of_notMem out] using sub z
    have sum_in (z : Finset ι) (inside : i ∈ z) :
        (∑ j ∈ z, h j) - (∑ j ∈ z,g j) = h i - g i := by
      linear_combination (sum_erase_add z h inside).symm -
        (sum_erase_add z g inside).symm + sub z
    have a := (mem_filter.mp hh).2
    have c := (mem_filter.mp hg).2
    change q * (∑ j ∈ v,h j) + b v = q * (∑ j ∈ w,h j) + b w at a
    change q * (∑ j ∈ v,g j) + b v = q * (∑ j ∈ w,g j) + b w at c
    have delta : q * (h i - g i) = 0 := by
      by_cases iv : i ∈ v
      · have iw : i ∉ w := fun hw => diff (iff_of_true iv hw)
        linear_combination a - c - q * sum_in v iv + q * sum_out w iw
      · have iw : i ∈ w := by by_contra h; exact diff (iff_of_false iv h)
        linear_combination c - a - q * sum_in w iw + q * sum_out v iv
    funext j
    by_cases ji : j=i
    · subst j; exact sub_eq_zero.mp ((mul_eq_zero.mp delta).resolve_left hq)
    · exact hother j ji
  have small := card_le_card_of_injOn (t:=univ) F (fun _ _ => mem_univ _) inj
  have total := Fintype.card_congr (Equiv.funSplitAt i (ZMod p))
  rw [Fintype.card_prod,ZMod.card] at total
  rw [card_univ] at small
  exact (Nat.mul_le_mul_left p small).trans_eq total.symm

end
end Sun28.ArtinCube
#print axioms Sun28.ArtinCube.equal_slices
