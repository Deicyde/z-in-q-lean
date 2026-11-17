import SplitObstruction

namespace Sun28.PrimeLower
open Finset Sun28.MixedSieve
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- At a split prime a rational norm vector supports *both* an obstructed tuple and
an unobstructed one. Therefore membership of its norm residues alone cannot certify
survival of every Gaussian lift, even at one prime. -/
theorem split_same_norm_good_and_bad (split : p%4=1) (big : 7≤p)
    (t : ι → ZMod p) (units : ∀ i,t i≠0) :
    (∃ z : (i : ι) → Circle p (t i), z∈obstructed t) ∧
    (∃ z : (i : ι) → Circle p (t i), z∉obstructed t) := by
  obtain ⟨i,j,ij⟩ := exists_pair_ne ι
  let off (r : ι) (e : Bool) : Circle p (t r) := (split_bad_all split (t r) e).choose
  have badAt (r : ι) (e : Bool) : off r e ∈bad p (t r) e := (split_bad_all split (t r) e).choose_spec
  let hit (r : ι) := if r=i then off r true else off r false
  have hi : hit i∈bad p (t i) true := by simpa [hit] using badAt i true
  have hj : hit j∈bad p (t j) false := by simpa [hit,ij.symm] using badAt j false
  refine ⟨⟨hit,(obstructed_iff hit).mpr ⟨i,j,hi,hj⟩⟩,?_⟩
  have get (r : ι) : ((bad p (t r) true)ᶜ).Nonempty := by
    apply card_pos.mp
    rw [card_compl]
    have lo := circle_card_lower (by omega : p≠2) (units r)
    have hi := bad_card (by omega : p≠2) (t r) true
    omega
  let z (r : ι) := (get r).choose
  refine ⟨z,?_⟩
  intro h
  obtain ⟨r,_,badZ,_⟩ := (obstructed_iff z).mp h
  exact (Finset.mem_compl.mp (get r).choose_spec) badZ

end
end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.split_same_norm_good_and_bad
