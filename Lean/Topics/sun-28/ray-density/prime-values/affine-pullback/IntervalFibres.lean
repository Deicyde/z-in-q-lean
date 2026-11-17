import AffineSteps

namespace Sun28.AffinePullback
open Finset
noncomputable section

/-- Representative interval of the class r in {0,...,J-1}, after division by h. -/
def lengthAt (J h r : ℕ) := J/h + if r<J%h then 1 else 0

theorem quotient_lt_iff (J h r u : ℕ) (hh : 0<h) (hr : r<h) :
    u < lengthAt J h r ↔ h*u+r < J := by
  have rem := Nat.mod_lt J hh
  have dec := Nat.mod_add_div J h
  by_cases hrJ : r<J%h
  · simp only [lengthAt, ite_eq_left hrJ]
    constructor
    · intro hu
      have hm := Nat.mul_le_mul_left h (show u≤J/h by omega)
      omega
    · intro hu
      by_contra! hn
      have hm := Nat.mul_le_mul_left h (show J/h+1≤u by omega)
      rw [Nat.mul_succ] at hm
      omega
  · simp only [lengthAt, ite_eq_right hrJ, Nat.add_zero]
    constructor
    · intro hu
      have hm := Nat.mul_le_mul_left h (show u+1≤J/h by omega)
      rw [Nat.mul_succ] at hm
      omega
    · intro hu
      by_contra! hn
      have hm := Nat.mul_le_mul_left h hn
      omega

theorem fibre_sum (J h r : ℕ) (hh : 0<h) (hr : r<h) (F : ℕ → ℝ) :
    ∑ i ∈ (range J).filter (fun i => i%h=r), F (i/h) =
      ∑ u ∈ range (lengthAt J h r), F u := by
  apply Finset.sum_bij (fun i _ => i/h)
  · intro i hi
    obtain ⟨hi,eq⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_range.mpr
    apply (quotient_lt_iff J h r _ hh hr).2
    rw [← eq, add_comm, Nat.mod_add_div]
    exact Finset.mem_range.mp hi
  · intro a ha b hb hab
    have ar := (Finset.mem_filter.mp ha).2
    have br := (Finset.mem_filter.mp hb).2
    have aa := Nat.mod_add_div a h
    have bb := Nat.mod_add_div b h
    rw [ar] at aa
    rw [br, ← hab] at bb
    omega
  · intro u hu
    refine ⟨h*u+r, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr ((quotient_lt_iff J h r u hh hr).1 (Finset.mem_range.mp hu)),
        by simp [Nat.add_mod, Nat.mod_eq_of_lt hr]⟩
    · simpa [Nat.div_eq_of_lt hr] using Nat.mul_add_div hh u r
  · intros; rfl

theorem pair_fibre_sum (J h : ℕ) (hh : 0<h) (K : ℕ → ℕ → ℝ) :
    ∑ i ∈ range J, ∑ j ∈ range J, (if i%h=j%h then K (i/h) (j/h) else 0) =
      ∑ r ∈ range h, ∑ u ∈ range (lengthAt J h r), ∑ v ∈ range (lengthAt J h r), K u v := by
  classical
  have mem (i : ℕ) (_ : i∈range J) : i%h ∈ range h := mem_range.mpr (Nat.mod_lt _ hh)
  rw [← Finset.sum_fiberwise_of_maps_to mem (fun i => ∑ j ∈ range J, (if i%h=j%h then K (i/h) (j/h) else 0))]
  apply Finset.sum_congr rfl
  intro r hr
  have hR := Finset.mem_range.mp hr
  calc
    _ = ∑ i ∈ (range J).filter (fun i => i%h=r), (∑ v ∈ range (lengthAt J h r), K (i/h) v) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
      rw [← fibre_sum J h r hh hR (K (i/h)), Finset.sum_filter]
      simp only [eq_comm]
    _ = _ := fibre_sum J h r hh hR (fun u => ∑ v ∈ range (lengthAt J h r), K u v)

theorem lengthAt_card (J h r : ℕ) (hh : 0<h) (hr : r<h) :
    lengthAt J h r = ((range J).filter (fun i => i%h=r)).card := by
  have hw := fibre_sum J h r hh hr (fun _ => 1)
  simpa using hw.symm

end
end Sun28.AffinePullback
#print axioms Sun28.AffinePullback.quotient_lt_iff
#print axioms Sun28.AffinePullback.fibre_sum
#print axioms Sun28.AffinePullback.pair_fibre_sum
#print axioms Sun28.AffinePullback.lengthAt_card
