import InertAvoidance

namespace Sun28.PrimeLower
open Finset Sun28.MixedSieve
open scoped Classical
noncomputable section
variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι]

/-- The one excluded rational row really has an obstructed Gaussian lift. Hence
this is the exact projection of the bad tuples in the complete local fibre model. -/
theorem inert_projection_iff (c : ι → ZMod p) (inj : Function.Injective c)
    (hi : p%4=3) (u w : ZMod p) :
    (∃ z : (i : ι) → Circle p (norms c u w i), z∈obstructed _) ↔ u=1 ∧ w=0 := by
  constructor
  · rintro ⟨z,h⟩
    exact inert_collision hi inj z h
  · rintro ⟨rfl,rfl⟩
    obtain ⟨i,j,ij⟩ := exists_pair_ne ι
    let z (k : ι) : Circle p (norms c 1 0 k) :=
      ⟨(if k=i then (-1,0) else (1,0)),by by_cases h : k=i <;> simp [h,norms]⟩
    refine ⟨z,(obstructed_iff z).mpr ⟨i,j,?_,?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨mem_univ _,by simp [z]⟩
    · exact Finset.mem_filter.mpr ⟨mem_univ _,by simp [z,ij.symm]⟩

end
end Sun28.PrimeLower
#print axioms Sun28.PrimeLower.inert_projection_iff
