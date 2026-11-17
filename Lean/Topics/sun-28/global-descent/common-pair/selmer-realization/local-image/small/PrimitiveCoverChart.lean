import LocalKummerFibre
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Tactic

namespace Sun28.SmallImage
open Sun28.SelmerRealization
noncomputable section

/-- A projective solution in a chart where at least one coordinate equals one. -/
theorem residue_cover {p : ℕ} [Fact p.Prime] (e : ℕ) {l : ℕ} {a b : ℤ}
    (h : Cover ℚ_[p] l a b) :
    ∃ x y z t : ZMod (p^e), (x=1 ∨ y=1 ∨ z=1 ∨ t=1) ∧
    (a : ZMod (p^e))*b*x^2-b*y^2=l*t^2 ∧
    (a : ZMod (p^e))*z^2-a*b*x^2=3*l*t^2 := by
  obtain ⟨X,Y,Z,T,zn,h1,h2⟩:=h
  let v : Fin 4 → ℚ_[p] := ![X,Y,Z,T]
  obtain ⟨j,_,big⟩:=Finset.exists_max_image (Finset.univ : Finset (Fin 4))
    (fun i=>‖v i‖) Finset.univ_nonempty
  have le (i) : ‖v i‖≤‖v j‖ := big i (Finset.mem_univ _)
  have nz : v j≠0 := by
    intro zero
    have all (i) : v i=0 := norm_le_zero_iff.mp (by simpa [zero] using le i)
    rcases zn with h|h|h|h
    · exact h (all 0)
    · exact h (all 1)
    · exact h (all 2)
    · exact h (all 3)
  let u (i : Fin 4) : ℤ_[p] := ⟨v i / v j, by
    change ‖v i / v j‖ ≤ 1
    rw [norm_div]; exact (div_le_one (norm_pos_iff.mpr nz)).mpr (le i)⟩
  have uj : u j=1 := Subtype.ext (div_self nz)
  have rel1 : (a:ℤ_[p])*b*(u 0)^2-b*(u 1)^2=l*(u 3)^2 := by
    apply Subtype.ext
    change (a:ℚ_[p])*b*(X/v j)^2-b*(Y/v j)^2=l*(T/v j)^2
    field_simp [nz]
    linear_combination h1
  have rel2 : (a:ℤ_[p])*(u 2)^2-a*b*(u 0)^2=3*l*(u 3)^2 := by
    apply Subtype.ext
    change (a:ℚ_[p])*(Z/v j)^2-a*b*(X/v j)^2=3*l*(T/v j)^2
    field_simp [nz]
    linear_combination h2
  let f : ℤ_[p] →+* ZMod (p^e) := PadicInt.toZModPow e
  use f (u 0), f (u 1), f (u 2), f (u 3)
  refine ⟨?_,?_,?_⟩
  · have j1 : f (u j)=1 := by rw [uj,map_one]
    fin_cases j <;> tauto
  · simpa only [map_sub,map_mul,map_pow,map_intCast,map_natCast] using congrArg f rel1
  · simpa only [map_sub,map_mul,map_pow,map_intCast,map_natCast,map_ofNat] using congrArg f rel2

end
end Sun28.SmallImage
#print axioms Sun28.SmallImage.residue_cover
