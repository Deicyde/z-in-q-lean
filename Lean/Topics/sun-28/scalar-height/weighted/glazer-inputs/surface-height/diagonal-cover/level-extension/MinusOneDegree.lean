import RadicalTower
import CoarseDiscriminant
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace ZInQBlueprint.LevelExtension
open Diagonal210 NumberField
noncomputable section
set_option maxRecDepth 12000

private def four : List ℚ := [7,6,-42*1201,-21*311]
private def five : List ℚ := -3::four
private theorem full_rank : IndependentRadicals five := by decide +kernel

/-- The fourth signed equation carries a rational square denominator at s=-1. -/
private theorem actual_roots {L : Type*} [Field L] [CharZero L]
    (y : Fibre L coefficient (-1)) : ∀ d∈four,IsSquare (algebraMap ℚ L d) := by
  intro d hd
  simp only [four,List.mem_cons,List.not_mem_nil,or_false] at hd
  rcases hd with rfl|rfl|rfl|rfl
  · refine ⟨y.1 0,?_⟩
    simpa [coefficient,mark,←sq] using (y.2 0).symm
  · refine ⟨y.1 1,?_⟩
    have h:=y.2 1
    norm_num [coefficient,mark] at h ⊢
    linear_combination -h
  · refine ⟨y.1 2,?_⟩
    have h:=y.2 2
    norm_num [coefficient,mark] at h ⊢
    linear_combination -h
  · refine ⟨4*y.1 3,?_⟩
    have h:=y.2 3
    norm_num [coefficient,mark] at h ⊢
    linear_combination -16*h

/-- At the negative unit slope the four actual coordinate roots have degree exactly 16. -/
theorem minus_one_coarse_degree (y : Fibre ℂ coefficient (-1)) :
    Module.finrank ℚ (rootField y) = 16 := by
  let v : Fibre (rootField y) coefficient (-1) := ⟨generator y,generator_sq y⟩
  have prod := radical_degree_dvd four full_rank.2 (actual_roots v)
  have div : 16 ∣ Module.finrank ℚ (rootField y) := prod
  exact le_antisymm (rootField_degree y) (Nat.le_of_dvd Module.finrank_pos div)

/-- A primitive third root and a point above the actual slope force degree
divisible by 32. A full level field supplies the former through the Weil pairing. -/
theorem minus_one_level_degree {L : Type*} [Field L] [NumberField L]
    (y : Fibre L coefficient (-1)) {ζ : L} (primitive : IsPrimitiveRoot ζ 3) :
    32 ∣ Module.finrank ℚ L := by
  have zn : ζ-1≠0 := sub_ne_zero.mpr (primitive.ne_one (by decide))
  have eq : (ζ-1)*(ζ^2+ζ+1)=0 := by linear_combination primitive.pow_eq_one
  have zq := (mul_eq_zero.mp eq).resolve_left zn
  have roots : ∀ d∈five,IsSquare (algebraMap ℚ L d) := by
    intro d mem
    rcases List.mem_cons.mp mem with rfl|h
    · refine ⟨2*ζ+1,?_⟩
      norm_num
      linear_combination -4*zq
    · exact actual_roots y d h
  exact radical_degree_dvd five full_rank roots

/-- The degree-sixteen equation alone cannot carry a full rational three-torsion
marking on a principally polarized surface at this slope. -/
theorem minus_one_no_primitive (y : Fibre ℂ coefficient (-1)) :
    ¬∃ ζ : rootField y, IsPrimitiveRoot ζ 3 := by
  rintro ⟨ζ,prim⟩
  let v : Fibre (rootField y) coefficient (-1) := ⟨generator y,generator_sq y⟩
  have bad := minus_one_level_degree v prim
  rw [minus_one_coarse_degree] at bad
  norm_num at bad

end
end ZInQBlueprint.LevelExtension
#print axioms ZInQBlueprint.LevelExtension.minus_one_coarse_degree
#print axioms ZInQBlueprint.LevelExtension.minus_one_level_degree
#print axioms ZInQBlueprint.LevelExtension.minus_one_no_primitive
