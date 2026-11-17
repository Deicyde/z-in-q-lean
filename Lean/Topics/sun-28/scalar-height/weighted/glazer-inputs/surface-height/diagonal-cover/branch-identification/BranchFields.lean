import QuarticCoordinates
import CoverField
import RadicalTower

namespace ZInQBlueprint.BranchId
open Diagonal210 LevelExtension IntermediateField
noncomputable section
set_option maxRecDepth 12000

/-- In each finite branch fibre these are the squareclasses of its three nonzero coordinates. -/
def bases : Fin 4 → Fin 3 → ℚ := ![![3,-21,-3],![-7,-14,-35],![-7,-2,-3],![2,10,-6]]
def factors : Fin 4 → Fin 3 → ℚ := ![![1,49,49/4],![1,60,15/4],![49,60,735/4],![49/8,15/8,735/8]]

theorem finite_branch_classes (i : Fin 4) (j : Fin 3) :
    radicand (mark i) (keep i j) = bases i j * (factors i j)^2 ∧ factors i j≠0 := by
  fin_cases i <;> fin_cases j <;> norm_num [radicand,mark,coefficient,keep,bases,factors]

private theorem covers_indices (i j : Fin 4) : j=i ∨ ∃ k,keep i k=j := by
  revert i j
  decide +kernel

private theorem upper (i : Fin 4) (y : Fibre ℂ coefficient (mark i)) : Module.finrank ℚ (rootField y) ≤ 8 := by
  classical
  let := finite_rootField y
  have van : generator y i = 0 := by
    have e:=generator_sq y i
    simp only [radicand,sub_self,mul_zero,map_zero] at e
    exact (pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp e
  let sign (f : rootField y →ₐ[ℚ] ℂ) (j : Fin 3) : Bool := decide (f (generator y (keep i j))=y.1 (keep i j))
  have inj : Function.Injective sign := by
    intro f g h
    apply IntermediateField.adjoin_algHom_ext
    rintro _ ⟨a,rfl⟩
    change f (generator y a)=g (generator y a)
    obtain rfl|⟨j,rfl⟩:=covers_indices i a
    · simp [van]
    · let a:=keep i j
      have same : (f (generator y a)=y.1 a) ↔ (g (generator y a)=y.1 a) := by
        have e := congrFun h j
        change decide _ = decide _ at e
        simpa [a] using e
      have choices (k : rootField y →ₐ[ℚ] ℂ) :
          k (generator y a)=y.1 a ∨ k (generator y a)= -y.1 a := by
        apply sq_eq_sq_iff_eq_or_eq_neg.mp
        rw [←map_pow,generator_sq,k.commutes,y.2 a]
        rfl
      rcases choices f with fpos|fneg
      · exact fpos.trans (same.mp fpos).symm
      · rcases choices g with gpos|gneg
        · exact (same.mpr gpos).trans gpos.symm
        · exact fneg.trans gneg.symm
  rw [←AlgHom.card ℚ (rootField y) ℂ]
  simpa using Fintype.card_le_of_injective sign inj

theorem finite_branch_degree (i : Fin 4) (y : Fibre ℂ coefficient (mark i)) :
    Module.finrank ℚ (rootField y)=8 := by
  let D : List ℚ := [bases i 0,bases i 1,bases i 2]
  have ind : IndependentRadicals D := by fin_cases i <;> decide +kernel
  have root (j : Fin 3) : IsSquare (algebraMap ℚ (rootField y) (bases i j)) := by
    let f:=algebraMap ℚ (rootField y) (factors i j)
    have nz : f≠0 := (map_ne_zero _).mpr (finite_branch_classes i j).2
    refine ⟨generator y (keep i j)/f,?_⟩
    rw [←sq,div_pow,eq_div_iff (pow_ne_zero 2 nz),generator_sq,(finite_branch_classes i j).1,map_mul,map_pow]
  have allroots : ∀ d∈D,IsSquare (algebraMap ℚ (rootField y) d) := by
    intro d hd
    simp only [D,List.mem_cons,List.not_mem_nil,or_false] at hd
    rcases hd with rfl|rfl|rfl
    · exact root 0
    · exact root 1
    · exact root 2
  have lower : 8 ∣ Module.finrank ℚ (rootField y) := radical_degree_dvd D ind allroots
  let :=finite_rootField y
  exact le_antisymm (upper i y) (Nat.le_of_dvd Module.finrank_pos lower)

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.finite_branch_classes
#print axioms ZInQBlueprint.BranchId.finite_branch_degree
