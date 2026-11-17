import BranchFields
import ProjectiveDiagonal

namespace ZInQBlueprint.BranchId
open Diagonal210 IntermediateField
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- At infinity every projective point admits the normalization y₀=1. -/
theorem infinity_first_nonzero {y : Fin 4 → K} (onCurve : quadrics 0 y)
    (live : ∃ j,y j≠0) : y 0≠0 := by
  intro h
  have ⟨h1,h2,h3⟩:=onCurve
  rw [h] at h1 h2 h3
  norm_num at h1 h2 h3
  obtain ⟨j,hj⟩:=live
  apply hj
  fin_cases j
  · exact h
  · simp_all
  · simp_all
  · simp_all

def InfinityOpen (K : Type*) [Field K] := {z : Fin 3 → K // quadrics 0 ![1,z 0,z 1,z 2]}

private theorem ratios (q : InfinityOpen K) :
    (q.1 0)^2=3/7 ∧ (q.1 1)^2= -3 ∧ (q.1 2)^2=6 := by
  have ⟨a,b,c⟩:=q.2
  norm_num at a b c
  exact ⟨by linear_combination a/7,by linear_combination b,by linear_combination c/16⟩

private theorem finite_ratios (p : Fibre K coefficient (mark 2)) :
    (p.1 0)^2= -16807 ∧ (p.1 1)^2= -7200 ∧ p.1 2=0 ∧ (p.1 3)^2= -1620675/16 := by
  have a:=p.2 0; have b:=p.2 1; have c:=p.2 2; have d:=p.2 3
  norm_num [mark,coefficient] at a b c d ⊢
  exact ⟨a,b,c,d⟩

def fromInfinity (q : InfinityOpen K) : Fibre K coefficient (mark 2) := by
  obtain ⟨a,b,_⟩:=ratios q
  refine ⟨![49*q.1 1/q.1 0,60*q.1 2/q.1 1,0,735*q.1 1/4],?_⟩
  intro i
  fin_cases i <;> norm_num [mark,coefficient,div_pow,mul_pow,a,b,(ratios q).2.2]

def toInfinity (p : Fibre K coefficient (mark 2)) : InfinityOpen K := by
  let v:=4*p.1 3/735
  refine ⟨![49*v/p.1 0,v,p.1 1*v/60],?_⟩
  have ⟨a,b,_,d⟩:=finite_ratios p
  norm_num [quadrics,v,div_pow,mul_pow,a,b,d]

/-- The branch fibres with labels 42 and 210 are isomorphic over ℚ,
including their complete fields of definition. -/
def infinity_equiv_42 : InfinityOpen K ≃ Fibre K coefficient (mark 2) where
  toFun := fromInfinity
  invFun := toInfinity
  left_inv p := by
    have ⟨a,b,_⟩:=ratios p
    have u : p.1 0≠0 := by intro h; rw [h] at a; norm_num at a
    have v : p.1 1≠0 := by intro h; rw [h] at b; norm_num at b
    apply Subtype.ext; funext i; fin_cases i <;>
      norm_num [toInfinity,fromInfinity] <;> field_simp [u,v]
  right_inv p := by
    have ⟨a,_,c,d⟩:=finite_ratios p
    have u : p.1 0≠0 := by intro h; rw [h] at a; norm_num at a
    have v : p.1 3≠0 := by intro h; rw [h] at d; norm_num at d
    apply Subtype.ext; funext i; fin_cases i <;>
      norm_num [toInfinity,fromInfinity,c] <;> field_simp [u,v]

def infinityField (q : InfinityOpen ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range q.1)

theorem infinity_field (q : InfinityOpen ℂ) : infinityField q=rootField (fromInfinity q) := by
  let p:=fromInfinity q
  have hz (i : Fin 3) : q.1 i∈infinityField q := subset_adjoin ℚ _ ⟨i,rfl⟩
  have hp (i : Fin 4) : p.1 i∈rootField p := (generator p i).property
  apply le_antisymm
  · apply adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    have eqn : toInfinity p=q := infinity_equiv_42.left_inv q
    change q.1 i∈rootField p
    have val_eq : q.1 i=(toInfinity p).1 i := congrArg (fun z : InfinityOpen ℂ =>z.1 i) eqn.symm
    rw [val_eq]
    let F:=rootField p
    have hv : 4*p.1 3/735 ∈ F := by exact F.div_mem (F.mul_mem (F.natCast_mem _) (hp 3)) (F.natCast_mem _)
    fin_cases i
    · exact F.div_mem (F.mul_mem (F.natCast_mem _) hv) (hp 0)
    · exact hv
    · exact F.div_mem (F.mul_mem (hp 1) hv) (F.natCast_mem _)
  · apply adjoin_le_iff.mpr
    rintro _ ⟨i,rfl⟩
    let F:=infinityField q
    fin_cases i
    · exact F.div_mem (F.mul_mem (F.natCast_mem _) (hz 1)) (hz 0)
    · exact F.div_mem (F.mul_mem (F.natCast_mem _) (hz 2)) (hz 1)
    · exact F.zero_mem
    · exact F.div_mem (F.mul_mem (F.natCast_mem _) (hz 1)) (F.natCast_mem _)

theorem infinity_degree (q : InfinityOpen ℂ) : Module.finrank ℚ (infinityField q)=8 := by
  rw [infinity_field]
  exact finite_branch_degree 2 _

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.infinity_first_nonzero
#print axioms ZInQBlueprint.BranchId.infinity_equiv_42
#print axioms ZInQBlueprint.BranchId.infinity_field
#print axioms ZInQBlueprint.BranchId.infinity_degree
