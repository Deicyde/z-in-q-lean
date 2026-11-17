import FreeParameters
import RationalLocalization

/-! The remaining global height hypothesis at the actual polynomial entry point. -/
namespace Sun28.Forward
open Sun28.Ordinary Sun28.ScalarHeight Sun28.FiveMarkUnits ZInQ
noncomputable section

/-- The only five-mark cases still assumed are the primitive pairs with
large residual prime support. The external height theorem concerns actual
units u+v=1 of Z[1/N]. The same finite branch list and constants are used
for both directions of the polynomial projection. -/
theorem compiled_projection_of_large_residual {c Γ D Uo Us} (cn : c≠0) (gn : Γ≠0)
    (chart : OrdinaryCharts (commonCutoff c Γ Uo Us) K0)
    (published : PublishedCorollary72) (remaining : LargeResidualHeight)
    (bs : List (Sun28.Compiler.Branch 28)) (branches : ExactBranchList c Γ D Uo Us bs)
    (complete : IntegerWitnesses c Γ D Uo Us) (x : ℚ) :
    (∃ y : Fin 28 → ℚ, Sun28.eval28 (Sun28.Branches.polynomial28 (Sun28.Compiler.branchAtlas bs)) x y=0) ↔
      ∃ k : ℤ, x=(k:ℚ) :=
  compiled_point_projection cn gn chart ((original_five_from_units published).2 remaining)
    bs branches complete x

/-- One-way arithmetic decoding suffices for branches that also check denominator guards.
Completeness asks for actual solutions on integer inputs in those very branches. -/
theorem guarded_projection_of_large_residual {c Γ D Uo Us} (cn : c≠0) (gn : Γ≠0)
    (chart : OrdinaryCharts (commonCutoff c Γ Uo Us) K0)
    (published : PublishedCorollary72) (remaining : LargeResidualHeight)
    (bs : List (Sun28.Compiler.Branch 28)) (decode : BranchesDecode c Γ D Uo Us bs)
    (complete : ∀ k : ℤ, Sun28.Compiler.branchRelation bs (k:ℚ)) (x : ℚ) :
    (∃ y : Fin 28 → ℚ, Sun28.eval28 (Sun28.Branches.polynomial28 (Sun28.Compiler.branchAtlas bs)) x y=0) ↔
      ∃ k : ℤ, x=(k:ℚ) :=
  compiled_projection_of_decoding cn gn chart ((original_five_from_units published).2 remaining)
    bs decode complete x

theorem integerDefinition28_of_large_residual {c Γ D Uo Us} (cn : c≠0) (gn : Γ≠0)
    (chart : OrdinaryCharts (commonCutoff c Γ Uo Us) K0)
    (published : PublishedCorollary72) (remaining : LargeResidualHeight)
    (bs : List (Sun28.Compiler.Branch 28)) (branches : ExactBranchList c Γ D Uo Us bs)
    (complete : IntegerWitnesses c Γ D Uo Us) : Sun28.IntegerDefinition28 :=
  ⟨_,compiled_projection_of_large_residual cn gn chart published remaining bs branches complete⟩

end
end Sun28.Forward
#print axioms Sun28.Forward.compiled_projection_of_large_residual
#print axioms Sun28.Forward.integerDefinition28_of_large_residual

#print axioms Sun28.Forward.guarded_projection_of_large_residual
