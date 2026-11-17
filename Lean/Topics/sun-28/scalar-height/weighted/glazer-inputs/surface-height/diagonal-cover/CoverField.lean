import DiagonalCover
import CMRingField

namespace ZInQBlueprint.Diagonal210
open IntermediateField Polynomial
noncomputable section

def rootField {s : ℚ} (y : Fibre ℂ coefficient s) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range y.1)

def generator {s : ℚ} (y : Fibre ℂ coefficient s) (i : Fin 4) : rootField y :=
  ⟨y.1 i, IntermediateField.subset_adjoin ℚ _ ⟨i,rfl⟩⟩

theorem generator_sq {s : ℚ} (y : Fibre ℂ coefficient s) (i : Fin 4) :
    generator y i ^ 2 = algebraMap ℚ (rootField y) (radicand s i) := by
  apply Subtype.ext
  exact y.2 i

theorem exists_fibre (s : ℚ) : Nonempty (Fibre ℂ coefficient s) := by
  choose y hy using fun i : Fin 4 => IsAlgClosed.exists_pow_nat_eq
    (algebraMap ℚ ℂ (radicand s i)) (n:=2) (by decide)
  exact ⟨⟨y,hy⟩⟩

theorem finite_rootField {s : ℚ} (y : Fibre ℂ coefficient s) : FiniteDimensional ℚ (rootField y) := by
  apply IntermediateField.finiteDimensional_adjoin
  rintro _ ⟨i,rfl⟩
  exact ⟨X^2-C (radicand s i),monic_X_pow_sub_C _ (by decide : (2:ℕ)≠0),by
    simp [radicand,y.2 i]⟩

/-- Choosing other square roots gives exactly the same subfield of the complex numbers. -/
theorem rootField_independent {s : ℚ} (y z : Fibre ℂ coefficient s) : rootField y = rootField z := by
  suffices h : ∀ a b : Fibre ℂ coefficient s,rootField a ≤ rootField b from le_antisymm (h y z) (h z y)
  intro a b
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i,rfl⟩
  have mem : b.1 i ∈ rootField b := (generator b i).property
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ((a.2 i).trans (b.2 i).symm) with e|e
  · rw [e]
    exact mem
  · rw [e]
    exact (rootField b).neg_mem mem

/-- Every embedding is determined by the signs it assigns to the four coordinates.
The argument includes fibres of smaller degree and vanishing coordinates. -/
theorem rootField_degree {s : ℚ} (y : Fibre ℂ coefficient s) : Module.finrank ℚ (rootField y) ≤ 16 := by
  classical
  let := finite_rootField y
  let sign (f : rootField y →ₐ[ℚ] ℂ) (i : Fin 4) : Bool := decide (f (generator y i)=y.1 i)
  have sign_inj : Function.Injective sign := by
    intro f g h
    apply IntermediateField.adjoin_algHom_ext
    rintro _ ⟨i,rfl⟩
    change f (generator y i)=g (generator y i)
    have same : (f (generator y i)=y.1 i) ↔ (g (generator y i)=y.1 i) :=
      by
        have e := congrFun h i
        change decide _ = decide _ at e
        simpa using e
    have choices (k : rootField y →ₐ[ℚ] ℂ) :
        k (generator y i)=y.1 i ∨ k (generator y i)= -y.1 i := by
      apply sq_eq_sq_iff_eq_or_eq_neg.mp
      rw [← map_pow,generator_sq,k.commutes,y.2 i]
      rfl
    rcases choices f with fpos|fneg
    · exact fpos.trans (same.mp fpos).symm
    · rcases choices g with gpos|gneg
      · exact (same.mpr gpos).trans gpos.symm
      · exact fneg.trans gneg.symm
  rw [← AlgHom.card ℚ (rootField y) ℂ]
  simpa using Fintype.card_le_of_injective sign sign_inj

/-- Actual coordinate fields supply the degree bound in the CM class-number argument. -/
theorem diagonal_class_number {s : ℚ} (y : Fibre ℂ coefficient s)
    (K : IntermediateField ℚ ℂ) {h : ℕ} (quadratic : Module.finrank ℚ K=2)
    (reciprocity : Module.finrank ℚ ↥(K ⊔ rootField y)=2*h) : h≤16 :=
  CMPeriods.ring_class_degree_le K (rootField y) quadratic reciprocity (rootField_degree y)

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.exists_fibre
#print axioms ZInQBlueprint.Diagonal210.finite_rootField
#print axioms ZInQBlueprint.Diagonal210.rootField_independent
#print axioms ZInQBlueprint.Diagonal210.rootField_degree
#print axioms ZInQBlueprint.Diagonal210.diagonal_class_number
