import OriginalThetaParity
import BranchRows

/-! The characteristics of the ten finite pairs in Eilers (4.2)–(4.4). -/
namespace ZInQBlueprint.SixMetric
open OriginalTheta ThetaPeriod ThetaQuotient BranchFormula ZInQ.LeafPush2

/-- Entries are written in the order ε₁′, ε₂′, ε₁, ε₂ of Eilers (1.2). -/
def chars (a₁ a₂ b₁ b₂ : Fin 2) : Char2 := (![a₁,a₂],![b₁,b₂])

/-- The fifth entry is finite. The sixth, the base point at infinity, has zero half-period. -/
def halfPeriod : Fin 6 → Char2 :=
  ![chars 1 0 0 0,chars 1 0 1 0,chars 0 1 1 0,chars 0 1 1 1,chars 0 0 1 1,chars 0 0 0 0]

def riemannConstant : Char2 := chars 1 1 0 1

/-- The row selects the *two* finite branch indices in Eilers (2.14). -/
def pairChar (i : Fin 10) : Char2 :=
  halfPeriod (row i).p.castSucc + halfPeriod (row i).q.castSucc - riemannConstant

/-- Eilers's ten pairs, in lexicographic order, as positions in the increasing even list. -/
def evenPosition : Fin 10 ≃ Fin 10 where
  toFun := ![9,3,1,7,2,0,6,8,4,5]
  invFun := ![5,2,4,1,8,9,6,3,7,0]
  left_inv := by decide
  right_inv := by decide

theorem riemannConstant_eq :
    riemannConstant = halfPeriod 1 + halfPeriod 3 ∧
    riemannConstant = halfPeriod 0 + halfPeriod 2 + halfPeriod 4 := by decide

theorem pairChar_eq (i : Fin 10) : pairChar i = characteristic (evenIndices (evenPosition i)) := by
  fin_cases i <;> decide

theorem pairChar_indices : (fun i => number (pairChar i)) =
    ![(15:Fin 16),3,1,9,2,0,8,12,4,6] := by
  funext i
  fin_cases i <;> rfl

/-- Distinct pairs give distinct characteristics. -/
theorem pairChar_injective : Function.Injective pairChar := by
  intro i j h
  rw [pairChar_eq,pairChar_eq] at h
  exact evenPosition.injective (evenIndices_injective (characteristicEquiv.injective h))

/-- Every even characteristic occurs; the pivot is the pair (2,4). -/
theorem even_unique (m : Char2) : dotParity m=0 ↔ ∃! i, pairChar i=m := by
  obtain ⟨j,rfl⟩ := characteristicEquiv.surjective m
  change dotParity (characteristic j)=0 ↔ _
  constructor
  · intro h
    have he : ∃ i, evenIndices i=j := by
      by_contra h'
      have h₁ := (odd_iff j).mpr h'
      rw [h] at h₁
      exact Fin.zero_ne_one h₁
    obtain ⟨k,rfl⟩ := he
    have hw : pairChar (evenPosition.symm k)=characteristicEquiv (evenIndices k) := by
      rw [pairChar_eq,evenPosition.apply_symm_apply]; rfl
    refine ⟨evenPosition.symm k,hw,?_⟩
    intro i hi
    exact pairChar_injective (hi.trans hw.symm)
  · rintro ⟨i,hi,_⟩
    have hij : characteristicEquiv (evenIndices (evenPosition i))=characteristicEquiv j := (pairChar_eq i).symm.trans hi
    have ij := characteristicEquiv.injective hij
    by_contra hn
    have ho : dotParity (characteristic j)=1 := by omega
    exact ((odd_iff j).mp ho) ⟨_,ij⟩

noncomputable def eilersLabel : Fin 10 ≃ Partition := evenPosition.symm.trans pairs

end ZInQBlueprint.SixMetric
#print axioms ZInQBlueprint.SixMetric.riemannConstant_eq
#print axioms ZInQBlueprint.SixMetric.pairChar_eq
#print axioms ZInQBlueprint.SixMetric.pairChar_indices
#print axioms ZInQBlueprint.SixMetric.pairChar_injective
#print axioms ZInQBlueprint.SixMetric.even_unique
