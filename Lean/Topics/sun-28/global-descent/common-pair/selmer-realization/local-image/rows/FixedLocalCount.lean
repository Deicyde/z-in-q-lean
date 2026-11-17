import FixedBound
import EightOrbit

namespace Sun28.FixedLocalRows
open Sun28.SelmerRealization
noncomputable section

/-- Equality for the set defined by the actual homogeneous covers over ℝ
and every p-adic field. The two inclusions are independent of rational rank. -/
theorem local_classes_eq_eight : localClasses n = (Sun28.LocalOrbit.eight : Set (ℤ×ℤ)) := by
  refine Set.Subset.antisymm ?_ Sun28.LocalOrbit.eight_subset
  rintro ⟨a,b⟩ h
  have mem := local_label_list h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with e|e|e|e|e|e|e|e <;> rw [e] <;> decide +kernel

theorem local_class_count : (localClasses n).ncard = 8 := by
  rw [local_classes_eq_eight,Set.ncard_coe_finset,Sun28.LocalOrbit.eight_card]

theorem fixed_descent : FiniteDescent n 526361 1 :=
  Sun28.MarkedDescent.finite_descent_iff_card.mpr local_class_count

end
end Sun28.FixedLocalRows
#print axioms Sun28.FixedLocalRows.local_classes_eq_eight
#print axioms Sun28.FixedLocalRows.local_class_count
#print axioms Sun28.FixedLocalRows.fixed_descent
