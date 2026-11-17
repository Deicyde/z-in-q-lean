import Mathlib

/-! Full two-torsion fixes sextic roots once nonzero torsion labels unordered pairs. -/
namespace ZInQBlueprint.PeriodGaussian
open Set
universe u v

/-- A map fixing each unordered pair fixes each vertex, as soon as each vertex has two
different neighbors. Injectivity of the map itself is unnecessary. -/
theorem fixes_vertices_of_fixes_pairs {V : Type u} (f : V → V)
    (neighbors : ∀ x : V, ∃ y z : V, x ≠ y ∧ x ≠ z ∧ y ≠ z)
    (pairs : ∀ x y : V, x ≠ y → ({f x, f y} : Set V) = {x,y}) :
    ∀ x, f x = x := by
  intro x
  obtain ⟨y,z,hxy,hxz,hyz⟩ := neighbors x
  have mem (v : V) (hv : x ≠ v) : f x = x ∨ f x = v := by
    have triv : f x ∈ ({f x, f v} : Set V) := by simp
    rwa [pairs x v hv,Set.mem_insert_iff,Set.mem_singleton_iff] at triv
  rcases mem y hxy with H|H
  · exact H
  rcases mem z hxz with h|h
  · exact h
  · exact (hyz (H.symm.trans h)).elim

/-- Applying the Galois-equivariant bijection of Flynn--Testa--van Luijk, §2, needs
only the local equality of the two torsion labels for a nontrivial edge. -/
theorem fixes_six_of_torsion {T : Type v} (f : Equiv.Perm (Fin 6))
    (label : Fin 6 → Fin 6 → T)
    (identifies : ∀ a b c d, a ≠ b → c ≠ d → label a b = label c d →
      ({a,b} : Set (Fin 6)) = {c,d})
    (fixed : ∀ a b, a ≠ b → label (f a) (f b) = label a b) : f = 1 := by
  apply Equiv.ext
  intro a
  change f a = a
  apply fixes_vertices_of_fixes_pairs (f := f)
  · intro i
    fin_cases i <;> first
      | exact ⟨1,2,by decide,by decide,by decide⟩
      | exact ⟨0,2,by decide,by decide,by decide⟩
      | exact ⟨0,1,by decide,by decide,by decide⟩
  · intro i j hij
    exact identifies _ _ _ _ (f.injective.ne hij) hij (fixed i j hij)

end ZInQBlueprint.PeriodGaussian
#print axioms ZInQBlueprint.PeriodGaussian.fixes_vertices_of_fixes_pairs
#print axioms ZInQBlueprint.PeriodGaussian.fixes_six_of_torsion
