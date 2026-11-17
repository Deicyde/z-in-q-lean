import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Operations

namespace EllipticHeight

universe u v

/-- A zero of the selected abscissa represents a nonzero two-torsion class.
An odd-indexed pole kills the base point. These local implications, only at
maximal ideals containing both coordinates, give the global Bézout identity.
The row's own denominator is included and its label may be even. -/
theorem numerator_coprime_denominators {R : Type u} [CommRing R]
    (A r d : R) (B : Fin 4 → R) (n : Fin 4 → ℤ) (i : Fin 4)
    (atTwo : IsCoprime A r) (atSeven : IsCoprime A d)
    (odd : ∀ j, j ≠ i → n j % 2 = 1)
    (reduction : ∀ (M : Ideal R) (j : Fin 4), M.IsMaximal → r ∉ M → d ∉ M →
      A ∈ M → B j ∈ M →
        ∃ (G : AddGrpCat.{v}) (P T : G),
          T ≠ 0 ∧ (2 : ℤ) • T = 0 ∧ n i • P = T ∧ n j • P = 0) :
    IsCoprime A (∏ j, B j) := by
  apply IsCoprime.prod_right
  intro j _
  by_contra common
  have proper : Ideal.span ({A, B j} : Set R) ≠ ⊤ := by
    intro top
    exact common (Ideal.mem_span_pair.mp ((Ideal.eq_top_iff_one _).mp top))
  obtain ⟨M, maximal, contains⟩ := Ideal.exists_le_maximal _ proper
  letI : M.IsPrime := maximal.isPrime
  have hA : A ∈ M := contains (Ideal.subset_span (by simp))
  have hB : B j ∈ M := contains (Ideal.subset_span (by simp))
  have hr := Ideal.IsPrime.notMem_of_isCoprime_of_mem atTwo hA
  have hd := Ideal.IsPrime.notMem_of_isCoprime_of_mem atSeven hA
  obtain ⟨G, P, T, nonzero, two, zeroClass, poleClass⟩ := reduction M j maximal hr hd hA hB
  apply nonzero
  by_cases same : j = i
  · subst j
    exact zeroClass.symm.trans poleClass
  have killed : n j • T = 0 := by
    rw [← zeroClass, ← mul_zsmul, mul_comm (n j) (n i), mul_zsmul, poleClass, zsmul_zero]
  have parity := odd j same
  have decomp : n j = (n j / 2)*2+1 := by omega
  rw [decomp, add_zsmul, mul_zsmul, two] at killed
  simpa using killed

#print axioms numerator_coprime_denominators

end EllipticHeight
