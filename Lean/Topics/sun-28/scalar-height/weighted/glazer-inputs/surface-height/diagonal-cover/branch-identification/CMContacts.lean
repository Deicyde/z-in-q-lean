import CoarseDiscriminant

namespace ZInQBlueprint.BranchId
open NumberField Sun28.Ordinary Diagonal210
open scoped NumberField
noncomputable section

/-- Discriminants in a tower with unramified top step have the same prime support. -/
theorem unramified_discriminants {K H : Type*} [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsScalarTower ℚ K H] (un : ∀ (P : Ideal (𝓞 H)) [P.IsPrime],
      Algebra.IsUnramifiedAt (𝓞 K) P) {p : ℕ} (hp : p.Prime) :
    (p:ℤ)∣NumberField.discr H ↔ (p:ℤ)∣NumberField.discr K := by
  constructor
  · contrapose!
    intro hn
    have prime:=Nat.prime_iff_prime_int.mp hp
    apply (NumberField.not_dvd_discr_iff_forall_mem H (𝓞 H) prime).mpr
    intro P hP mem
    let Q:=P.under (𝓞 K)
    have inQ : (p:𝓞 K)∈Q := by
      change algebraMap (𝓞 K) (𝓞 H) (p:𝓞 K)∈P
      simpa using mem
    have base := (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) prime).mp hn Q inferInstance (by simpa using inQ)
    apply Ideal.ramificationIdx_eq_one_iff.mp
    rw [Ideal.ramificationIdx_tower (R:=ℤ) Q P,Ideal.ramificationIdx_eq_one_iff.mpr base,
      Ideal.ramificationIdx_eq_one_iff.mpr (un P),one_mul]
  · exact fun h=>dvd_trans h (NumberField.discr_dvd_discr K H)

/-- A coarse point contained in an everywhere unramified extension of a possible
CM field has no odd contact above the original paper cutoff. -/
theorem no_large_contact_in_cm_field {A B : ℤ} (cop : Int.gcd A B=1)
    (hn : ∀ i,oldForm i A B≠0) (y : Fibre ℂ coefficient ((A:ℚ)/B))
    (K H : Type*) [Field K] [NumberField K] [Field H] [NumberField H]
    [Algebra K H] [IsScalarTower ℚ K H]
    [Algebra (rootField y) H] [IsScalarTower ℚ (rootField y) H]
    (bound : (NumberField.discr K).natAbs ≤ 5460)
    (un : ∀ (P : Ideal (𝓞 H)) [P.IsPrime],Algebra.IsUnramifiedAt (𝓞 K) P) :
    oldContactPrimes oldCutoff A B=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hit
  have contact:=mem_oldContactPrimes.mp hit
  let : Fact p.Prime:=⟨contact.1⟩
  have far : 76176<p := by
    by_contra! h
    apply contact.2.1
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),contact.1⟩
  have coarse:=(discriminant_iff_contact (by omega : 7<p) cop hn y oldCutoff contact.2.1).mpr hit
  have dk := (unramified_discriminants un contact.1).mp
    (dvd_trans coarse (NumberField.discr_dvd_discr (rootField y) H))
  have small : p≤(NumberField.discr K).natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr (NumberField.discr_ne_zero K)) (by simpa using Int.natAbs_dvd_natAbs.mpr dk)
  omega

end
end ZInQBlueprint.BranchId
#print axioms ZInQBlueprint.BranchId.unramified_discriminants
#print axioms ZInQBlueprint.BranchId.no_large_contact_in_cm_field
