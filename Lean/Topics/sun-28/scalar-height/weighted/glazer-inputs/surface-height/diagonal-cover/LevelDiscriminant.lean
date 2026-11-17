import CoarseDiscriminant

namespace ZInQBlueprint.Diagonal210
open NumberField Sun28.Ordinary
open scoped NumberField
noncomputable section

/-- A finite étale level covering supplies the relative assertion at each
prime of its number field. Multiplicativity of ramification indices then
transfers the coarse support bound to that field. -/
theorem level_discriminant_support {A B : ℤ} (cop : Int.gcd A B=1)
    (hn : ∀ i,oldForm i A B≠0) (y : Fibre ℂ coefficient ((A:ℚ)/B))
    (L : Type*) [Field L] [NumberField L] [Algebra (rootField y) L]
    [IsScalarTower ℚ (rootField y) L] {p : ℕ} [hp : Fact p.Prime]
    (large : 7<p) (S : Finset ℕ) (out : p∉S)
    (level : ∀ (P : Ideal (𝓞 L)) [P.IsPrime], (p:𝓞 L)∈P → Algebra.IsUnramifiedAt (𝓞 (rootField y)) P) :
    (p:ℤ)∣NumberField.discr L → p∈oldContactPrimes S A B := by
  contrapose!
  intro away
  let K := rootField y
  have un : ¬(p:ℤ)∣NumberField.discr K := fun d=>away ((discriminant_iff_contact large cop hn y S out).mp d)
  have prime := Nat.prime_iff_prime_int.mp hp.out
  apply (NumberField.not_dvd_discr_iff_forall_mem L (𝓞 L) prime).mpr
  intro P hpP mem
  let Q := P.under (𝓞 K)
  have inQ : (p:𝓞 K)∈Q := by
    change algebraMap (𝓞 K) (𝓞 L) (p:𝓞 K) ∈ P
    simpa using mem
  have base := (NumberField.not_dvd_discr_iff_forall_mem K (𝓞 K) prime).mp un Q inferInstance inQ
  have fine := level P (by simpa using mem)
  apply Ideal.ramificationIdx_eq_one_iff.mp
  rw [Ideal.ramificationIdx_tower (R:=ℤ) Q P,Ideal.ramificationIdx_eq_one_iff.mpr base,
    Ideal.ramificationIdx_eq_one_iff.mpr fine,one_mul]

end
end ZInQBlueprint.Diagonal210
#print axioms ZInQBlueprint.Diagonal210.level_discriminant_support
