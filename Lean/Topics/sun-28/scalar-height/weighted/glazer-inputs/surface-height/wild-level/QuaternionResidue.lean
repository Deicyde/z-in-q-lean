import ProjectiveWildImage
import Mathlib.Tactic

namespace ZInQBlueprint.WildLevel
open Matrix
open scoped MatrixGroups
noncomputable section

/-- Restriction of reduction modulo the principal units of the local
quaternion division algebra to the finite projective wild image. -/
structure QuaternionResidue (P : Type*) [Group P] (ℓ : ℕ) where
  quotient : Type
  group : Group quotient
  cardinality : Nat.card quotient=2*(ℓ+1)
  reduction : P →* quotient
  principal : ∀ x, reduction x=1 → ∃ n : ℕ, x^(ℓ^n)=1

attribute [instance] QuaternionResidue.group

/-- Reduction embeds every finite p-group away from ℓ. No information
about the index of the tame inertia subgroup is needed. -/
theorem projective_divisibility {P : Type*} [Group P] {p ℓ : ℕ} (wild : IsPGroup p P)
    (different : Nat.Coprime p ℓ) (D : QuaternionResidue P ℓ) :
    Nat.card P ∣ 2*(ℓ+1) := by
  have ker : ∀ x, D.reduction x=1 → x=1 := by
    intro x hx
    obtain ⟨a,ha⟩ := wild x
    obtain ⟨b,hb⟩ := D.principal x hx
    have cp := (different.pow_left a).pow_right b
    exact orderOf_eq_one_iff.mp
      (Nat.eq_one_of_dvd_coprimes cp (orderOf_dvd_of_pow_eq_one ha) (orderOf_dvd_of_pow_eq_one hb))
  have inj := (injective_iff_map_eq_one _).mpr ker
  rw [←D.cardinality]
  exact Subgroup.card_dvd_of_injective D.reduction inj

/-- Use the ramified quaternion coefficient primes 5, 7 and 3 in
residue characteristics 2, 3 and greater than 3 respectively. -/
def auxiliary (p : ℕ) : ℕ := if p=2 then 5 else if p=3 then 7 else 3

theorem auxiliary_coprime {p : ℕ} (hp:p.Prime) : p.Coprime (auxiliary p) := by
  by_cases h:p=2
  · subst p; decide
  by_cases h':p=3
  · subst p; decide
  simpa [auxiliary,h,h'] using hp.coprime_iff_not_dvd.mpr (fun hd => h' ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hd))

theorem odd_quotient {p:ℕ} (hp:p.Prime) (odd:p≠2) : p.Coprime (2*(auxiliary p+1)) := by
  by_cases h:p=3
  · subst p; decide
  have cp := hp.coprime_iff_not_dvd.mpr (fun hd => odd ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hd))
  simpa [auxiliary,h,odd] using (show p.Coprime (2^3) from cp.pow_right 3)

/-- The finite representation and its local quaternion reduction at the
chosen coefficient prime, together with the determinant on wild inertia. -/
structure WildFibre (p : ℕ) where
  field : Type
  fieldInstance : Field field
  image : Subgroup (GL (Fin 2) field)
  finite : Finite image
  wild : IsPGroup p image
  quotient : QuaternionResidue (projectivize image).range (auxiliary p)
  determinant : ∀ x:image,x.val.det^(if p=2 then 2 else 1)=1
attribute [instance] WildFibre.fieldInstance WildFibre.finite

theorem wild_orders {p : ℕ} (hp:p.Prime) (F : WildFibre p) :
    if p=2 then Nat.card F.image≤16 else Nat.card F.image=1 := by
  have proj := F.wild.of_surjective (projectivize F.image).rangeRestrict (projectivize F.image).rangeRestrict_surjective
  have div:=projective_divisibility proj (auxiliary_coprime hp) F.quotient
  split
  next h =>
    subst p
    exact dyadic_image F.image F.wild div (by simpa using F.determinant)
  next neq =>
    let _ : Fact p.Prime:=⟨hp⟩
    have odd := hp.coprime_iff_not_dvd.mpr (fun hd => neq ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2)).mp hd))
    exact odd_image F.image F.wild odd (odd_quotient hp neq) div (by simpa [neq] using F.determinant)

end
end ZInQBlueprint.WildLevel
#print axioms ZInQBlueprint.WildLevel.projective_divisibility
#print axioms ZInQBlueprint.WildLevel.auxiliary_coprime
#print axioms ZInQBlueprint.WildLevel.odd_quotient
#print axioms ZInQBlueprint.WildLevel.wild_orders
