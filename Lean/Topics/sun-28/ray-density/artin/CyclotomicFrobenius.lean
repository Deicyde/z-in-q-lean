import CyclotomicCharacter
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Frobenius

namespace Sun28.RayDensity.Artin
open IsCyclotomicExtension IsCyclotomicExtension.Rat NumberField

/-- The exponent of an arithmetic Frobenius in the canonical cyclotomic
Galois isomorphism, computed for each maximal integral ideal above p. -/
theorem galois_frobenius {n p:ℕ} [NeZero n] [Fact p.Prime]
    (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (Q:Ideal (𝓞 K)) [Q.IsMaximal] [overP:Q.LiesOver (Ideal.span {(p:ℤ)})]
    (cop:p.Coprime n) {σ:Gal(K/ℚ)} (fr:IsArithFrobAt ℤ σ Q) :
    galEquivZMod n K σ = ZMod.unitOfCoprime p cop := by
  have underQ : Q.under ℤ=Ideal.span {(p:ℤ)} := overP.over.symm
  have away : (n:𝓞 K)∉Q := by
    intro h
    have b : (n:ℤ)∈Q.under ℤ := by
      change algebraMap ℤ (𝓞 K) (n:ℤ) ∈ Q
      simpa using h
    rw [underQ,Ideal.mem_span_singleton] at b
    exact ((Fact.out:p.Prime).coprime_iff_not_dvd.mp cop) (by exact_mod_cast b)
  have root:= (zeta_spec n ℚ K).toInteger_isPrimitiveRoot
  have e := fr.apply_of_pow_eq_one root.pow_eq_one away
  change σ • (zeta_spec n ℚ K).toInteger = _ at e
  rw [underQ,Int.card_ideal_quot,galEquivZMod_smul_of_pow_eq n K σ root.pow_eq_one] at e
  apply Units.ext
  rw [ZMod.coe_unitOfCoprime]
  have z := (root.isOfFinOrder (NeZero.ne n)).pow_inj_mod.mp e
  rw [←root.eq_orderOf] at z
  simpa [ZMod.val_natCast] using (ZMod.natCast_eq_natCast_iff' _ _ _).2 z

theorem explicit_frobenius {n p:ℕ} [NeZero n] [Fact p.Prime]
    (K:Type*) [Field K] [NumberField K] [IsCyclotomicExtension {n} ℚ K]
    (Q:Ideal (𝓞 K)) [Q.IsMaximal] [Q.LiesOver (Ideal.span {(p:ℤ)})]
    (cop:p.Coprime n) :
    ∃ σ : Gal(K/ℚ), IsArithFrobAt ℤ σ Q ∧ galEquivZMod n K σ = ZMod.unitOfCoprime p cop := by
  have : IsGalois ℚ K:=IsCyclotomicExtension.isGalois {n} ℚ K
  obtain ⟨σ,h⟩:=IsArithFrobAt.exists_of_isInvariant ℤ (Gal(K/ℚ)) Q
  exact ⟨σ,h,galois_frobenius K Q cop h⟩

end Sun28.RayDensity.Artin
#print axioms Sun28.RayDensity.Artin.galois_frobenius
#print axioms Sun28.RayDensity.Artin.explicit_frobenius
