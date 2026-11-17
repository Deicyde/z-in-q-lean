import FibreInertia
import ContactMultiplicity
import Mathlib.GroupTheory.OrderOfElement

open scoped NumberField
open ZInQBlueprint.SixContact ZInQBlueprint.ContactMultiplicity

namespace ZInQBlueprint.ContactRamification

variable {A Γ : Type*} [Group A] [Group Γ]

/-- The specialization and the generic cover can have different Galois groups. The image
of inertia under the specialization embedding is conjugate to the indicated subgroup. -/
def ConjugatePower (I : Subgroup A) (ι : A →* Γ) (s : Γ) (m : ℤ) : Prop :=
  ∃ g : Γ, (I.map ι).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (s ^ m)

theorem order_of_conjugate_power {I : Subgroup A} {ι : A →* Γ} (hi : Function.Injective ι)
    {s : Γ} {m : ℤ} (h : ConjugatePower I ι s m) : Nat.card I = orderOf (s ^ m) := by
  obtain ⟨g, hg⟩ := h
  calc
    Nat.card I = Nat.card (I.map ι) := Nat.card_congr (I.equivMapOfInjective ι hi).toEquiv
    _ = Nat.card ((I.map ι).map (MulAut.conj g).toMonoidHom) :=
      Nat.card_congr ((I.map ι).equivMapOfInjective _ (MulAut.conj g).injective).toEquiv
    _ = Nat.card (Subgroup.zpowers (s ^ m)) := by rw [hg]
    _ = orderOf (s ^ m) := Nat.card_zpowers _

private theorem card_one_iff {I : Subgroup A} {ι : A →* Γ} (hi : Function.Injective ι)
    {s : Γ} {e : ℕ} (he : orderOf s = e) {m : ℤ} (h : ConjugatePower I ι s m) :
    Nat.card I = 1 ↔ (e : ℤ) ∣ m := by
  rw [order_of_conjugate_power hi h, orderOf_eq_one_iff, ← orderOf_dvd_iff_zpow_eq_one, he]

/-- The conclusion needed from tame specialization at a single prime of the literal
fibre field. Heights, contact support and ramification indices do not occur in the hypotheses. -/
structure TameFibre (I : Subgroup A) (ι : A →* Γ) (s₀ sPole s₃ : Γ) (p : ℕ) (u : ℚ) : Prop where
  injective : Function.Injective ι
  zeroOrder : orderOf s₀ = 4
  poleOrder : orderOf sPole = 6
  thirdOrder : orderOf s₃ = 2
  zero : 0 < padicValRat p (J u) → ConjugatePower I ι s₀ (padicValRat p (J u))
  pole : padicValRat p (J u) < 0 → ConjugatePower I ι sPole (-padicValRat p (J u))
  third : 0 < padicValRat p (J u + 16/27) → ConjugatePower I ι s₃ (padicValRat p (J u + 16/27))
  away : padicValRat p (J u) = 0 → padicValRat p (J u + 16/27) ≤ 0 → I.map ι = ⊥

theorem unramified_order_iff {I : Subgroup A} {ι : A →* Γ} {s₀ sPole s₃ : Γ} {p : ℕ} {u : ℚ}
    (h : TameFibre I ι s₀ sPole s₃ p u) : Nat.card I = 1 ↔ ¬ badBranch p u := by
  constructor
  · intro hc
    rintro (⟨hz, hn⟩ | ⟨hp, hn⟩ | ⟨ht, hn⟩)
    · exact hn ((card_one_iff h.injective h.zeroOrder (h.zero hz)).mp hc)
    · exact hn ((card_one_iff h.injective h.poleOrder (h.pole hp)).mp hc)
    · exact hn ((card_one_iff h.injective h.thirdOrder (h.third ht)).mp hc)
  · intro hn
    by_cases hz : 0 < padicValRat p (J u)
    · apply (card_one_iff h.injective h.zeroOrder (h.zero hz)).mpr
      by_contra hbad
      exact hn (.inl ⟨hz,hbad⟩)
    by_cases hp : padicValRat p (J u) < 0
    · apply (card_one_iff h.injective h.poleOrder (h.pole hp)).mpr
      by_contra hbad
      exact hn (.inr (.inl ⟨hp,hbad⟩))
    by_cases ht : 0 < padicValRat p (J u + 16/27)
    · apply (card_one_iff h.injective h.thirdOrder (h.third ht)).mpr
      by_contra hbad
      exact hn (.inr (.inr ⟨ht,hbad⟩))
    have he := h.away (by omega) (by omega)
    rw [(I.map_eq_bot_iff_of_injective h.injective).mp he]
    simp

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

local instance prime_span (p : ℕ) [Fact p.Prime] : (Ideal.span {(p : ℤ)}).IsPrime := by
  have hprime : p.Prime := Fact.out
  apply (Ideal.span_singleton_prime (by exact_mod_cast hprime.ne_zero)).mpr
  simpa [Int.prime_iff_natAbs_prime] using hprime

theorem unramified_iff_not_contact {p : ℕ} [Fact p.Prime] (hp : 17 ≤ p)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) (S : Finset ℕ) (hS : p ∉ S)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    {ι : Gal(K/ℚ) →* Γ} {s₀ sPole s₃ : Γ}
    (h : TameFibre (FibreInertia.inertia K P) ι s₀ sPole s₃ p u) :
    Algebra.IsUnramifiedAt ℤ P ↔ ¬ p ∣ ZInQ.contactSupport S u := by
  rw [FibreInertia.unramified_iff_card K (Ideal.span {(p : ℤ)}) P, unramified_order_iff h,
    branch_iff_dvd_contactSupport hp hu S hS]

/-- At an odd contact the order is exactly two, since the valuation of J is even
and the zero-branch generator has order four. -/
theorem ramification_index_at_contact {p : ℕ} [Fact p.Prime] (hp : 17 ≤ p)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) (S : Finset ℕ) (hS : p ∉ S)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    {ι : Gal(K/ℚ) →* Γ} {s₀ sPole s₃ : Γ}
    (h : TameFibre (FibreInertia.inertia K P) ι s₀ sPole s₃ p u)
    (hc : p ∣ ZInQ.contactSupport S u) : P.ramificationIdx ℤ = 2 := by
  have hbad := (branch_iff_dvd_contactSupport hp hu S hS).mpr hc
  have hz : 0 < padicValRat p (J u) ∧ ¬ (4 : ℤ) ∣ padicValRat p (J u) := by
    rcases hbad with hz | ⟨hv,hd⟩ | ⟨_,hd⟩
    · exact hz
    · exact (hd (pole_multiple hp hu hv)).elim
    · exact (hd (third_even hp u)).elim
  rw [← FibreInertia.card_inertia K (Ideal.span {(p : ℤ)}) P, order_of_conjugate_power h.injective (h.zero hz.1)]
  apply orderOf_eq_prime
  · rw [← zpow_natCast, ← zpow_mul]
    apply orderOf_dvd_iff_zpow_eq_one.mp
    rw [h.zeroOrder]
    obtain ⟨k,he⟩ := zero_even (p := p) u
    exact ⟨k,by push_cast; omega⟩
  · intro he
    apply hz.2
    simpa only [h.zeroOrder, Nat.cast_ofNat] using (orderOf_dvd_iff_zpow_eq_one.mpr he)

/-- The arithmetic statement used in PR(i), with all primes of the number field
above p quantified in the standard definition of unramifiedness. -/
theorem unramified_in_of_not_contact {p : ℕ} [Fact p.Prime] (hp : 17 ≤ p)
    {u : ℚ} (hu : u ∉ ZInQ.contactSet) (S : Finset ℕ) (hS : p ∉ S)
    {ι : Gal(K/ℚ) →* Γ} {s₀ sPole s₃ : Γ}
    (tame : ∀ (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})],
      TameFibre (FibreInertia.inertia K P) ι s₀ sPole s₃ p u)
    (hc : ¬ p ∣ ZInQ.contactSupport S u) : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  intro P hP hOver
  have := hP
  have := hOver
  exact (unramified_iff_not_contact K hp hu S hS P (tame P)).mpr hc

end ZInQBlueprint.ContactRamification

#print axioms ZInQBlueprint.ContactRamification.order_of_conjugate_power
#print axioms ZInQBlueprint.ContactRamification.unramified_order_iff
#print axioms ZInQBlueprint.ContactRamification.unramified_iff_not_contact

#print axioms ZInQBlueprint.ContactRamification.ramification_index_at_contact

#print axioms ZInQBlueprint.ContactRamification.unramified_in_of_not_contact
