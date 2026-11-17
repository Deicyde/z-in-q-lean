import ClusterParameters
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-! The rational invariant in homogeneous primitive coordinates. -/
namespace ZInQBlueprint.ContactInvariant
open ResidualFactors
noncomputable section

theorem J_homogeneous {A B : ℚ} (hB : B ≠ 0) :
    SixContact.J (A/B) = -57600*(contactProduct A B)^2/(poleForm A B)^6 := by
  obtain ⟨hf,hg⟩ := ClusterParameters.homogenize A B hB
  rw [← hf,← hg,SixContact.J]
  field_simp [hB,(SixContact.positive_denominator _).ne']

private theorem F_nonzero {A B : ℤ} (hB : B ≠ 0) (hu : (A:ℚ)/B ∉ ZInQ.contactSet) :
    contactProduct (A:ℚ) (B:ℚ) ≠ 0 := by
  have hB' : (B:ℚ) ≠ 0 := by exact_mod_cast hB
  have hf : SixContact.F ((A:ℚ)/B) ≠ 0 := by
    intro hz
    have h0 : SixContact.J ((A:ℚ)/B)=0 := by simp [SixContact.J,hz]
    exact (CoarseConic.unmarked_range hu).2.ne h0
  rw [← (ClusterParameters.homogenize (A:ℚ) (B:ℚ) hB').1]
  exact mul_ne_zero hf (pow_ne_zero _ hB')

variable {p : ℕ} [hprime : Fact p.Prime]

private theorem scalar_unit (hp : 5<p) {n k : ℕ} (hn : n ∣ 120^k) :
    padicValRat p (n:ℚ)=0 := by
  have h0 : ¬p ∣ n := by
    intro h
    have h120 := hprime.out.dvd_of_dvd_pow (h.trans hn)
    have hfac : p ∣ Nat.factorial 5 := by simpa only [show Nat.factorial 5=120 by decide] using h120
    exact (not_le_of_gt hp) ((Nat.Prime.dvd_factorial hprime.out).mp hfac)
  simp [padicValNat.eq_zero_of_not_dvd h0]

theorem invariant_coefficient_unit (hp : 5 < p) : padicValRat p (3779136:ℚ) = 0 :=
  scalar_unit (n:=3779136) (k:=10) hp (by decide)

/-- The exact additive valuation, before distinguishing contact and pole. -/
theorem J_valuation {A B : ℤ} (hB : B ≠ 0) (hu : (A:ℚ)/B ∉ ZInQ.contactSet) (hp : 5 < p) :
    padicValRat p (SixContact.J ((A:ℚ)/B)) =
      2*padicValRat p (contactProduct A B:ℤ) - 6*padicValRat p (poleForm A B:ℤ) := by
  have hB' : (B:ℚ) ≠ 0 := by exact_mod_cast hB
  have hf := F_nonzero hB hu
  have hg : poleForm (A:ℚ) (B:ℚ) ≠ 0 := by
    rw [← (ClusterParameters.homogenize (A:ℚ) (B:ℚ) hB').2]
    exact mul_ne_zero (SixContact.positive_denominator _).ne' (pow_ne_zero _ hB')
  have h57600 : padicValRat p (57600:ℚ)=0 := scalar_unit (n:=57600) (k:=3) hp (by decide)
  have hfcast : ((contactProduct A B:ℤ):ℚ) = contactProduct (A:ℚ) (B:ℚ) := by simp [contactProduct]
  have hgcast : ((poleForm A B:ℤ):ℚ) = poleForm (A:ℚ) (B:ℚ) := by simp [poleForm]
  rw [J_homogeneous hB',padicValRat.div (mul_ne_zero (by norm_num) (pow_ne_zero _ hf)) (pow_ne_zero _ hg),
    padicValRat.mul (by norm_num) (pow_ne_zero _ hf),padicValRat.neg,h57600,
    padicValRat.pow,padicValRat.pow,hfcast,hgcast]
  norm_num

private theorem reduced_zero {z : ℤ} (h : 0 < padicValRat p z) : (z : ZMod p) = 0 := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr
  by_contra hn
  simp [padicValInt.eq_zero_of_not_dvd hn] at h

private theorem reduced_unit {z : ℤ} (h : (z : ZMod p) ≠ 0) : padicValRat p z = 0 := by
  have hn : ¬(p:ℤ) ∣ z := fun hh => h ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hh)
  simp [padicValInt.eq_zero_of_not_dvd hn]

/-- In a primitive pair a positive valuation of either homogeneous form forces the other to be a unit. -/
theorem disjoint_valuations {A B : ℤ} (hprim : IsCoprime A B) (hp : 5<p) :
    (0 < padicValRat p (contactProduct A B:ℤ) → padicValRat p (poleForm A B:ℤ)=0) ∧
    (0 < padicValRat p (poleForm A B:ℤ) → padicValRat p (contactProduct A B:ℤ)=0) := by
  have cn (n:ℕ) (hn : 0<n) (h : n<p) : (n : ZMod p) ≠ 0 := by
    rw [Ne,CharP.cast_eq_zero_iff (ZMod p) p]
    exact Nat.not_dvd_of_pos_of_lt hn h
  let : NeZero (2:ZMod p) := ⟨cn 2 (by decide) (by omega)⟩
  let : NeZero (3:ZMod p) := ⟨cn 3 (by decide) (by omega)⟩
  let : NeZero (5:ZMod p) := ⟨cn 5 (by decide) hp⟩
  obtain ⟨a,b,he⟩ := hprim.map (Int.castRingHom (ZMod p))
  have hab : (A:ZMod p) ≠ 0 ∨ (B:ZMod p) ≠ 0 := by
    by_contra! hn
    simp [hn.1,hn.2] at he
  have hsep : ((contactProduct A B:ℤ):ZMod p)=0 → ((poleForm A B:ℤ):ZMod p) ≠ 0 := by
    simpa [contactProduct,poleForm] using ClusterParameters.separate_marks hab
  exact ⟨fun h => reduced_unit (hsep (reduced_zero h)),
    fun h => reduced_unit (fun hf => hsep hf (reduced_zero h))⟩

theorem primitive_orders {A B : ℤ} (hB : B ≠ 0) (hprim : IsCoprime A B)
    (hu : (A:ℚ)/B ∉ ZInQ.contactSet) (hp : 5 < p) :
    (∀ d : ℤ, 0<d → padicValRat p (contactProduct A B:ℤ)=2*d →
      padicValRat p (SixContact.J ((A:ℚ)/B))=4*d) ∧
    (∀ g : ℤ, 0<g → padicValRat p (poleForm A B:ℤ)=g →
      padicValRat p (SixContact.J ((A:ℚ)/B))= -6*g) := by
  obtain ⟨hf,hg⟩ := disjoint_valuations hprim hp
  rw [J_valuation hB hu hp]
  constructor
  · intro d hd hv
    rw [hf (by omega), hv]
    ring
  · intro g hpos hv
    rw [hg (by omega), hv]
    ring

/-- Direct specialization to the canonical reduced numerator and denominator of u. -/
theorem rational_orders (u : ℚ) (hu : u ∉ ZInQ.contactSet) (hp : 5 < p) :
    (∀ d : ℤ, 0<d → padicValRat p (contactProduct u.num (u.den:ℤ):ℤ)=2*d →
      padicValRat p (SixContact.J u)=4*d) ∧
    (∀ g : ℤ, 0<g → padicValRat p (poleForm u.num (u.den:ℤ):ℤ)=g →
      padicValRat p (SixContact.J u)= -6*g) := by
  have hb : (u.den:ℤ) ≠ 0 := by exact_mod_cast u.den_nz
  have hpq : (u.num:ℚ)/(↑(u.den:ℤ):ℚ)=u := by exact_mod_cast Rat.num_div_den u
  have hc : IsCoprime u.num (u.den:ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using u.reduced)
  have huq : (u.num:ℚ)/(↑(u.den:ℤ):ℚ) ∉ ZInQ.contactSet := hpq.symm ▸ hu
  simpa only [hpq] using primitive_orders hb hc huq hp

theorem J_valuation_rational (u : ℚ) (hu : u ∉ ZInQ.contactSet) (hp : 5 < p) :
    padicValRat p (SixContact.J u) = 2*padicValRat p (contactProduct u.num (u.den:ℤ):ℤ)
      - 6*padicValRat p (poleForm u.num (u.den:ℤ):ℤ) := by
  have hb : (u.den:ℤ) ≠ 0 := by exact_mod_cast u.den_nz
  have hpq : (u.num:ℚ)/(↑(u.den:ℤ):ℚ)=u := by exact_mod_cast Rat.num_div_den u
  have huq : (u.num:ℚ)/(↑(u.den:ℤ):ℚ) ∉ ZInQ.contactSet := hpq.symm ▸ hu
  simpa only [hpq] using J_valuation hb huq hp

end
end ZInQBlueprint.ContactInvariant
#print axioms ZInQBlueprint.ContactInvariant.J_homogeneous
#print axioms ZInQBlueprint.ContactInvariant.invariant_coefficient_unit
#print axioms ZInQBlueprint.ContactInvariant.J_valuation
#print axioms ZInQBlueprint.ContactInvariant.disjoint_valuations
#print axioms ZInQBlueprint.ContactInvariant.primitive_orders
#print axioms ZInQBlueprint.ContactInvariant.rational_orders
#print axioms ZInQBlueprint.ContactInvariant.J_valuation_rational
