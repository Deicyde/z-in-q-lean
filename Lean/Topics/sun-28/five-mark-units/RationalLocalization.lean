import FiveMarkUnits
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Data.Nat.Factorization.Basic

/-! The exact unit group of Z[1/N_S] and its comparison with rational coordinates. -/
namespace Sun28.FiveMarkUnits
open Sun28.Ordinary Height

abbrev UnitRing (S : Finset ℕ) := Localization (Submonoid.powers (primeProduct S:ℤ))

theorem prime_product_nonzero (S : Finset ℕ) (prime : ∀ p∈S,p.Prime) : primeProduct S≠0 :=
  (Finset.prod_pos fun p hp => (prime p hp).pos).ne'

theorem prime_factors_product (S : Finset ℕ) (prime : ∀ p∈S,p.Prime) :
    (primeProduct S).primeFactors=S := by
  ext p
  constructor
  · intro hp
    obtain ⟨pp,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    obtain ⟨q,hq,d⟩ := (Prime.dvd_finsetProd_iff (S:=S) pp.prime (fun n : ℕ => n)).mp dvd
    exact (Nat.prime_dvd_prime_iff_eq pp (prime q hq)).mp d ▸ hq
  · intro hp
    exact Nat.mem_primeFactors.mpr ⟨prime p hp,Finset.dvd_prod_of_mem (fun p : ℕ => p) hp,prime_product_nonzero S prime⟩

noncomputable def rationalMap (S : Finset ℕ) (prime : ∀ p∈S,p.Prime) : UnitRing S →+* ℚ :=
  IsLocalization.Away.lift (primeProduct S:ℤ) (g:=algebraMap ℤ ℚ)
    (isUnit_iff_ne_zero.mpr (by
      have integer : (primeProduct S:ℤ)≠0 := Int.natCast_ne_zero.mpr (prime_product_nonzero S prime)
      exact Int.cast_ne_zero.mpr integer))

theorem integer_unit {S : Finset ℕ} (prime : ∀ p∈S,p.Prime) {a : ℤ} (nz : a≠0)
    (supported : a.natAbs.primeFactors⊆S) : IsUnit (algebraMap ℤ (UnitRing S) a) := by
  apply (IsLocalization.Away.algebraMap_isUnit_iff (primeProduct S:ℤ)).mpr
  obtain ⟨k,h⟩ := (Nat.exists_dvd_pow_iff (Int.natAbs_ne_zero.mpr nz) (prime_product_nonzero S prime)).mpr
    ((prime_factors_product S prime).symm ▸ supported)
  exact ⟨k,Int.natAbs_dvd_natAbs.mp (by simpa using h)⟩

theorem rational_unit_lift {S : Finset ℕ} (prime : ∀ p∈S,p.Prime) {x : ℚ} (h : RationalSUnit S x) :
    ∃ u : (UnitRing S)ˣ, rationalMap S prime u=x := by
  obtain ⟨xn,nu,de⟩ := h
  have un := integer_unit prime (a:=x.num) (by simpa using xn) nu
  have ud := integer_unit prime (a:=(x.den:ℤ)) (by exact_mod_cast x.den_nz) (by simpa using de)
  let f := rationalMap S prime
  have eval (a : ℤ) : f (algebraMap ℤ (UnitRing S) a)=(a:ℚ) := IsLocalization.Away.lift_eq _ _ _
  have nu' : f un.unit=(x.num:ℚ) := by rw [un.unit_spec,eval]
  have de' : f ud.unit=(x.den:ℚ) := by rw [ud.unit_spec,eval]; simp
  have ni : f (↑ud.unit⁻¹:UnitRing S)=(x.den:ℚ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [←de',←map_mul]
    simp
  refine ⟨un.unit/ud.unit,?_⟩
  change f (↑(un.unit/ud.unit):UnitRing S)=x
  rw [div_eq_mul_inv,Units.val_mul,map_mul,nu',ni,←div_eq_mul_inv,Rat.num_div_den]

theorem rationalMap_injective (S : Finset ℕ) (prime : ∀ p∈S,p.Prime) :
    Function.Injective (rationalMap S prime) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  let N : ℤ := primeProduct S
  let f := rationalMap S prime
  obtain ⟨k,a,eq⟩ := IsLocalization.Away.surj N z
  have eval (n : ℤ) : f (algebraMap ℤ (UnitRing S) n)=(n:ℚ) := IsLocalization.Away.lift_eq _ _ _
  have mapped := congrArg f eq
  rw [map_mul,map_pow,eval,eval,show f z=0 from hz,zero_mul] at mapped
  have zero : a=0 := by exact_mod_cast mapped.symm
  rw [zero,map_zero] at eq
  have unit : IsUnit ((algebraMap ℤ (UnitRing S) N)^k) := (IsLocalization.Away.algebraMap_isUnit N).pow k
  exact unit.mul_left_eq_zero.mp eq

/-- The published statement on actual units of the concrete localization Z[1/N_S].
The equation is imposed in the localized ring, and heights use its embedding in Q. -/
def PublishedCorollary72 : Prop :=
  ∀ (S : Finset ℕ) (prime : ∀ p∈S,p.Prime) (u v : (UnitRing S)ˣ),
    (u : UnitRing S)+(v : UnitRing S)=1 →
    let n : ℝ := 2^7*(primeProduct S:ℝ)
    logHeight₁ (rationalMap S prime u)≤(3/2)*n*(Real.log n)^2+65 ∧
    logHeight₁ (rationalMap S prime v)≤(3/2)*n*(Real.log n)^2+65

theorem supported_corollary (published : PublishedCorollary72) : VonKanel72 := by
  intro S prime x y hx hy eq
  obtain ⟨u,hu⟩ := rational_unit_lift prime hx
  obtain ⟨v,hv⟩ := rational_unit_lift prime hy
  have inRing : (u : UnitRing S)+(v : UnitRing S)=1 := by
    apply rationalMap_injective S prime
    simpa only [map_add,map_one,hu,hv] using eq
  have bounds := published S prime u v inRing
  simpa only [hu,hv] using bounds

theorem original_five_from_units (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ LargeResidualHeight :=
  originalFiveHeight_iff_large_residual (supported_corollary published)

end Sun28.FiveMarkUnits
#print axioms Sun28.FiveMarkUnits.prime_factors_product
#print axioms Sun28.FiveMarkUnits.rational_unit_lift
#print axioms Sun28.FiveMarkUnits.rationalMap_injective
#print axioms Sun28.FiveMarkUnits.supported_corollary
#print axioms Sun28.FiveMarkUnits.original_five_from_units
