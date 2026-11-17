import ContactInvariant
import RationalBranchHeight

/-! Sum normalization of the ten branch weights and its local additive orders. -/
open Polynomial
namespace ZInQBlueprint.ContactInvariant
open BranchHeight SexticThetaHeight ResidualFactors
noncomputable section

/-- Sum-normalized projective branch coordinates in the intrinsic ratio field. -/
def sumWeights (r : Fin 6 → ℂ) (i : Fin 10) : weightField r :=
  weights r i / ∑ j, weights r j

/-- In the complex embedding, sum normalization cancels the original pivot weight. -/
theorem sumWeights_complex {r : Fin 6 → ℂ} (hr : Function.Injective r) (i : Fin 10) :
    ((sumWeights r i : weightField r):ℂ) =
      ThetaPeriod.branchValue (ThetaPeriod.finiteBranches r) (BranchFormula.pairs i) /
        ∑ j : Fin 10, ThetaPeriod.branchValue (ThetaPeriod.finiteBranches r) (BranchFormula.pairs j) := by
  let w := fun j : Fin 10 => ThetaPeriod.branchValue (ThetaPeriod.finiteBranches r) (BranchFormula.pairs j)
  have h0 : w 0 ≠ 0 := ThetaPeriod.branchValue_nonzero _ (ThetaPeriod.finiteBranches_injective hr) _
  change (weightField r).val (weights r i / ∑ j, weights r j)=w i / ∑ j, w j
  rw [map_div₀,map_sum]
  change (w i / w 0) / (∑ j, w j / w 0) = _
  rw [← Finset.sum_div]
  by_cases h : ∑ j, w j=0
  · simp [h]
  · field_simp [h0,h]

theorem sumWeights_equations {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0) :
    (∑ i, sumWeights r i)=1 ∧
    (∏ i, sumWeights r i)=((SixContact.J u/3779136:ℚ):weightField r)^2 := by
  obtain ⟨hs,hJ⟩ := paper_pair hu hδ hr hz
  constructor
  · simp only [sumWeights,← Finset.sum_div,div_self hs]
  · simp only [sumWeights,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
      Rat.cast_div,Rat.cast_ofNat,div_pow]
    have h := (eq_div_iff (pow_ne_zero 10 hs)).mp hJ
    apply (div_eq_div_iff (pow_ne_zero 10 hs) (by norm_num)).mpr
    linear_combination -h

variable {K : Type*} [Field K]

/-- The product identity determines the sum of the orders in every additive valuation. -/
theorem sum_of_orders (ord : K → ℚ) (hm : ∀ {x y:K}, x≠0 → y≠0 → ord (x*y)=ord x+ord y)
    {x : Fin 10 → K} (hx : ∀ i, x i ≠ 0) {j : K} (hj : j≠0)
    (hprod : ∏ i, x i=j^2) : (∑ i, ord (x i))=2*ord j := by
  classical
  have h1 : ord 1=0 := by have he := hm (x:=1) (y:=1) one_ne_zero one_ne_zero; rw [one_mul] at he; linarith
  have hp (s : Finset (Fin 10)) : ord (∏ i ∈ s, x i)=∑ i ∈ s, ord (x i) := by
    induction s using Finset.induction_on with
    | empty => simpa using h1
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha,hm (hx _) (Finset.prod_ne_zero_iff.mpr (fun i _ => hx i)),ih]
  rw [← hp Finset.univ,hprod,pow_two,hm hj hj]
  ring

/-- A single exceptional order determines the other nine from their sum and the difference. -/
theorem nine_and_one (a : Fin 10 → ℚ) (i₀ : Fin 10) (m gap total : ℚ)
    (ha : ∀ i, a i = m + if i=i₀ then gap else 0) (hs : ∑ i, a i=total) :
    m=(total-gap)/10 ∧ a i₀=(total+9*gap)/10 := by
  simp only [ha,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true] at hs
  norm_cast at hs
  simp [ha]
  constructor <;> linarith

/-- The contact and pole predictions are two specializations of the same linear equation. -/
theorem normalized_pattern {u δ : ℚ} {p : ℕ} [Fact p.Prime] (hp : 5<p)
    (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) {r : Fin 6 → ℂ}
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (ord : weightField r → ℚ)
    (hm : ∀ {x y : weightField r}, x≠0 → y≠0 → ord (x*y)=ord x+ord y)
    (hq : ∀ q : ℚ, q≠0 → ord (q:weightField r)=(padicValRat p q:ℚ))
    (i₀ : Fin 10) (m h g : ℚ)
    (hF : (padicValRat p (contactProduct u.num (u.den:ℤ):ℤ):ℚ)=h)
    (hG : (padicValRat p (poleForm u.num (u.den:ℤ):ℤ):ℚ)=g)
    (relative : ∀ i, ord (sumWeights r i)=m + if i=i₀ then 4*h+8*g else 0) :
    m= -2*g ∧ ord (sumWeights r i₀)=4*h+6*g := by
  have hj : SixContact.J u ≠ 0 := (CoarseConic.unmarked_range hu).2.ne
  have hjc : SixContact.J u/3779136 ≠ 0 := div_ne_zero hj (by norm_num)
  have hn : (↑(SixContact.J u/3779136:ℚ):weightField r) ≠ 0 := by exact_mod_cast hjc
  have he := (sumWeights_equations hu hδ hr hz).2
  have hx : ∀ i, sumWeights r i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp (he ▸ pow_ne_zero 2 hn)) i (Finset.mem_univ _)
  have hs := sum_of_orders ord hm hx hn he
  rw [hq _ hjc,padicValRat.div hj (by norm_num),invariant_coefficient_unit hp,sub_zero,
    J_valuation_rational u hu hp] at hs
  push_cast at hs
  rw [hF,hG] at hs
  obtain ⟨hm',hex⟩ := nine_and_one _ i₀ m (4*h+8*g) _ relative hs
  constructor <;> linarith

/-- Compare the projective weight orders at one fixed denominator. The nonzero scalar
introduced by sum normalization cancels on taking these differences. -/
theorem gap_after_sum_normalization {u δ : ℚ} (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0)
    {r : Fin 6 → ℂ} (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (ord : weightField r → ℚ)
    (hm : ∀ {x y : weightField r}, x≠0 → y≠0 → ord (x*y)=ord x+ord y)
    (i₀ : Fin 10) (l gap : ℚ)
    (raw : ∀ i, ord (weights r i)=l + if i=i₀ then gap else 0) :
    ∃ m : ℚ, ∀ i, ord (sumWeights r i)=m + if i=i₀ then gap else 0 := by
  set S := ∑ j, weights r j
  have hS : S ≠ 0 := (paper_pair hu hδ hr hz).1
  have hj : SixContact.J u ≠ 0 := (CoarseConic.unmarked_range hu).2.ne
  have hjc : SixContact.J u/3779136 ≠ 0 := div_ne_zero hj (by norm_num)
  have hn : (↑(SixContact.J u/3779136:ℚ):weightField r) ≠ 0 := by exact_mod_cast hjc
  have he := (sumWeights_equations hu hδ hr hz).2
  have hx : ∀ i, sumWeights r i ≠ 0 := fun i =>
    (Finset.prod_ne_zero_iff.mp (he ▸ pow_ne_zero 2 hn)) i (Finset.mem_univ _)
  refine ⟨l-ord S,?_⟩
  intro i
  have eq : sumWeights r i*S=weights r i := div_mul_cancel₀ _ hS
  have val := congrArg ord eq
  rw [hm (hx i) hS,raw] at val
  linarith

/-- Given the raw projective gap, the chart-independent factors normalized by their sum
have the explicitly stated order at every coordinate. -/
theorem orders_of_raw_gap {u δ : ℚ} {p : ℕ} [Fact p.Prime] (hp : 5<p)
    (hu : u ∉ ZInQ.contactSet) (hδ : δ ≠ 0) {r : Fin 6 → ℂ}
    (hr : Function.Injective r) (hz : ∀ i, aeval (r i) (sextic u δ)=0)
    (ord : weightField r → ℚ)
    (hm : ∀ {x y : weightField r}, x≠0 → y≠0 → ord (x*y)=ord x+ord y)
    (hq : ∀ q : ℚ, q≠0 → ord (q:weightField r)=(padicValRat p q:ℚ))
    (i₀ : Fin 10) (l h g : ℚ)
    (hF : (padicValRat p (contactProduct u.num (u.den:ℤ):ℤ):ℚ)=h)
    (hG : (padicValRat p (poleForm u.num (u.den:ℤ):ℤ):ℚ)=g)
    (raw : ∀ i, ord (weights r i)=l + if i=i₀ then 4*h+8*g else 0) :
    ∀ i, ord (sumWeights r i)=if i=i₀ then 4*h+6*g else -2*g := by
  obtain ⟨m,relative⟩ := gap_after_sum_normalization hu hδ hr hz ord hm i₀ l (4*h+8*g) raw
  obtain ⟨hlo,hhi⟩ := normalized_pattern hp hu hδ hr hz ord hm hq i₀ m h g hF hG relative
  intro i
  by_cases hi : i=i₀
  · simpa [hi] using hhi
  · simpa [hi,hlo] using relative i

end
end ZInQBlueprint.ContactInvariant
#print axioms ZInQBlueprint.ContactInvariant.sumWeights_equations
#print axioms ZInQBlueprint.ContactInvariant.sum_of_orders
#print axioms ZInQBlueprint.ContactInvariant.nine_and_one
#print axioms ZInQBlueprint.ContactInvariant.normalized_pattern
#print axioms ZInQBlueprint.ContactInvariant.gap_after_sum_normalization
#print axioms ZInQBlueprint.ContactInvariant.sumWeights_complex
#print axioms ZInQBlueprint.ContactInvariant.orders_of_raw_gap
