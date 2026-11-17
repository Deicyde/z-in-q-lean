import UnitHeight

/-! The exact remaining subfamily of the original five-contact inequality. -/
namespace Sun28.FiveMarkUnits
open Sun28.Ordinary Height

theorem five_height_of_conductor (published : VonKanel72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (conductor : primeProduct (tripleSupport A B)≤(cutoffProduct*oddProduct A B)^23) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  obtain ⟨na,nb,nd⟩ := off_triple off
  obtain ⟨x,y,equation⟩ := triple_equation na nb nd
  have source := (published (tripleSupport A B) (fun p hp => triple_primes hp) _ _ x y equation).1
  rw [signed_height nb primitive,show (2:ℝ)^7=128 by norm_num] at source
  have np : 0<primeProduct (tripleSupport A B) := Finset.prod_pos fun _ hp => (triple_primes hp).pos
  have result := source.trans (explicit_five_bound np (pos_odd A B) conductor)
  simpa only [oddProduct,oddSupport,primeProduct,Nat.cast_prod] using result

theorem five_height_of_residual (published : VonKanel72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (small : residualProduct A B≤(cutoffProduct*oddProduct A B)^22) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  apply five_height_of_conductor published primitive off
  calc
    primeProduct (tripleSupport A B) ≤ _ := support_bound A B
    _ ≤ (cutoffProduct*oddProduct A B)*(cutoffProduct*oddProduct A B)^22 :=
      Nat.mul_le_mul_left _ small
    _ = _ := by ring

theorem five_height_of_small_residual (published : VonKanel72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (small : residualProduct A B≤(oddProduct A B)^21) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  apply five_height_of_residual published primitive off
  have oc : oddProduct A B≤cutoffProduct*oddProduct A B := Nat.le_mul_of_pos_left _ pos_cutoff
  calc
    residualProduct A B ≤ _ := small
    _ ≤ (oddProduct A B)^22 := Nat.pow_le_pow_right (pos_odd A B) (by decide)
    _ ≤ _ := Nat.pow_le_pow_left oc _

/-- A counterexample to the original five-mark bound would have to fail this
strict residual-radical threshold. The target still quantifies over both signs. -/
def LargeResidualHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (cutoffProduct*oddProduct A B)^22<residualProduct A B →
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

theorem originalFiveHeight_iff_large_residual (published : VonKanel72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ LargeResidualHeight := by
  constructor
  · exact fun all A B primitive off _ => all A B primitive off
  · intro remainder A B primitive off
    rcases le_or_gt (residualProduct A B) ((cutoffProduct*oddProduct A B)^22) with small|large
    · exact five_height_of_residual published primitive off small
    · exact remainder A B primitive off large

/-- Each residual prime divides one of the triple forms, is outside the original
cutoff, and all five original contact orders at it are even, including order 0. -/
theorem residual_even {A B : ℤ} {p : ℕ} (member : p∈residualSupport A B) :
    p.Prime ∧ 76176<p ∧ (p∣A.natAbs ∨ p∣B.natAbs ∨ p∣(A-B).natAbs) ∧
      ∀ i : Fin 5, Even (padicValInt p (oldForm i A B)) := by
  obtain ⟨inTriple,outside⟩ := Finset.mem_sdiff.mp member
  have prime := triple_primes inTriple
  have small : p∉oldCutoff := fun inside => outside (Finset.mem_union_left _ inside)
  have large : 76176<p := by
    by_contra! le
    exact small (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prime⟩)
  have divisor : p∣A.natAbs ∨ p∣B.natAbs ∨ p∣(A-B).natAbs := by
    rcases Finset.mem_union.mp inTriple with ab|d
    · rcases Finset.mem_union.mp ab with a|b
      · exact Or.inl (Nat.dvd_of_mem_primeFactors a)
      · exact Or.inr (Or.inl (Nat.dvd_of_mem_primeFactors b))
    · exact Or.inr (Or.inr (Nat.dvd_of_mem_primeFactors d))
  refine ⟨prime,large,divisor,?_⟩
  intro i
  rcases Nat.even_or_odd (padicValInt p (oldForm i A B)) with even|odd
  · exact even
  have pos : 0<padicValInt p (oldForm i A B) := by obtain ⟨k,hk⟩ := odd; omega
  exact (outside (Finset.mem_union_right _ (mem_oldContactPrimes.mpr ⟨prime,small,i,pos,odd⟩))).elim

end Sun28.FiveMarkUnits
#print axioms Sun28.FiveMarkUnits.five_height_of_conductor
#print axioms Sun28.FiveMarkUnits.five_height_of_residual
#print axioms Sun28.FiveMarkUnits.five_height_of_small_residual
#print axioms Sun28.FiveMarkUnits.originalFiveHeight_iff_large_residual
#print axioms Sun28.FiveMarkUnits.residual_even
