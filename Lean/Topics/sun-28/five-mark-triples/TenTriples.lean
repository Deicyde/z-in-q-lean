import ProjectiveHeight
import TripleResiduals

/-! Reduction of the original five-mark height by the ten rational unit equations. -/
namespace Sun28.FiveMarkTriples
open Sun28.Ordinary Sun28.FiveMarkUnits Height

theorem explicit_five_plus32 {N O : ℕ} (npos : 0<N) (opos : 0<O)
    (conductor : N≤(cutoffProduct*O)^23) :
    (3/2)*(128*(N:ℝ))*(Real.log (128*(N:ℝ)))^2+65+32 ≤ glazerConstant24*(O:ℝ)^24 := by
  let B : ℝ := cutoffProduct
  have b : 1≤B := by
    change (1:ℝ)≤(cutoffProduct:ℝ)
    exact_mod_cast (show 1≤cutoffProduct from pos_cutoff)
  have o : 1≤(O:ℝ) := by exact_mod_cast opos
  have x : 1≤B*(O:ℝ) := one_le_mul_of_one_le_of_one_le b o
  have co : (N:ℝ)≤(B*(O:ℝ))^23 := by
    change (N:ℝ)≤((cutoffProduct:ℝ)*(O:ℝ))^23
    exact_mod_cast conductor
  have h := analytic_absorption (by exact_mod_cast npos : (1:ℝ)≤N) x co
  have h6 : (192:ℝ)*53^2 ≤ 2*(4608^165888+6^100) := by
    have le : (6:ℝ)^8≤6^100 := pow_le_pow_right₀ (by norm_num) (by decide)
    have pos : (0:ℝ)≤4608^165888 := pow_nonneg (by norm_num) _
    calc
      (192:ℝ)*53^2 ≤ 2*6^8 := by norm_num
      _ ≤ 2*6^100 := mul_le_mul_of_nonneg_left le (by norm_num)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left pos) (by norm_num)
  have l := mul_le_mul_of_nonneg_right h6 (by positivity : 0≤(B*(O:ℝ))^24)
  have c : (97:ℝ)≤128*(O:ℝ)^24 := by
    have h1 : 1≤(O:ℝ)^24 := one_le_pow₀ o
    linarith
  calc
    _ ≤ (192*53^2)*(B*(O:ℝ))^24+97 := by linarith only [h]
    _ ≤ 2*(4608^165888+6^100)*(B*(O:ℝ))^24+128*(O:ℝ)^24 := add_le_add l c
    _ = glazerConstant24*(O:ℝ)^24 := by
      have beq (S : Finset ℕ) : (primeProduct S:ℝ)=∏ p ∈ S,(p:ℝ) := by
        unfold primeProduct
        push_cast
        rfl
      have clean (C b o : ℝ) : C*(b*o)^24+128*o^24=(C*b^24+128)*o^24 := by ring
      change _ = (2*(4608^165888+6^100)*(∏ p ∈ oldCutoff,(p:ℝ))^24+128)*(O:ℝ)^24
      rw [←beq oldCutoff]
      exact clean _ _ _


/-- The original bound follows as soon as one triple satisfies the residual threshold. -/
theorem five_height_of_triple_conductor (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (t : Fin 10)
    (co : primeProduct (oldCutoff∪triplePrimes (first t) (second t) (third t) A B)≤(cutoffProduct*oddProduct A B)^23) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  let i:=first t
  let j:=second t
  let k:=third t
  let S:=oldCutoff∪triplePrimes i j k A B
  let x:=crossRatio i j k A B
  have st:=increasing t
  have h1 : i≠j:=ne_of_lt st.1
  have h2 : j≠k:=ne_of_lt st.2
  have h3 : i≠k:=ne_of_lt (lt_trans st.1 st.2)
  have prime (p : ℕ) (hp : p∈S) : p.Prime := by
    rcases Finset.mem_union.mp hp with h|h
    · exact (Finset.mem_filter.mp h).2
    · exact support_prime h
  have units:=localised_pair h1 h3 h2 A B off
  have src:=(supported_corollary published S prime x (1-x) units.1 units.2 (by ring)).1
  have source : logHeight₁ x ≤ (3/2)*(128*(primeProduct S:ℝ))*Real.log (128*(primeProduct S:ℝ))^2+65 := by
    simpa only [show (2:ℝ)^7=128 by norm_num] using src
  have np : 0<primeProduct S:=Finset.prod_pos (fun p hp => (prime p hp).pos)
  have result := ((crossRatio_height i j k h1 h3 h2 primitive off).trans
    (add_le_add_left source 32)).trans (explicit_five_plus32 np (pos_odd A B) co)
  simpa only [oddProduct,oddSupport,primeProduct,Nat.cast_prod] using result

theorem five_height_of_triple (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (t : Fin 10)
    (small : residualTriple t A B≤(cutoffProduct*oddProduct A B)^22) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  apply five_height_of_triple_conductor published primitive off t
  calc
    _ ≤ _ := triple_conductor t A B
    _ ≤ (cutoffProduct*oddProduct A B)*(cutoffProduct*oddProduct A B)^22 :=
      Nat.mul_le_mul_left _ small
    _ = _ := by ring

/-- The possible counterexamples after using every rational unit equation. -/
def TenLargeResidualHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ t : Fin 10,(cutoffProduct*oddProduct A B)^22<residualTriple t A B) →
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

theorem originalFiveHeight_iff_ten_triples (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ TenLargeResidualHeight := by
  constructor
  · exact fun all A B primitive off _ => all A B primitive off
  · intro remain A B primitive off
    by_cases failure : ∀ t : Fin 10,(cutoffProduct*oddProduct A B)^22<residualTriple t A B
    · exact remain A B primitive off failure
    push Not at failure
    obtain ⟨t,small⟩:=failure
    exact five_height_of_triple published primitive off t small

/-- A single test on the even support of all five forms also suffices. -/
theorem five_height_of_total (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (small : totalResidual A B^6≤(cutoffProduct*oddProduct A B)^220) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  have someChart : ¬ ∀ t : Fin 10,(cutoffProduct*oddProduct A B)^22<residualTriple t A B :=
    fun h => (not_lt_of_ge small) (failures_force_total primitive h)
  push Not at someChart
  obtain ⟨t,ht⟩:=someChart
  exact five_height_of_triple published primitive off t ht

def PooledLargeResidualHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (cutoffProduct*oddProduct A B)^220<totalResidual A B^6 →
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

theorem originalFiveHeight_iff_pooled (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ PooledLargeResidualHeight := by
  constructor
  · exact fun all A B primitive off _ => all A B primitive off
  · intro remain A B primitive off
    rcases le_or_gt (totalResidual A B^6) ((cutoffProduct*oddProduct A B)^220) with h|h
    · exact five_height_of_total published primitive off h
    · exact remain A B primitive off h

end Sun28.FiveMarkTriples
#print axioms Sun28.FiveMarkTriples.explicit_five_plus32
#print axioms Sun28.FiveMarkTriples.five_height_of_triple_conductor
#print axioms Sun28.FiveMarkTriples.five_height_of_triple
#print axioms Sun28.FiveMarkTriples.originalFiveHeight_iff_ten_triples
#print axioms Sun28.FiveMarkTriples.five_height_of_total
#print axioms Sun28.FiveMarkTriples.originalFiveHeight_iff_pooled
