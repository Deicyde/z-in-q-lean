import ConductorPooling

/-! The published conductor estimate with an explicit part of the original coefficient. -/
namespace Sun28.FiveMarkTriples
open Sun28.Ordinary Sun28.FiveMarkUnits Height

/-- Reserve one factor of 4608^24 for the scalar in the analytic estimate. -/
def conductorScale : ℕ := 4608^6911

theorem scaled_five_plus32 {N O : ℕ} (npos : 0<N) (opos : 0<O)
    (conductor : N≤(conductorScale*cutoffProduct*O)^23) :
    (3/2)*(128*(N:ℝ))*(Real.log (128*(N:ℝ)))^2+65+32 ≤ glazerConstant24*(O:ℝ)^24 := by
  let K:ℝ:=conductorScale
  let B:ℝ:=cutoffProduct
  have k : K=(4608:ℝ)^6911 := by
    change (((4608:ℕ)^6911:ℕ):ℝ)=(4608:ℝ)^6911
    rw [Nat.cast_pow]
    rfl
  have kb : 1≤K := k ▸ one_le_pow₀ (by norm_num : (1:ℝ)≤4608)
  have b : 1≤B := by
    change (1:ℝ)≤(cutoffProduct:ℝ)
    exact_mod_cast (show 1≤cutoffProduct from pos_cutoff)
  have o : 1≤(O:ℝ) := by exact_mod_cast opos
  have x : 1≤K*B*(O:ℝ) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le kb b) o
  have co : (N:ℝ)≤(K*B*(O:ℝ))^23 := by
    change (N:ℝ)≤((conductorScale:ℝ)*(cutoffProduct:ℝ)*(O:ℝ))^23
    exact_mod_cast conductor
  have h := analytic_absorption (by exact_mod_cast npos : (1:ℝ)≤N) x co
  have margin : (192:ℝ)*53^2 ≤ 4608^24 := calc
    _ ≤ (4608:ℝ)^2 := by norm_num
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by decide)
  have a : ((192:ℝ)*53^2)*K^24≤2*(4608^165888+6^100) := calc
    _ ≤ (4608:ℝ)^24*K^24 := mul_le_mul_of_nonneg_right margin (pow_nonneg (by linarith only [kb]) _)
    _ = (4608:ℝ)^165888 := by rw [k,←pow_mul,←pow_add]
    _ ≤ _ := by
      have twice (U V : ℝ) (u : 0≤U) (v : 0≤V) : U≤2*(U+V) := by linarith
      exact twice _ _ (pow_nonneg (by norm_num) _) (pow_nonneg (by norm_num) _)
  have bO : 0≤(B*(O:ℝ))^24 := pow_nonneg (by positivity) _
  have c : (97:ℝ)≤128*(O:ℝ)^24 := by
    have h1 : 1≤(O:ℝ)^24 := one_le_pow₀ o
    linarith
  have ident (z k b o : ℝ) : z*(k*b*o)^24=(z*k^24)*(b*o)^24 := by ring
  calc
    _ ≤ (192*53^2)*(K*B*(O:ℝ))^24+97 := by linarith only [h]
    _ ≤ 2*(4608^165888+6^100)*(B*(O:ℝ))^24+128*(O:ℝ)^24 := by
      rw [ident]
      exact add_le_add (mul_le_mul_of_nonneg_right a bO) c
    _ = glazerConstant24*(O:ℝ)^24 := by
      have beq (S : Finset ℕ) : (primeProduct S:ℝ)=∏ p ∈ S,(p:ℝ) := by
        unfold primeProduct
        push_cast
        rfl
      have clean (C b o : ℝ) : C*(b*o)^24+128*o^24=(C*b^24+128)*o^24 := by ring
      change _ = (2*(4608^165888+6^100)*(∏ p ∈ oldCutoff,(p:ℝ))^24+128)*(O:ℝ)^24
      rw [←beq oldCutoff]
      exact clean _ _ _

theorem five_height_of_scaled_conductor (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (t : Fin 10)
    (co : actualConductor t A B≤(conductorScale*cutoffProduct*oddProduct A B)^23) :
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
    (add_le_add_left source 32)).trans (scaled_five_plus32 np (pos_odd A B) co)
  simpa only [oddProduct,oddSupport,primeProduct,Nat.cast_prod] using result

theorem bad_scaled_conductors {A B : ℤ} (primitive : Int.gcd A B=1)
    (failure : ∀ t : Fin 10,(conductorScale*cutoffProduct*oddProduct A B)^23<actualConductor t A B) :
    conductorScale^230*cutoffProduct^220*oddProduct A B^224<totalResidual A B^6 := by
  let K:=conductorScale
  let C:=cutoffProduct
  let O:=oddProduct A B
  let E:=totalResidual A B
  have kp : 0<K:=pow_pos (by decide : 0<(4608:ℕ)) _
  have xp : 0<K*C*O := Nat.mul_pos (Nat.mul_pos kp pos_cutoff) (pos_odd A B)
  have cut (K C O : ℕ) : (K*C*O)^230=(C^10*O^6)*(K^230*C^220*O^224) := by ring
  have join (C O E : ℕ) : C^10*(O*E)^6=(C^10*O^6)*E^6 := by ring
  have inequality : (K*C*O)^230<C^10*(O*E)^6 := calc
    _ = ∏ _t : Fin 10,(K*C*O)^23 := by simp [←pow_mul]
    _ < ∏ t : Fin 10,actualConductor t A B :=
      Finset.prod_lt_prod_of_nonempty₀ (fun _ _=>pow_pos xp _) (fun t _=>failure t) Finset.univ_nonempty
    _ = _ := conductor_pool primitive
  rw [cut,join] at inequality
  exact lt_of_mul_lt_mul_left' inequality

def ScaledLargeConductorHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ t : Fin 10,(conductorScale*cutoffProduct*oddProduct A B)^23<actualConductor t A B) →
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

theorem originalFiveHeight_iff_scaled_conductors (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ ScaledLargeConductorHeight := by
  constructor
  · exact fun all A B primitive off _ => all A B primitive off
  · intro remain A B primitive off
    by_cases failure : ∀ t : Fin 10,(conductorScale*cutoffProduct*oddProduct A B)^23<actualConductor t A B
    · exact remain A B primitive off failure
    push Not at failure
    obtain ⟨t,small⟩:=failure
    exact five_height_of_scaled_conductor published primitive off t small

theorem five_height_of_scaled_pool (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (small : totalResidual A B^6≤conductorScale^230*cutoffProduct^220*oddProduct A B^224) :
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24 := by
  have someChart : ¬ ∀ t : Fin 10,(conductorScale*cutoffProduct*oddProduct A B)^23<actualConductor t A B :=
    fun h => (not_lt_of_ge small) (bad_scaled_conductors primitive h)
  push Not at someChart
  obtain ⟨t,ht⟩:=someChart
  exact five_height_of_scaled_conductor published primitive off t ht

def ScaledLargeEvenHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    conductorScale^230*cutoffProduct^220*oddProduct A B^224<totalResidual A B^6 →
    pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

theorem originalFiveHeight_iff_scaled_even (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ ScaledLargeEvenHeight := by
  constructor
  · exact fun all A B primitive off _ => all A B primitive off
  · intro remain A B primitive off
    rcases le_or_gt (totalResidual A B^6) (conductorScale^230*cutoffProduct^220*oddProduct A B^224) with h|h
    · exact five_height_of_scaled_pool published primitive off h
    · exact remain A B primitive off h

end Sun28.FiveMarkTriples
#print axioms Sun28.FiveMarkTriples.scaled_five_plus32
#print axioms Sun28.FiveMarkTriples.five_height_of_scaled_conductor
#print axioms Sun28.FiveMarkTriples.bad_scaled_conductors
#print axioms Sun28.FiveMarkTriples.originalFiveHeight_iff_scaled_conductors
#print axioms Sun28.FiveMarkTriples.five_height_of_scaled_pool
#print axioms Sun28.FiveMarkTriples.originalFiveHeight_iff_scaled_even
