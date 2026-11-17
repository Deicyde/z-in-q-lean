import MinimalProducts
import SharperScale

/-! The exact rational supports, with both a chart-wise and a pooled five-mark criterion. -/
namespace Sun28.MinimalConductors
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples Height
noncomputable section

def target (A B : ℤ) : Prop :=
  pairLogHeight A B≤glazerConstant24*(∏ p ∈ oldContactPrimes oldCutoff A B,(p:ℝ))^24

def vonKanelBound (N : ℕ) : ℝ :=
  (3/2)*(128*(N:ℝ))*Real.log (128*(N:ℝ))^2+97

theorem least_positive (t : Fin 10) {A B : ℤ} (off : ∀ i,oldForm i A B≠0) :
    0<leastConductor t A B :=
  Finset.prod_pos (fun _ hp=>(small_primes t A B (least_subset t A B off hp)).pos)

/-- The published estimate on the exact reduced numerator and denominator primes of one pair. -/
theorem single_chart_height (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (t : Fin 10) :
    pairLogHeight A B≤vonKanelBound (leastConductor t A B) := by
  let S:=leastSet t A B
  let i:=first t
  let j:=second t
  let k:=third t
  let x:=crossRatio i j k A B
  have pr (p : ℕ) (hp : p∈S) : p.Prime := small_primes t A B (least_subset t A B off hp)
  have u:=(least_set_iff t A B off S).2 (fun _ h=>h)
  have h:=((supported_corollary published S pr x (1-x) u.1 u.2 (by ring)).1)
  have chart : pairLogHeight A B≤logHeight₁ x+32 := crossRatio_height _ _ _ (ne_of_lt (increasing t).1)
    (ne_of_lt (lt_trans (increasing t).1 (increasing t).2)) (ne_of_lt (increasing t).2) primitive off
  have bound : logHeight₁ x≤(3/2)*(128*(leastConductor t A B:ℝ))*Real.log (128*(leastConductor t A B:ℝ))^2+65 := by
    simpa only [S,leastConductor,show (2:ℝ)^7=128 by norm_num] using h
  unfold vonKanelBound
  linarith only [chart,bound]

theorem five_height_of_least (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (t : Fin 10)
    (test : leastConductor t A B≤(scale*cutoffProduct*oddProduct A B)^23) : target A B := by
  have bound:=coefficient_bound (least_positive t off) (pos_odd A B) test
  have cut : vonKanelBound (leastConductor t A B)≤glazerConstant24*(oddProduct A B:ℝ)^24 := by
    unfold vonKanelBound
    linarith only [bound]
  have result := (single_chart_height published primitive off t).trans cut
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using result

def allLarge (A B : ℤ) : Prop :=
  ∀ t : Fin 10,(scale*cutoffProduct*oddProduct A B)^23<leastConductor t A B

def LargeMinimalConductorHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) → allLarge A B → target A B

theorem original_iff_minimal_conductors (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ LargeMinimalConductorHeight := by
  constructor
  · exact fun h A B cop off _=>h A B cop off
  · intro remain A B cop off
    by_cases fail : allLarge A B
    · exact remain A B cop off fail
    · unfold allLarge at fail
      push Not at fail
      obtain ⟨t,ht⟩:=fail
      exact five_height_of_least published cop off t ht

/-- A strict failure at every minimal chart forces this explicit excess in even support. -/
theorem large_forces_even {A B : ℤ} (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (fail : allLarge A B) :
    scale^230*cutoffProduct^224*oddProduct A B^224<210^4*totalResidual A B^6 := by
  let K:=scale
  let C:=cutoffProduct
  let O:=oddProduct A B
  let E:=totalResidual A B
  have pos : 0<K*C*O := Nat.mul_pos (Nat.mul_pos positive_scale pos_cutoff) (pos_odd A B)
  have main : (K*C*O)^230 < 210^4*C^6*(O*E)^6 := calc
    _ = ∏ _t : Fin 10,(K*C*O)^23 := by simp [←pow_mul]
    _ < ∏ t : Fin 10,leastConductor t A B :=
      Finset.prod_lt_prod_of_nonempty₀ (fun _ _=>pow_pos pos _) (fun t _=>fail t) Finset.univ_nonempty
    _ ≤ _ := least_product_bounds primitive off
  have left (k c o : ℕ) : (k*c*o)^230=(c^6*o^6)*(k^230*c^224*o^224) := by ring
  have right (c o e : ℕ) : 210^4*c^6*(o*e)^6=(c^6*o^6)*(210^4*e^6) := by ring
  rw [left,right] at main
  exact lt_of_mul_lt_mul_left' main

theorem five_height_of_even (published : PublishedCorollary72) {A B : ℤ} (primitive : Int.gcd A B=1)
    (off : ∀ i,oldForm i A B≠0)
    (test : 210^4*totalResidual A B^6 ≤ scale^230*cutoffProduct^224*oddProduct A B^224) : target A B := by
  by_contra bad
  have fail : allLarge A B := by
    intro t
    by_contra! h
    exact bad (five_height_of_least published primitive off t h)
  exact (not_lt_of_ge test) (large_forces_even primitive off fail)

def LargeEvenSupportHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    scale^230*cutoffProduct^224*oddProduct A B^224<210^4*totalResidual A B^6 → target A B

theorem original_iff_even_support (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ LargeEvenSupportHeight := by
  constructor
  · exact fun h A B cop off _=>h A B cop off
  · intro remain A B cop off
    rcases le_or_gt (210^4*totalResidual A B^6) (scale^230*cutoffProduct^224*oddProduct A B^224) with h|h
    · exact five_height_of_even published cop off h
    · exact remain A B cop off h

end
end Sun28.MinimalConductors
#print axioms Sun28.MinimalConductors.least_positive
#print axioms Sun28.MinimalConductors.single_chart_height
#print axioms Sun28.MinimalConductors.five_height_of_least
#print axioms Sun28.MinimalConductors.original_iff_minimal_conductors
#print axioms Sun28.MinimalConductors.large_forces_even
#print axioms Sun28.MinimalConductors.five_height_of_even
#print axioms Sun28.MinimalConductors.original_iff_even_support
