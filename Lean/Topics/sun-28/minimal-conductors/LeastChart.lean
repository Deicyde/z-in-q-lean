import MinimalFiveHeight

/-! All ten least conductors can be tested by the least of ten natural numbers. -/
namespace Sun28.MinimalConductors
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.FiveMarkTriples
noncomputable section

def best (A B : ℤ) : ℕ := Finset.univ.inf' Finset.univ_nonempty (fun t : Fin 10 => leastConductor t A B)

theorem best_attained (A B : ℤ) : ∃ t : Fin 10, leastConductor t A B=best A B := by
  obtain ⟨t,_,e⟩:=Finset.exists_mem_eq_inf' (s:=(Finset.univ : Finset (Fin 10)))
    (f:=fun t => leastConductor t A B) Finset.univ_nonempty
  exact ⟨t,e.symm⟩

theorem best_le (A B : ℤ) (t : Fin 10) : best A B≤leastConductor t A B :=
  Finset.inf'_le _ (Finset.mem_univ t)

/-- The direct analytic test keeps the logarithm, before any power absorption or pooling. -/
theorem attained_height (published : PublishedCorollary72) {A B : ℤ}
    (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) :
    pairLogHeight A B≤vonKanelBound (best A B) := by
  obtain ⟨t,eq⟩:=best_attained A B
  rw [←eq]; exact single_chart_height published primitive off t

/-- Failure of the exact published threshold implies all ten polynomial-size tests fail. -/
theorem exact_forces_large {A B : ℤ} (off : ∀ i,oldForm i A B≠0)
    (fail : glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B)) : allLarge A B := by
  obtain ⟨t,eq⟩:=best_attained A B
  intro j
  by_contra! h
  have test := (best_le A B j).trans h
  rw [←eq] at test fail
  have bound:=coefficient_bound (least_positive t off) (pos_odd A B) test
  unfold vonKanelBound at fail
  linarith only [bound,fail]

theorem exact_forces_even {A B : ℤ} (primitive : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0)
    (fail : glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B)) :
    scale^230*cutoffProduct^224*oddProduct A B^224<210^4*totalResidual A B^6 :=
  large_forces_even primitive off (exact_forces_large off fail)

def ExactLeastHeight : Prop :=
  ∀ A B : ℤ, Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) → target A B

/-- The exact published-function residual is smaller than the power and pooling residuals. -/
theorem original_iff_exact_least (published : PublishedCorollary72) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ ExactLeastHeight := by
  constructor
  · exact fun h A B cop off _=>h A B cop off
  · intro remain A B cop off
    rcases le_or_gt (vonKanelBound (best A B)) (glazerConstant24*(oddProduct A B:ℝ)^24) with h|h
    · have b:=(attained_height published cop off).trans h
      simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using b
    · exact remain A B cop off h

end
end Sun28.MinimalConductors
#print axioms Sun28.MinimalConductors.best_attained
#print axioms Sun28.MinimalConductors.best_le
#print axioms Sun28.MinimalConductors.attained_height
#print axioms Sun28.MinimalConductors.exact_forces_large
#print axioms Sun28.MinimalConductors.exact_forces_even
#print axioms Sun28.MinimalConductors.original_iff_exact_least
