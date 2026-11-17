import WeightedSelection

namespace Sun28.WeightedSelection
open Sun28.ContactSieve Sun28.ContactFactors Sun28.NormSieve
noncomputable section

def mainMass {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (T : Finset ℕ) (κ L : ℕ)
    (S : Finset (Candidate A d H Y)) : ℝ := by
  classical exact ∑ a∈S.filter (fun a => below a T κ L),weight a

def removedMass {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} (T : Finset ℕ) (κ L : ℕ)
    (S : Finset (Candidate A d H Y)) : ℝ := by
  classical exact ∑ a∈S.filter (fun a => below a T κ L ∧ tail a T κ L),weight a

/-- One chosen Gaussian record per eligible pair in a growing rectangle. -/
structure CountingBoxes (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) where
  width : ℕ→ℕ
  grows : ∀ m : ℕ,∃ b₀ : ℕ,∀ b : ℕ,b₀≤b → m≤width b
  short : ∀ ε : ℝ,0<ε → ∃ b₀ : ℕ,∀ b : ℕ,b₀≤b → (width b:ℝ)^2 ≤ ε*b
  records : ℕ→Finset (Candidate A d H Y)
  inBox : ∀ b,∀ a∈records b,b<2*a.u ∧ a.u≤b ∧ a.v≤width b
  uniquePair : ∀ b,∀ a∈records b,∀ a'∈records b,a.u=a'.u → a.v=a'.v → a=a'
  covers : ∀ b (a : Candidate A d H Y),b<2*a.u → a.u≤b → a.v≤width b →
    ∃ a'∈records b,a'.u=a.u ∧ a'.v=a.v

/-- A positive lower bound and a tail bound on the same growing rectangles,
normalized by the number of integer parameter pairs. -/
structure CountingBounds (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ : ℕ) : Prop where
  estimates : ∃ (c C : ℝ),0<c ∧ 0≤C ∧
    ∃ L₀ : ℕ,∀ L : ℕ,L₀≤L → 0<L → ∃ boxes : CountingBoxes A d H Y,∀ ε : ℝ,0<ε →
      ∃ b₀ : ℕ,∀ b : ℕ,b₀≤b →
        let X := (b:ℝ)*(boxes.width b:ℝ)
        c*X ≤ mainMass T κ L (boxes.records b) ∧
          removedMass T κ L (boxes.records b) ≤ (C/(L:ℝ)+ε)*X

theorem surplus_of_bounds {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} {T : Finset ℕ} {κ : ℕ}
    (counts : CountingBounds A d H Y T κ) :
    ∃ L : ℕ,∃ S : Finset (Candidate A d H Y),surplus T κ L S := by
  obtain ⟨c,C,cp,_,L₀,est⟩:=counts.estimates
  obtain ⟨m,hm⟩:=exists_nat_gt (2*C/c)
  let L := max (L₀+1) m
  have lm : m≤L:=le_max_right _ _
  have big : L₀+1≤L:=le_max_left _ _
  have lp : 0<(L:ℝ) := by exact_mod_cast (show 0<L by omega)
  have step : C/(L:ℝ)<c/2 := by
    have l : 2*C/c<(L:ℝ):=hm.trans_le (by exact_mod_cast lm)
    apply (div_lt_iff₀ lp).mpr
    have h:=(div_lt_iff₀ cp).mp l
    nlinarith only [h]
  obtain ⟨boxes,estimate⟩:=est L (by omega) (by omega)
  obtain ⟨b₀,hb⟩:=estimate (c/2) (by linarith)
  obtain ⟨b₁,hw⟩:=boxes.grows 1
  let b := max (b₀+1) b₁
  have ha : b₀+1≤b:=le_max_left _ _
  have wide:=hw b (le_max_right _ _)
  have xpos : 0<(b:ℝ)*(boxes.width b:ℝ) :=
    mul_pos (by exact_mod_cast (show 0<b by omega))
      (by exact_mod_cast (show 0<boxes.width b by omega))
  obtain ⟨lower,upper⟩:=hb b (by omega)
  exact ⟨L,boxes.records b,upper.trans_lt
    ((mul_lt_mul_of_pos_right (by linarith : C/(L:ℝ)+c/2<c) xpos).trans_le lower)⟩

/-- The two weighted estimates for the actual cleared Sun coefficients. -/
def AnalyticCounts : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ),AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ),0<d → 0<κ → (∀ l∈T,l.Prime) → 2∈T →
      ∀ H Y : ℝ, CountingBounds (Sun28.RealPoleBounds.fixedScale n) d H Y T κ

theorem prime_values_of_counts (h : AnalyticCounts) : PrimeValuesWithResidues :=
  prime_values_iff_surplus.mpr fun X c q n roots d κ T dp kp primes two H Y =>
    surplus_of_bounds (h X c q n roots d κ T dp kp primes two H Y)

end
end Sun28.WeightedSelection
#print axioms Sun28.WeightedSelection.surplus_of_bounds
#print axioms Sun28.WeightedSelection.prime_values_of_counts
