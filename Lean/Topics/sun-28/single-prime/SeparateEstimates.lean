import WidthSelection
import SinglePrimeCounts

namespace Sun28.SinglePrime
open Filter Topology Sun28.WeightedSelection Sun28.ContactSieve
noncomputable section
variable {A : Fin 3→ℚ} {d : ℕ} {H Y : ℝ} {T : Finset ℕ} {κ K L : ℕ} {σ C : ℝ}

/-- For a fixed finite set of prime tests, the count theorem may require a lower
threshold on the width. It suffices that every fixed square-root row eventually clears it. -/
def CountThreshold (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ K L : ℕ) (σ : ℝ) : Prop :=
  ∃ ω : ℕ→ℕ,(∀ j,∀ᶠ b : ℕ in atTop,ω b≤rowWidth j b) ∧
    ∀ (w : ℕ→ℕ) (grow : Tendsto w atTop atTop)
      (short : ∀ ε : ℝ,0<ε → ∀ᶠ b : ℕ in atTop,(w b:ℝ)^2≤ε*b),
      (∀ᶠ b : ℕ in atTop,ω b≤w b) →
        CountsAt A d H Y T κ K L (numericalBoxes w (fun m=>eventually_atTop.mp (tendsto_atTop.mp grow m))
          (fun ε ep=>eventually_atTop.mp (short ε ep))) σ

/-- An estimate on each fixed aspect ratio. The error allowance tends to zero with the row index.
The starting b may depend arbitrarily on the row and the finite cutoff. -/
def RowTail (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ L : ℕ) (C : ℝ) : Prop :=
  ∀ j : ℕ,∀ᶠ b : ℕ in atTop,
    removedMass T κ L (box (A:=A) (d:=d) (H:=H) (Y:=Y) b (rowWidth j b)) ≤
      (C/(L:ℝ)+1/((j:ℝ)+1))*((b:ℝ)*(rowWidth j b:ℝ))

theorem common_boxes (finite : CountThreshold A d H Y T κ K L σ)
    (tail : RowTail A d H Y T κ L C) :
    ∃ boxes : CountingBoxes A d H Y, CountsAt A d H Y T κ K L boxes σ ∧
      ∀ ε : ℝ,0<ε →∀ᶠ b in atTop,removedMass T κ L (boxes.records b) ≤(C/(L:ℝ)+ε)*area boxes b := by
  obtain ⟨ω,slow,counts⟩:=finite
  obtain ⟨s,up,good,grow,short⟩:=choose_width ω _ slow tail
  let w := fun b=>rowWidth (s b) b
  let boxes : CountingBoxes A d H Y := numericalBoxes w
    (fun m=>eventually_atTop.mp (tendsto_atTop.mp grow m)) (fun ε ep=>eventually_atTop.mp (short ε ep))
  refine ⟨boxes,counts w grow short (good.mono (fun b h=>h.2)),?_⟩
  intro ε ep
  filter_upwards [good,eventual_error up ep] with b hb he
  exact hb.1.trans (mul_le_mul_of_nonneg_right (add_le_add_right he _) (by change 0≤(b:ℝ)*(rowWidth (s b) b:ℝ); positivity))

structure SeparateBounds (A : Fin 3→ℚ) (d : ℕ) (H Y : ℝ) (T : Finset ℕ) (κ : ℕ) : Prop where
  estimates : ∃ (K : ℕ) (σ C : ℝ),2810≤K ∧ (∀ p∈T,p≤K) ∧ (∀ p∈κ.primeFactors,p≤K) ∧
    0<σ ∧ 0≤C ∧ ∀ L : ℕ,K≤L → CountThreshold A d H Y T κ K L σ ∧ RowTail A d H Y T κ L C

theorem single_prime_bounds (h : SeparateBounds A d H Y T κ) : SinglePrimeBounds A d H Y T κ := by
  obtain ⟨K,σ,C,hK,hT,hκ,hs,hC,all⟩:=h.estimates
  exact ⟨K,σ,C,hK,hT,hκ,hs,hC,fun L hL=>common_boxes (all L hL).1 (all L hL).2⟩

def SeparateInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ),AdmissibleRoots X c q n →
    ∀ (d κ : ℕ) (T : Finset ℕ),0<d → 0<κ → (∀ p∈T,p.Prime) → 2∈T →
      ∀ H Y : ℝ,SeparateBounds (Sun28.RealPoleBounds.fixedScale n) d H Y T κ

theorem single_prime_inputs (h : SeparateInputs) : SinglePrimeInputs :=
  fun X c q n roots d κ T dp kp primes two H Y=>single_prime_bounds (h X c q n roots d κ T dp kp primes two H Y)

end
end Sun28.SinglePrime
#print axioms Sun28.SinglePrime.common_boxes
#print axioms Sun28.SinglePrime.single_prime_bounds
#print axioms Sun28.SinglePrime.single_prime_inputs
