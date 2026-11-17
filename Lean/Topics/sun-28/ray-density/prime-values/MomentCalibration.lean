import PairDensity
import MomentRows

namespace Sun28.PrimeValues
open Finset Filter Sun28.MixedSieve Sun28.PrimeLower Sun28.FinitePattern Sun28.SinglePrime
open Sun28.ContactFactors Sun28.PrimeMass
open scoped Classical
noncomputable section

/-- Conditional loss in the finite residue model. At split primes it counts with
multiplicity for every ordered collision pair. At inert primes the exceptional
integer residue pair has mass 1/p² before conditioning on all norm residues being units. -/
def localPairRate (A : Fin 3→ℚ) (p : ℕ) [Fact p.Prime] : ℝ :=
  let c:=coefficients A p
  if p%4=3 then (1/(p:ℝ)^2)/unitRate c else averagePairs c/unitRate c

theorem local_rate_bound (A : Fin 3→ℚ) {p : ℕ} [Fact p.Prime] (big : 26≤p) :
    localPairRate A p ≤ 1404/((p:ℝ)-1)^2 := by
  let c:=coefficients A p
  have k : Fintype.card ↥(shifts A)≤13 := by simpa using Sun28.GaussianSelection.shifts_card_le A
  change (if p%4=3 then _ else _) ≤ _
  split
  next =>
    have half:= (inert_relative_loss_le c (by omega)).1
    have pp : (1:ℝ)<p := by exact_mod_cast (show 1<p by omega)
    have positive : (0:ℝ)<p := by linarith
    have up : 0<unitRate c := by linarith
    calc
      _ ≤ 2/(p:ℝ)^2 := by
        apply (div_le_iff₀ up).mpr
        apply le_trans _ (mul_le_mul_of_nonneg_left half (by positivity))
        ring_nf
        exact le_rfl
      _ ≤ 2/((p:ℝ)-1)^2 := div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos (by linarith)) (by nlinarith)
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  next => exact relative_pair_rate big k c

/-- An upper comparison suffices. Single-prime convergence may have a threshold
depending on p; no distribution over a composite growing conductor is assumed. -/
def calibratedUpper (A : Fin 3→ℚ) (d K j p : ℕ) [Fact p.Prime] : Prop :=
  ∀ ε : ℝ,0<ε → ∀ᶠ t : ℕ in atTop,
    let N:=lengthAt t
    let W:=rowWidth j N
    upperMoment A d K p N W ≤ localPairRate A p * patternMass A d K K N W + ε*((N:ℝ)*W)

theorem relative_of_calibrated {A : Fin 3→ℚ} {d K j p : ℕ} [Fact p.Prime] (big : 26≤p)
    (H:calibratedUpper A d K j p) : relativeUpper A d K j p := by
  intro ε pos
  filter_upwards [H ε pos] with t h
  dsimp only at h ⊢
  have non : 0≤patternMass A d K K (lengthAt t) (rowWidth j (lengthAt t)) := sum_nonneg fun z _=>base_nonneg A K z
  exact h.trans (add_le_add (mul_le_mul_of_nonneg_right (local_rate_bound A big) non) (le_refl _))

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.local_rate_bound
#print axioms Sun28.PrimeValues.relative_of_calibrated
