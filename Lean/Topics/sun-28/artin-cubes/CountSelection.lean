import UnweightedRows

namespace Sun28.CutoffCount
open Finset Filter Topology Sun28.SinglePrime Sun28.ContactFactors Sun28.ContactSieve
open Sun28.FinitePattern Sun28.WeightedSelection Sun28.MediumSieve Sun28.PrimeMass
noncomputable section

/-- A one-cutoff lower bound for the number of rational prime tuples. -/
def Inputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4 → ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0<d → ∀ (B : ℕ) (D : ℝ), ∃ (L : ℕ) (δ : ℝ),
      B≤L ∧ 0<δ ∧ D < δ*((L:ℝ)*Real.log L) ∧ rows (Sun28.RealPoleBounds.fixedScale n) d L δ

/-- Truncating both signs at a single cutoff handles all finite tests. The tail
estimate is used at that very cutoff, so no second base or mixed ray test enters. -/
theorem count_surplus (low : Inputs) (upper : PrimeUpperInputs) : PositiveSurplus := by
  intro X c q n roots d κ T dp kp primes two H Y
  let A := Sun28.RealPoleBounds.fixedScale n
  let E := (2:ℝ)^(shifts A).card
  have ep : 0<E := by dsimp [E];positivity
  obtain ⟨K,C,cn,upp⟩ := upper X c q n roots d κ T dp kp primes two H Y
  let B := max (max 2 K) (max (T.sup id) (κ.primeFactors.sup id))
  obtain ⟨L,δ,large,δp,margin,counts⟩ := low X c q n roots d dp B (2*(C*(4*Real.log 4))*E)
  have l2 : 2≤L := (le_max_left 2 K).trans ((le_max_left _ _).trans large)
  have lp : 0<(L:ℝ) := by exact_mod_cast (show 0<L by omega)
  have logp := Real.log_pos (by exact_mod_cast (show 1<L by omega) : (1:ℝ)<L)
  obtain ⟨J,row⟩ := upp L ((le_max_right 2 K).trans ((le_max_left _ _).trans large))
  have inT (p : ℕ) (hp : p∈T) : p≤L :=
    (Finset.le_sup (f:=id) hp).trans ((le_max_left _ _).trans ((le_max_right _ _).trans large))
  have inAux (p : ℕ) (hp : p∈κ.primeFactors) : p≤L :=
    (Finset.le_sup (f:=id) hp).trans ((le_max_right _ _).trans ((le_max_right _ _).trans large))
  refine ⟨L,surplus_of_row (frequent_of_count counts) (sharp_transfer l2 cn row) l2 le_rfl inT inAux
    (div_pos δp ep) ?_⟩
  change (C*(4*Real.log 4)/Real.log L)/(L:ℝ) < (δ/E)/2
  field_simp
  linarith only [show 2*(C*(4*Real.log 4))*E < δ*((L:ℝ)*Real.log L) from margin]

end
end Sun28.CutoffCount
#print axioms Sun28.CutoffCount.count_surplus
