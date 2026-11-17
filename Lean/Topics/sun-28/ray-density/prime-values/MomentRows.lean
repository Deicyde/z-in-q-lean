import TwoMoments
import HybridProjection

namespace Sun28.PrimeValues
open Finset Filter Topology Sun28.FinitePattern Sun28.SinglePrime Sun28.ContactFactors
open Sun28.ContactSieve Sun28.PrimeMass Sun28.WeightedSelection Sun28.MediumSieve
noncomputable section

/-- The additional prime p is fixed before t tends to infinity. The eventual
threshold may depend on the row, p and ε. No uniform error in growing p is required. -/
def relativeUpper (A : Fin 3→ℚ) (d K j p : ℕ) : Prop :=
  ∀ ε : ℝ, 0<ε → ∀ᶠ t : ℕ in atTop,
    let N := lengthAt t
    let W := rowWidth j N
    upperMoment A d K p N W ≤
      (1404/((p:ℝ)-1)^2)*patternMass A d K K N W + ε*((N:ℝ)*W)

/-- The base lower estimate and single-prime upper estimates must use the same
cofinally narrow rows. Different primes may have different eventual thresholds. -/
def firstMomentRows (A : Fin 3→ℚ) (d K : ℕ) (α : ℝ) : Prop :=
  ∀ J : ℕ, ∃ j ≥ J,
    (∃ᶠ t : ℕ in atTop, let N:=lengthAt t; let W:=rowWidth j N
      α*((N:ℝ)*W) ≤ patternMass A d K K N W) ∧
    ∀p : ℕ,p.Prime → K<p → relativeUpper A d K j p

theorem hybrid_rows_of_moments {A : Fin 3→ℚ} {d K : ℕ} {α : ℝ}
    (large : 2810≤K) (pos : 0<α) (rows : firstMomentRows A d K α) (L : ℕ) :
    hybridRows A d K L (α/4) := by
  intro J
  obtain ⟨j,jJ,lower,upper⟩:=rows J
  let P:=places K L
  let e:=α/(4*((P.card:ℝ)+1))
  have ep : 0<e := by dsimp [e];positivity
  have slack : (P.card:ℝ)*e≤α/4 := by
    dsimp [e]
    have r : (0:ℝ)<P.card+1 := by positivity
    calc
      _ ≤ ((P.card:ℝ)+1)*(α/(4*(P.card+1))) :=
        mul_le_mul_of_nonneg_right (by linarith) ep.le
      _ = α/4 := by field_simp
  have collect : ∀ᶠ t : ℕ in atTop, ∀ p∈P,
      let N:=lengthAt t; let W:=rowWidth j N
      upperMoment A d K p N W ≤
        (1404/((p:ℝ)-1)^2)*patternMass A d K K N W + e*((N:ℝ)*W) :=
    (Filter.eventually_all_finset P).2 fun p hp=>upper p (mem_places.mp hp).2.2 (mem_places.mp hp).1 e ep
  refine ⟨j,jJ,(lower.and_eventually collect).mono ?_⟩
  intro t h
  exact finite_retention large h.1 h.2 slack

/-- Each fixed arithmetic base may have its own lower density. The base density
need only be positive, with no rate as the base grows. -/
def FirstMomentInputs : Prop :=
  ∀ (X c q : ℤ) (n : Fin 4→ℤ), AdmissibleRoots X c q n →
    ∀ d : ℕ, 0<d → ∀ B : ℕ, ∃ (K : ℕ) (α : ℝ),B≤K ∧ 0<α ∧
      firstMomentRows (Sun28.RealPoleBounds.fixedScale n) d K α

theorem hybrid_inputs_of_moments (inps:FirstMomentInputs) : HybridInputs := by
  intro X c q n roots d dp B
  obtain ⟨K,α,bk,pos,rows⟩:=inps X c q n roots d dp (max B 2810)
  refine ⟨K,(le_max_left _ _).trans bk,?_⟩
  intro m D
  obtain ⟨r,hr⟩:=exists_nat_gt (Real.exp (4*D/α))
  let L:=max (max K m) (max r 2)
  have rl : (r:ℝ)≤L := by exact_mod_cast (le_max_left r 2).trans (le_max_right _ _)
  have l2 : 2≤L := (le_max_right r 2).trans (le_max_right _ _)
  have lp : 1≤(L:ℝ) := by exact_mod_cast (show 1≤L by omega)
  have logpos : 0≤Real.log (L:ℝ) := Real.log_nonneg lp
  have lg := (Real.lt_log_iff_exp_lt (by linarith : 0<(L:ℝ))).2 (hr.trans_le rl)
  have lo : D < (α/4)*Real.log L := by
    have := (div_lt_iff₀ pos).1 lg
    linarith
  refine ⟨L,α/4,le_max_left _ _,by positivity,lo.trans_le ?_,
    hybrid_rows_of_moments ((le_max_right _ _).trans bk) pos rows L⟩
  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left logpos lp) (by positivity)

theorem surplus_of_moments (inps:FirstMomentInputs) (upper:PrimeUpperInputs) : PositiveSurplus :=
  hybrid_surplus (hybrid_inputs_of_moments inps) upper

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.hybrid_rows_of_moments
#print axioms Sun28.PrimeValues.hybrid_inputs_of_moments
#print axioms Sun28.PrimeValues.surplus_of_moments
