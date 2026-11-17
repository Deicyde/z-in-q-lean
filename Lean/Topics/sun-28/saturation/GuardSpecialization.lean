import GuardFamilies
import Mathlib.RingTheory.Localization.FractionRing

/-! Why a symbolic compiler must separate gcd specializations. -/
open Polynomial
namespace Sun28.Guard

/-- The family with seed T and guard T-a has a generic surviving root zero and loses
that root at a=0. Evaluating a generic retained polynomial at all parameters would fail. -/
theorem changing_guard {K : Type*} [Field K] [DecidableEq K] (a : K) :
    (fibre (evalRingHom a) (X : K[X][X]) [] [X-C (X : K[X])]).IsRoot 0 ↔ a≠0 := by
  rw [isRoot_fibre]
  · simp
  · simp

/-- Keeping the polynomial on the generic field and specializing at zero need not commute,
already for a monic linear seed and one guard. -/
theorem generic_root_lost (K : Type*) [Field K] [DecidableEq K]
    [DecidableEq (FractionRing K[X])] :
    (fibre (algebraMap K[X] (FractionRing K[X])) (X : K[X][X]) [] [X-C (X : K[X])]).IsRoot 0 ∧
    ¬(fibre (evalRingHom (0:K)) (X : K[X][X]) [] [X-C (X : K[X])]).IsRoot 0 := by
  constructor
  · rw [isRoot_fibre]
    · simp
    · simp
  · simpa using (changing_guard (0:K)).not

#print axioms changing_guard
#print axioms generic_root_lost
end Sun28.Guard
