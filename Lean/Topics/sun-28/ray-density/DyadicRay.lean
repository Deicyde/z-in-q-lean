import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Prod

set_option maxRecDepth 50000
set_option maxHeartbeats 8000000

namespace Sun28.RayDensity
open Finset

abbrev Pair (m : ℕ) := ZMod m × ZMod m

def primary (z : Pair 16) : Bool :=
  z.1.val % 2 = 1 && z.2.val % 2 = 0 && (z.1.val+z.2.val)%4=1

def turn (j : Fin 4) (z : Pair 16) : Pair 16 :=
  match j.val with
  | 0 => z
  | 1 => (-z.2,z.1)
  | 2 => (-z.1,-z.2)
  | _ => (z.2,-z.1)

def conjPair {m : ℕ} (z : Pair m) : Pair m := (z.1,-z.2)

def pairNorm {m : ℕ} (z : Pair m) := z.1^2+z.2^2

def ratioPair {m : ℕ} (e : ℕ) (z : Pair m) : Pair m :=
  ((z.1^2-z.2^2)*(pairNorm z)^e,(2*z.1*z.2)*(pairNorm z)^e)

def primarySet : Finset (Pair 16) := univ.filter fun z => primary z
def sevenUnits : Finset (Pair 7) := univ.filter fun z => pairNorm z ≠ 0

/-- Unique primary associate of every dyadic unit. -/
theorem primary_normalization : ∀ z : Pair 16, (pairNorm z).val%2=1 →
    ((univ : Finset (Fin 4)).filter fun j => primary (turn j z)).card=1 := by decide

/-- The inverse powers in the two finite rings represent division by the norm. -/
theorem base_inverse_powers :
    (∀ z ∈ primarySet, (pairNorm z)^3 * pairNorm z=1) ∧
    (∀ z ∈ sevenUnits, (pairNorm z)^5 * pairNorm z=1) := by decide

theorem base_orders :
    primarySet.card=32 ∧ sevenUnits.card=48 ∧
    (primarySet.image (ratioPair 3)).card=4 ∧ (sevenUnits.image (ratioPair 5)).card=8 := by decide

def cmCoset {m : ℕ} [NeZero m] (e : ℕ) (S : Finset (Pair m)) (w : Pair m) : Finset (Pair m) :=
  (S.image (ratioPair e)).image fun z => (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)

def baseCoset := (cmCoset 3 primarySet (9,0)).product (cmCoset 5 sevenUnits (1,3))
def baseRays : Finset (Pair 16 × Pair 7) := {((9,0),(1,3)),((9,0),(1,-3))}

/-- Exact conditional proportion at the minimal base modulus 112. -/
theorem base_coset_fraction :
    baseRays ⊆ baseCoset ∧ baseRays.card=2 ∧ baseCoset.card=32 := by decide

end Sun28.RayDensity
#print axioms Sun28.RayDensity.primary_normalization
#print axioms Sun28.RayDensity.base_inverse_powers
#print axioms Sun28.RayDensity.base_orders
#print axioms Sun28.RayDensity.base_coset_fraction
