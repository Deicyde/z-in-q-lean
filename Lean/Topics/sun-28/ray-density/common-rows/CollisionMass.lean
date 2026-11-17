import SignedRows

namespace Sun28.CommonRows
open Finset Filter Sun28.PrimeValues Sun28.FinitePattern Sun28.PrimeClasses
open Sun28.PrimeLower Sun28.ContactFactors Sun28.ContactSieve Sun28.WeightedSelection
open Sun28.SinglePrime Sun28.MediumSieve Sun28.MixedSieve Sun28.PrimeMass
open scoped Classical
noncomputable section

def collisions (A : Fin 3→ℚ) (K L:ℕ) (z:ℕ×ℕ) : ℕ :=
  ((places K L).filter fun p=>signedHit A p z).card

def onePlaceMass (A : Fin 3→ℚ) (d K N W p:ℕ) : ℝ := moment A d K N W (signedHit A p)

def multipleMass (A : Fin 3→ℚ) (d K L N W:ℕ) : ℝ :=
  ∑z∈parameterBox d N W, ((collisions A K L z-1:ℕ):ℝ)*patternWeight A K K z

def cleanMass (A : Fin 3→ℚ) (d K L N W:ℕ) : ℝ :=
  moment A d K N W (fun z=>collisions A K L z=0)

theorem no_collision {A : Fin 3→ℚ} {K L:ℕ} {z:ℕ×ℕ} :
    collisions A K L z=0 ↔ ∀p∈places K L,¬signedHit A p z := by
  simp [collisions,Finset.filter_eq_empty_iff]

/-- Subtract each obstruction prime once. If a row fails at m primes, add back
exactly m−1 copies of its logarithmic weight. This identity needs no independence. -/
theorem clean_mass (A : Fin 3→ℚ) (d K L N W:ℕ) :
    cleanMass A d K L N W = patternMass A d K K N W -
      ∑p∈places K L,onePlaceMass A d K N W p + multipleMass A d K L N W := by
  unfold cleanMass multipleMass onePlaceMass moment patternMass
  rw [sum_comm (s:=places K L) (t:=parameterBox d N W)]
  change (∑z∈parameterBox d N W,_) = (∑z∈parameterBox d N W,_) - (∑z∈parameterBox d N W,_) + _
  rw [←sum_sub_distrib,←sum_add_distrib]
  apply sum_congr rfl
  intro z _
  let m:=collisions A K L z
  let w:=patternWeight A K K z
  have count : (∑p∈places K L,if signedHit A p z then w else 0)=(m:ℝ)*w := by
    rw [←sum_filter, sum_const, nsmul_eq_mul];rfl
  rw [count]
  change (@ite ℝ (m=0) (Classical.propDecidable _) w 0) = w - (m:ℝ)*w + ((m-1:ℕ):ℝ)*w
  by_cases yes : m=0
  · rw [ite_eq_left yes,yes];simp
  · rw [ite_eq_right yes,Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr yes),Nat.cast_one];ring

theorem clean_ge_first (A : Fin 3→ℚ) (d K L N W:ℕ) :
    patternMass A d K K N W-∑p∈places K L,onePlaceMass A d K N W p ≤ cleanMass A d K L N W := by
  rw [clean_mass]
  apply le_add_of_nonneg_right
  apply sum_nonneg
  intro z _
  exact mul_nonneg (Nat.cast_nonneg _) (base_nonneg A K z)

/-- The overlap correction can be lower-bounded by a single weighted
intersection, with no third-moment penalty: use at most one link per row. -/
theorem intersection_le_multiple {A : Fin 3→ℚ} {d K L N W p q:ℕ}
    (hp:p∈places K L) (hq:q∈places K L) (distinct:p≠q) :
    moment A d K N W (fun z=>signedHit A p z ∧ signedHit A q z) ≤
    multipleMass A d K L N W := by
  apply sum_le_sum
  intro z _
  by_cases good:signedHit A p z ∧ signedHit A q z
  · rw [ite_eq_left good]
    have h : ({p,q}:Finset ℕ) ⊆ (places K L).filter (fun t=>signedHit A t z) := by
      intro t ht
      rcases mem_insert.mp ht with rfl|other
      · exact mem_filter.mpr ⟨hp,good.1⟩
      · have := mem_singleton.mp other;subst t;exact mem_filter.mpr ⟨hq,good.2⟩
    have size:=card_le_card h
    simp [distinct] at size
    have cnt : 1≤collisions A K L z-1 := by dsimp [collisions];omega
    exact le_mul_of_one_le_left (base_nonneg A K z) (by exact_mod_cast cnt)
  · rw [ite_eq_right good]
    exact mul_nonneg (Nat.cast_nonneg _) (base_nonneg A K z)

end
end Sun28.CommonRows
#print axioms Sun28.CommonRows.no_collision
#print axioms Sun28.CommonRows.clean_mass
#print axioms Sun28.CommonRows.clean_ge_first
#print axioms Sun28.CommonRows.intersection_le_multiple