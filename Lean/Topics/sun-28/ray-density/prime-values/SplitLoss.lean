import HybridCount
import PrimeClassRays

namespace Sun28.PrimeValues
open Finset Sun28.FinitePattern Sun28.PrimeLower Sun28.PrimeClasses Sun28.SinglePrime Sun28.ContactFactors
open ManuscriptV15.Arithmetic
open scoped Classical
noncomputable section

abbrev parameterBox (d N W : ℕ) :=
  (Ioc (N/2) N ×ˢ Icc 1 W).filter (fun z : ℕ×ℕ => d∣z.2)

def splitEvent (A : Fin 3→ℚ) (p : ℕ) (i j : ↥(shifts A)) (z : ℕ×ℕ) : Prop :=
  (p:ℤ) ∣ signedOrder (form A z i).toNat true ∧ (p:ℤ) ∣ signedOrder (form A z j).toNat false

def inertEvent (p : ℕ) (z : ℕ×ℕ) : Prop := (z.1 : ZMod p)=1 ∧ (z.2 : ZMod p)=0

def obstruction (A : Fin 3→ℚ) (p : ℕ) (z : ℕ×ℕ) : Prop :=
  if p%4=3 then inertEvent p z else ∃ i j : ↥(shifts A),splitEvent A p i j z

theorem live_test {A : Fin 3→ℚ} {K L : ℕ} {z : ℕ×ℕ} (live:patternWeight A K K z≠0) :
    extraTest A K L z ↔ ∀p∈places K L,¬obstruction A p z := by
  have good (i : ↥(shifts A)) : 0≤form A z i ∧ commonPrime K K (form A z i).toNat := by
    by_contra h
    exact live (Finset.prod_eq_zero (f:=fun j : ↥(shifts A)=>primeWeight K K (form A z j))
      (Finset.mem_univ i) (ite_eq_right h))
  let π (i : ↥(shifts A)) := (good i).2.2.choose
  have req (i : ↥(shifts A)) := (good i).2.2.choose_spec
  have iff_order (i : ↥(shifts A)) (p:ℕ) (sgn:Bool) :
      p∣adjacentNorm (π i) sgn ↔ (p:ℤ) ∣ signedOrder (form A z i).toNat sgn :=
    order_dvd_iff (good i).2.1 (req i).1 (req i).2.1 (req i).2.2.1 sgn p
  have sep (p:ℕ) :
      ((∀ i,¬p∣adjacentNorm (π i) true) ∨ (∀ j,¬p∣adjacentNorm (π j) false)) ↔
        ¬∃ i j,splitEvent A p i j z := by
    simp_rw [iff_order]
    unfold splitEvent
    constructor
    · rintro (a|b) ⟨i,j,hi,hj⟩
      · exact a i hi
      · exact b j hj
    · intro none
      by_cases all : ∀ i : ↥(shifts A),¬(p:ℤ)∣signedOrder (form A z i).toNat true
      · exact Or.inl all
      · push Not at all
        obtain ⟨i,hi⟩:=all
        exact Or.inr fun j hj=>none ⟨i,j,hi,hj⟩
  constructor
  · rintro ⟨w,ws,added⟩ p hp
    have same : w=π := funext fun i=> oriented_unique (good i).2.1 (ws i).1 (req i).1
      (ws i).2.1 (req i).2.1 (ws i).2.2 (req i).2.2.1
    rw [same] at added
    obtain ⟨lo,hi,pr⟩:=mem_places.mp hp
    have atp:=added p pr lo hi
    by_cases inert : p%4=3
    · simpa [obstruction,inertEvent,inert] using atp
    · simpa [obstruction,inert] using (sep p).1 (by simpa [inert] using atp)
  · intro h
    refine ⟨π,fun i=>⟨(req i).1,(req i).2.1,(req i).2.2.1⟩,?_⟩
    intro p pr lo hi
    have atp:=h p (mem_places.mpr ⟨lo,hi,pr⟩)
    by_cases inert : p%4=3
    · simpa [obstruction,inertEvent,inert] using atp
    · simpa [inert] using (sep p).2 (by simpa [obstruction,inert] using atp)

/-- A restricted moment still uses all k primality and fixed-base tests. -/
def moment (A : Fin 3→ℚ) (d K N W : ℕ) (P : ℕ×ℕ → Prop) : ℝ :=
  ∑ z ∈ parameterBox d N W, if P z then patternWeight A K K z else 0

theorem base_nonneg (A : Fin 3→ℚ) (K : ℕ) (z : ℕ×ℕ) : 0 ≤ patternWeight A K K z := by
  apply Finset.prod_nonneg
  intro i _
  unfold primeWeight
  split
  next h => exact Real.log_nonneg (by exact_mod_cast h.2.1.one_le)
  next => exact le_rfl

theorem hybrid_filter (A : Fin 3→ℚ) (d K L N W : ℕ) :
    hybridMass A d K L N W = moment A d K N W (fun z=>∀p∈places K L,¬obstruction A p z) := by
  apply Finset.sum_congr rfl
  intro z _
  unfold hybridWeight
  by_cases live : patternWeight A K K z=0
  · simp [live]
  · rw [live_test live]

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.live_test
#print axioms Sun28.PrimeValues.base_nonneg
#print axioms Sun28.PrimeValues.hybrid_filter
