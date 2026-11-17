import SplitLoss

namespace Sun28.PrimeValues
open Finset Sun28.FinitePattern Sun28.PrimeLower Sun28.SinglePrime Sun28.ContactFactors Sun28.MixedSieve
open scoped Classical
noncomputable section

/-- The additional modulus enters through one rational residue pair at inert primes,
or two signed elliptic orders at split primes. The diagonal pairs are included. -/
def upperMoment (A : Fin 3→ℚ) (d K p N W : ℕ) : ℝ :=
  if p%4=3 then moment A d K N W (inertEvent p)
  else ∑ i : ↥(shifts A), ∑ j : ↥(shifts A), moment A d K N W (splitEvent A p i j)

theorem moment_nonneg (A : Fin 3→ℚ) (d K N W : ℕ) (P : ℕ×ℕ→Prop) :
    0 ≤ moment A d K N W P := by
  apply sum_nonneg
  intro z _
  split
  next => exact base_nonneg _ _ _
  next => exact le_rfl

private theorem union_moment {ι : Type*} [Fintype ι] (A : Fin 3→ℚ) (d K N W : ℕ)
    (E : ι → ℕ×ℕ → Prop) :
    moment A d K N W (fun z=>∃ i,E i z) ≤ ∑ i, moment A d K N W (E i) := by
  unfold moment
  rw [Finset.sum_comm (s:=univ) (t:=parameterBox d N W)]
  apply sum_le_sum
  intro z _
  have non (i:ι) (_ : i∈univ) : 0≤(if E i z then patternWeight A K K z else 0) := by
    split
    next => exact base_nonneg _ _ _
    next => exact le_rfl
  split
  next yes =>
    obtain ⟨i,ei⟩:=yes
    simpa [ei] using Finset.single_le_sum non (mem_univ i)
  next => exact sum_nonneg non

theorem single_le_upper (A : Fin 3→ℚ) (d K p N W : ℕ) :
    moment A d K N W (obstruction A p) ≤ upperMoment A d K p N W := by
  by_cases inert : p%4=3
  · have eq : obstruction A p = inertEvent p := funext fun z => by simp only [obstruction,inert,ite_true]
    rw [eq,upperMoment,ite_eq_left inert]
  · simp only [upperMoment,inert,ite_false]
    calc
      _ = moment A d K N W (fun z=>∃ i j,splitEvent A p i j z) := by
        congr 1
        funext z
        simp only [obstruction,inert,ite_false]
      _ ≤ ∑ i, moment A d K N W (fun z=>∃ j,splitEvent A p i j z) :=
        union_moment _ _ _ _ _ _
      _ ≤ _ := sum_le_sum fun i _=>union_moment _ _ _ _ _ _

/-- First Bonferroni inequality for the actual numerical weighted sample. -/
theorem finite_moments (A : Fin 3→ℚ) (d K L N W : ℕ) :
    patternMass A d K K N W - ∑ p∈places K L, upperMoment A d K p N W ≤ hybridMass A d K L N W := by
  rw [hybrid_filter]
  have keep := surviving_mass (places K L) (parameterBox d N W) (obstruction A)
    (patternWeight A K K) (fun z _=>base_nonneg _ _ _)
  have adj : patternMass A d K K N W - ∑ p∈places K L, moment A d K N W (obstruction A p) ≤
      moment A d K N W (fun z=>∀p∈places K L,¬obstruction A p z) := by
    apply keep.trans_eq
    unfold moment
    apply sum_congr rfl
    intro z _
    by_cases h : ∀p∈places K L,¬obstruction A p z <;> simp [h]
  exact (sub_le_sub_left (sum_le_sum fun p _=>single_le_upper A d K p N W) _).trans adj

theorem finite_retention {A : Fin 3→ℚ} {d K L N W : ℕ} (large : 2810≤K)
    {α ε : ℝ} (low : α*((N:ℝ)*W) ≤ patternMass A d K K N W)
    (bounds : ∀p∈places K L, upperMoment A d K p N W ≤
      (1404/((p:ℝ)-1)^2)*patternMass A d K K N W + ε*((N:ℝ)*W))
    (slack : ((places K L).card:ℝ)*ε≤α/4) :
    (α/4)*((N:ℝ)*W) ≤ hybridMass A d K L N W := by
  let P:=places K L
  let f:=fun p:ℕ=>1404/((p:ℝ)-1)^2
  let Z:ℝ:=(N:ℝ)*W
  let M:=patternMass A d K K N W
  have non : 0≤M := sum_nonneg (fun z _=>base_nonneg A K z)
  have sumf : (∑p∈P,f p)≤1/2 := uniform_sum P f
    (fun p hp=>large.trans (mem_places.mp hp).1.le) (fun _ _=>le_rfl)
  have upper : (∑p∈P,upperMoment A d K p N W)≤(1/2)*M + (α/4)*Z := calc
    _ ≤ ∑p∈P,(f p*M+ε*Z) := sum_le_sum bounds
    _ = (∑p∈P,f p)*M+((P.card:ℝ)*ε)*Z := by rw [Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_const,nsmul_eq_mul];ring
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_right sumf non)
      (mul_le_mul_of_nonneg_right slack (by dsimp [Z];positivity))
  apply le_trans _ (finite_moments A d K L N W)
  change α/4*Z ≤ M-∑p∈P,upperMoment A d K p N W
  change α*Z≤M at low
  linarith

end
end Sun28.PrimeValues
#print axioms Sun28.PrimeValues.moment_nonneg
#print axioms Sun28.PrimeValues.single_le_upper
#print axioms Sun28.PrimeValues.finite_moments
#print axioms Sun28.PrimeValues.finite_retention
