import ConeDenominator
import FactorialCost
import Mathlib.NumberTheory.Harmonic.Bounds

namespace Sun28.RayDensity
open Finset Sun28.ConeSieve
noncomputable section

/-- An upper Mertens inequality with an explicit constant, obtained by first-moment truncation. -/
theorem squarefree_product {L : ℕ} (large : 2≤L) (P : Finset ℕ)
    (primes : ∀ p∈P,p.Prime ∧ p≤L) :
    (∏ p∈P,(1+(p:ℝ)⁻¹)) ≤ 2*(1+4*Real.log L) := by
  classical
  let g : ℕ → ℝ := fun p => 1/((p:ℝ)+1)
  let z := L^4
  let f := fun r : Finset ℕ => ∏ p∈r,p
  have pos (p : ℕ) (hp : p∈P) : 0<(p:ℝ) := by exact_mod_cast (primes p hp).1.pos
  have odd (p : ℕ) (hp : p∈P) : odds g p=(p:ℝ)⁻¹ := by
    have pp := pos p hp
    dsimp [odds,g]
    field_simp [pp.ne']
    ring
  have mean : (∑ p∈P,g p*Real.log p) ≤ ∑ p∈P,Real.log (p:ℝ)/p := by
    apply sum_le_sum
    intro p hp
    have pp:=pos p hp
    have nn:=Real.log_nonneg (by exact_mod_cast (primes p hp).1.one_le : 1≤(p:ℝ))
    dsimp [g]
    rw [one_div,inv_mul_eq_div]
    exact div_le_div_of_nonneg_left nn pp (by linarith)
  have lg : Real.log (z:ℝ)=4*Real.log L := by simp [z,Real.log_pow]
  have half := half_euler_product P g z (by exact one_lt_pow₀ (show 1<L by omega) (by decide))
    (fun p h=>(primes p h).1) (fun p h=>by
      have pp:=pos p h
      dsimp [g]
      exact ⟨by positivity,(div_lt_one (by linarith)).mpr (by linarith)⟩)
    (by rw [lg];linarith only [mean,Sun28.FinitePattern.factorial_prime_sum (by omega : 0<L) P primes])
  have good {r : Finset ℕ} (hr : r∈index P z) (p : ℕ) (hp : p∈r) : p.Prime :=
    (primes p (mem_powerset.mp (mem_filter.mp hr).1 hp)).1
  have inj : Set.InjOn f (↑(index P z)) := by
    intro r hr s hs eq
    have e:=congrArg Nat.primeFactors eq
    simpa [f,Nat.primeFactors_prod (good hr),Nat.primeFactors_prod (good hs)] using e
  have sub : (index P z).image f ⊆ Icc 1 z := by
    intro d hd
    obtain ⟨r,hr,rfl⟩ := mem_image.mp hd
    exact mem_Icc.mpr ⟨(show 0<f r from prod_pos (fun p hp=>(good hr p hp).pos)),(mem_filter.mp hr).2⟩
  have cost : denominator g (index P z)≤harmonic z := by
    unfold denominator
    rw [harmonic_eq_sum_Icc]
    push_cast
    calc _ = ∑ r∈index P z,((f r:ℕ):ℝ)⁻¹ := by
           apply sum_congr rfl;intro r hr
           dsimp [f];rw [Nat.cast_prod,←prod_inv_distrib]
           exact prod_congr rfl (fun p h=>odd p (mem_powerset.mp (mem_filter.mp hr).1 h))
         _ = ∑ m∈(index P z).image f,(m:ℝ)⁻¹ := (sum_image (f:=fun m : ℕ => (m:ℝ)⁻¹) inj).symm
         _ ≤ _ := sum_le_sum_of_subset_of_nonneg sub (fun m _ _ => by positivity)
  have eq : (∏ p∈P,(1+odds g p))=∏ p∈P,(1+(p:ℝ)⁻¹) := prod_congr rfl fun p h=>by rw [odd p h]
  rw [eq] at half
  have lim:=harmonic_le_one_add_log z
  rw [lg] at lim
  linarith

end
end Sun28.RayDensity
#print axioms Sun28.RayDensity.squarefree_product
