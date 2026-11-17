import ScalarHeight
import Mathlib.Algebra.BigOperators.Associated

/-! A bounded multiplier list for the local square-class conditions at infinity, 2 and 3. -/
open Sun28.Ordinary
namespace Sun28.ScalarHeight

def representatives (i : Fin 8) : ℕ := ![1,5,7,11,13,17,19,23] i

def shift (neg a b : Bool) (i : Fin 8) : ℤ :=
  (if neg then -1 else 1)*(if a then 2 else 1)*(if b then 3 else 1)*representatives i

def smallMultipliers : Finset ℚ :=
  (Finset.univ : Finset (Bool × Bool × Bool × Fin 8)).image
    fun ⟨neg,a,b,i⟩ => (shift neg a b i:ℚ)

/-- After removing the factor of 2, respectively 3, the indicated odd-prime
units cover every pair of unit residues for each choice of sign and parities. -/
theorem multiplier_residues (neg a b : Bool) (z : Fin 8) (w : Fin 3)
    (zodd : z.val%2=1) (wn : w.val≠0) :
    ∃ i : Fin 8, ((if neg then 7 else 1)*(if b then 3 else 1)*representatives i)%8=z.val ∧
      ((if neg then 2 else 1)*(if a then 2 else 1)*representatives i)%3=w.val := by
  revert neg a b z w
  decide

theorem small_support : ∀ μ∈smallMultipliers, support μ ⊆ oldCutoff := by
  intro μ mem p hp
  obtain ⟨⟨neg,a,b,i⟩,_,rfl⟩ := Finset.mem_image.mp mem
  have eq (n : ℤ) : support (n:ℚ)=n.natAbs.primeFactors := by simp [support]
  rw [eq] at hp
  obtain ⟨prime,dvd,nz⟩ := Nat.mem_primeFactors.mp hp
  have allBounded : ∀ (n a b : Bool) (j : Fin 8), (shift n a b j).natAbs≤138 := by decide
  have bounded := allBounded neg a b i
  have z := Nat.le_of_dvd (Nat.pos_of_ne_zero nz) dvd
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),prime⟩

def preparationPrimes (M : Finset ℚ) : Finset ℕ := {2,3} ∪ M.biUnion support

def preparationGamma (M : Finset ℚ) (N : ℕ) : ℕ := (∏ p ∈ preparationPrimes M,p)^N

theorem preparationGamma_support (M : Finset ℚ) (N : ℕ)
    (small : ∀ μ∈M,support μ ⊆ oldCutoff) : support (preparationGamma M N : ℚ)⊆oldCutoff := by
  intro p hp
  have eq (n : ℕ) : support (n:ℚ)=n.primeFactors := by simp [support]
  rw [eq] at hp
  obtain ⟨prime,dvd,_⟩ := Nat.mem_primeFactors.mp hp
  have divides := prime.dvd_of_dvd_pow dvd
  obtain ⟨q,mem,d⟩ := (Prime.dvd_finsetProd_iff (S:=preparationPrimes M) prime.prime (fun n : ℕ => n)).mp divides
  have smallq : q≤76176 := by
    rcases Finset.mem_union.mp mem with two|many
    · simp only [Finset.mem_insert,Finset.mem_singleton] at two
      omega
    · obtain ⟨μ,hm,hq⟩ := Finset.mem_biUnion.mp many
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp (small μ hm hq)).1)
  have qpos : 0<q := by
    rcases Finset.mem_union.mp mem with two|many
    · simp only [Finset.mem_insert,Finset.mem_singleton] at two; omega
    · obtain ⟨μ,hm,hq⟩ := Finset.mem_biUnion.mp many
      exact (Finset.mem_filter.mp (small μ hm hq)).2.pos
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by have le := Nat.le_of_dvd qpos d; omega),prime⟩

/-- Sun's choice of Gamma from S₀ adds no factors to the original height coefficient. -/
theorem concrete_scalar_constant (N : ℕ) :
    scalarConstant (preparationGamma smallMultipliers N) smallMultipliers=glazerConstant24 :=
  scalarConstant_eq_of_small (preparationGamma_support _ N small_support) small_support

private theorem gamma_nonzero (M : Finset ℚ) (N : ℕ) (small : ∀ μ∈M,support μ ⊆ oldCutoff) :
    preparationGamma M N≠0 := by
  unfold preparationGamma
  apply pow_ne_zero
  apply Finset.prod_ne_zero_iff.mpr
  intro q mem
  change q∈({2,3}:Finset ℕ) ∪ M.biUnion support at mem
  rcases Finset.mem_union.mp mem with two|u
  · simp only [Finset.mem_insert,Finset.mem_singleton] at two; omega
  · obtain ⟨μ,hm,hq⟩ := Finset.mem_biUnion.mp u
    exact (Finset.mem_filter.mp (small μ hm hq)).2.ne_zero

open NumberField Sun28.Scalar Height
open scoped NumberField

theorem scalar_sqrt_height_at_original_constant {K : Type*} [Field K] [NumberField K] [DecidableEq K]
    [Algebra.IsQuadraticExtension ℚ K] {ρ : K} (root : ρ^2=2) (h s : ℤ) (x : ℚ) (D N : ℕ)
    (hh : h≠0) (classicalInputs : LocalCharts (exceptional (preparationGamma smallMultipliers N) smallMultipliers) K)
    (upstream : OriginalFiveHeight glazerConstant24 oldCutoff) (guard : (s-1) • paperGenerator root≠0)
    (accept : TreeCertificate root h s (scalarRadicand (beta x)) (preparationGamma smallMultipliers N) D smallMultipliers ∨
      TraceCertificate root h s (scalarRadicand (beta x)) (preparationGamma smallMultipliers N) D smallMultipliers) :
    logHeight₁ (beta x) ≤ glazerConstant24*Real.sqrt |((s-1:ℤ):ℝ)| := by
  have nz := gamma_nonzero smallMultipliers N small_support
  simpa only [concrete_scalar_constant] using scalar_sqrt_height root h s x _ D smallMultipliers hh
    (by exact_mod_cast nz) classicalInputs upstream guard accept

end Sun28.ScalarHeight
#print axioms Sun28.ScalarHeight.multiplier_residues
#print axioms Sun28.ScalarHeight.small_support
#print axioms Sun28.ScalarHeight.preparationGamma_support
#print axioms Sun28.ScalarHeight.concrete_scalar_constant
#print axioms Sun28.ScalarHeight.scalar_sqrt_height_at_original_constant
