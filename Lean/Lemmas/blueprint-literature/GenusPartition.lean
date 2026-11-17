import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Exact finite sets and the row-5b matrix for the TYZ odd genus term.
The equality of their values is a named work package, not an axiom. -/
namespace ZInQBlueprint.Rank

noncomputable section
open scoped BigOperators NumberField
open Matrix

abbrev Qbar := AlgebraicClosure ℚ

/-- A selected root of X²+d in the algebraic closure of the rationals. -/
def sqrtMinus (d : ℕ) : Qbar :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (-(d : Qbar)) zero_lt_two)

theorem sqrtMinus_sq (d : ℕ) : sqrtMinus d ^ 2 = -(d : Qbar) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (-(d : Qbar)) zero_lt_two)

/-- The field Q(√−d). Changing the choice of the square root leaves this subfield unchanged. -/
def imaginaryField (d : ℕ) : IntermediateField ℚ Qbar :=
  IntermediateField.adjoin ℚ {sqrtMinus d}

instance (d : ℕ) : NumberField (imaginaryField d) := by
  haveI : FiniteDimensional ℚ (imaginaryField d) :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (R := ℚ) (sqrtMinus d))
  exact NumberField.of_module_finite ℚ (imaginaryField d)

/-- TYZ's g(d) is the order of the subgroup of squares in the ideal class group. -/
def genusSize (d : ℕ) : ℕ := by
  classical
  let G := ClassGroup (𝓞 (imaginaryField d))
  exact (Finset.univ.filter (fun c : G => IsSquare c)).card

/-- Product of the distinct primes in one block. -/
def blockProduct (b : Finset ℕ) : ℕ := ∏ p ∈ b, p

/-- Each object is an unordered partition of the exact prime divisors of n.
Exactly one block has product 7 and one has product 3 modulo 8; every other
block has product 1. Nonempty blocks are disjoint as sets of primes. -/
def genusPartitions (n : ℕ) : Finset (Finset (Finset ℕ)) := by
  classical
  exact n.primeFactors.powerset.powerset.filter fun blocks =>
    (∀ b ∈ blocks, b.Nonempty) ∧
    (blocks.biUnion id = n.primeFactors) ∧
    (∀ b ∈ blocks, ∀ c ∈ blocks, b ≠ c → Disjoint b c) ∧
    (blocks.filter (fun b => blockProduct b % 8 = 7)).card = 1 ∧
    (blocks.filter (fun b => blockProduct b % 8 = 3)).card = 1 ∧
    (∀ b ∈ blocks, blockProduct b % 8 ∈ ({1,3,7} : Finset ℕ))

/-- The unordered (7,3) coefficient, as an actual natural-number sum. -/
def genusSum (n : ℕ) : ℕ :=
  ∑ partition ∈ genusPartitions n, ∏ b ∈ partition, genusSize (blockProduct b)

/-- The additive Legendre bit convention of Rank5b/Matrices.lean at 6f20b15. -/
def legBit (p : ℕ) (a : ℤ) : ZMod 2 := by
  classical
  exact if IsSquare (a : ZMod p) then 0 else 1

def laplacian (n : ℕ) : Matrix n.primeFactors n.primeFactors (ZMod 2) := by
  classical
  exact fun i j => if i = j then
    ∑ k ∈ Finset.univ.erase i, legBit i.val (k.val : ℤ)
  else legBit i.val (j.val : ℤ)

def smithM1 (n : ℕ) :
    Matrix (n.primeFactors ⊕ n.primeFactors) (n.primeFactors ⊕ n.primeFactors) (ZMod 2) :=
  Matrix.fromBlocks (laplacian n + (laplacian n)ᵀ) (laplacian n)ᵀ (laplacian n)
    (Matrix.diagonal (fun i => legBit i.val 2))

def smithM5b (n : ℕ) :
    Matrix ((n.primeFactors ⊕ n.primeFactors) ⊕ Unit)
      ((n.primeFactors ⊕ n.primeFactors) ⊕ Unit) (ZMod 2) :=
  let w : (n.primeFactors ⊕ n.primeFactors) → ZMod 2 :=
    Sum.elim (fun _ => 0) (fun p => legBit p.val (-1))
  Matrix.fromBlocks (smithM1 n) (Matrix.replicateCol Unit w) (Matrix.replicateRow Unit w) 0

/-- Project's determinant/forest/genus comparison (tyz-5b, Theorem 3.6).
Its proof is a separate work package. -/
def DeterminantGenusComparison : Prop :=
  ∀ n : ℕ, n % 8 = 5 → Squarefree n → (smithM5b n).det = (genusSum n : ZMod 2)

end
end ZInQBlueprint.Rank
