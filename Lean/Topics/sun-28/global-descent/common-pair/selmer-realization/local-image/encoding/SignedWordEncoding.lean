import LocalSymbols
import SignedPrimeFactorization
import Mathlib.Tactic.NormNum.Prime

namespace Sun28.FixedLocalRows.WordEncoding

set_option maxRecDepth 4096

/-- The low bit records negativity; the next nine bits mark the distinct prime divisors. -/
def blockBits (z : ℤ) : List Bool :=
  decide (z < 0) :: primes.map (fun p => decide (p ∈ z.natAbs.primeFactors))

/-- The first block encodes the class of x+3n, and the second the class of x−n. -/
def encode (a b : ℤ) : Word := BitVec.ofBoolListLE (blockBits a ++ blockBits b)

/-- Lookup in the actual word, including indices outside its twenty-bit extent. -/
theorem encode_bits (a b : ℤ) (i : ℕ) :
    (encode a b).getLsbD i = (blockBits a ++ blockBits b).getD i false :=
  BitVec.getLsbD_ofBoolListLE

/-- Read the two sign bits directly. -/
theorem encode_sign_bits (a b : ℤ) :
    (encode a b).getLsbD 0 = decide (a < 0) ∧
    (encode a b).getLsbD 10 = decide (b < 0) := by
  rw [encode_bits, encode_bits]
  constructor <;> rfl

/-- At the same prime index, the two blocks mark divisibility of the two
squarefree integers independently. -/
theorem encode_prime_bits {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (j : Fin 9) :
    (encode a b).getLsbD (j.val + 1) = decide (((primes[j.val]'(by exact j.isLt) : ℕ) : ℤ) ∣ a) ∧
    (encode a b).getLsbD (j.val + 11) = decide (((primes[j.val]'(by exact j.isLt) : ℕ) : ℤ) ∣ b) := by
  have atIndex (z : ℤ) (hz : Squarefree z) (p : ℕ) (hp : p.Prime) :
      decide (p ∈ z.natAbs.primeFactors) = decide ((p : ℤ) ∣ z) := by
    have hne : z.natAbs ≠ 0 := (Int.squarefree_natAbs.mpr hz).ne_zero
    simp [Nat.mem_primeFactors, hp, hne, Int.natCast_dvd]
  have bits : (encode a b).getLsbD (j.val + 1) =
      decide (primes[j.val]'(by exact j.isLt) ∈ a.natAbs.primeFactors) ∧
      (encode a b).getLsbD (j.val + 11) =
      decide (primes[j.val]'(by exact j.isLt) ∈ b.natAbs.primeFactors) := by
    rw [encode_bits, encode_bits]
    fin_cases j <;> constructor <;> rfl
  have prime : (primes[j.val]'(by exact j.isLt)).Prime := by
    fin_cases j <;> norm_num [primes]
  exact ⟨bits.1.trans (atIndex a ha _ prime), bits.2.trans (atIndex b hb _ prime)⟩

/-- The literal label table multiplies the selected factors in each signed block. -/
theorem labels_encode_products (a b : ℤ) :
    labels (encode a b) = (signedProduct a, signedProduct b) := by
  unfold labels
  simp only [generatorProduct, encode_bits]
  rfl

/-- Every pair of supported signed squarefree representatives is represented by its word. -/
theorem labels_encode {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (sa : Supported a) (sb : Supported b) :
    labels (encode a b) = (a,b) := by
  rw [labels_encode_products, signedProduct_eq ha sa, signedProduct_eq hb sb]

theorem exists_word {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (sa : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a → p ∈ primes)
    (sb : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → p ∈ primes) :
    ∃ v : Word, labels v = (a,b) :=
  ⟨encode a b, labels_encode ha hb (supported_of_prime_divisors sa)
    (supported_of_prime_divisors sb)⟩

end Sun28.FixedLocalRows.WordEncoding

#print axioms Sun28.FixedLocalRows.WordEncoding.encode_bits
#print axioms Sun28.FixedLocalRows.WordEncoding.encode_sign_bits
#print axioms Sun28.FixedLocalRows.WordEncoding.encode_prime_bits
#print axioms Sun28.FixedLocalRows.WordEncoding.labels_encode_products
#print axioms Sun28.FixedLocalRows.WordEncoding.labels_encode
#print axioms Sun28.FixedLocalRows.WordEncoding.exists_word
