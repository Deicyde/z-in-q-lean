import LocalSelection

namespace ManuscriptV15.Arithmetic

abbrev Gaussian := ℤ × ℤ

def gaussianNorm (z : Gaussian) : ℕ := (z.1^2 + z.2^2).natAbs
def gaussianMul (z w : Gaussian) : Gaussian := (z.1*w.1-z.2*w.2,z.1*w.2+z.2*w.1)
def gaussianPrime (z : Gaussian) : Prop := gaussianNorm z > 1 ∧
  ∀ a b : Gaussian, gaussianMul a b = z → gaussianNorm a = 1 ∨ gaussianNorm b = 1
def adjacentNorm (z : Gaussian) (plus : Bool) : ℕ :=
  gaussianNorm (z.1 + (if plus then 1 else -1), z.2)
def gaussianCongruent (m : ℕ) (z w : Gaussian) : Prop :=
  Int.ModEq m z.1 w.1 ∧ Int.ModEq m z.2 w.2

def gaussianPattern {k : ℕ} (c : Fin k → ℤ) (q M u w : ℕ) (p : Fin k → ℕ) : Prop :=
  q ∣ w ∧ ∃ π : Fin k → Gaussian,
    (∀ j, (p j:ℤ) = u + c j * (w:ℤ)^2 ∧ (p j).Prime ∧
      gaussianPrime (π j) ∧ gaussianNorm (π j) = p j ∧
      gaussianCongruent 16 (π j) (9,0) ∧ gaussianCongruent 7 (π j) (1,3) ∧
      gaussianCongruent M (π j) (0,1)) ∧
    (∀ j, ∀ l : ℕ, l.Prime → Odd l → ¬ (l ∣ adjacentNorm (π j) false ∧ l ∣ adjacentNorm (π j) true)) ∧
    (∀ j h, j ≠ h → ∀ e f : Bool, ∀ l : ℕ, l.Prime → Odd l →
      ¬ (l ∣ adjacentNorm (π j) e ∧ l ∣ adjacentNorm (π h) f)) ∧
    (∀ j, padicValNat 2 (adjacentNorm (π j) false) = 6 ∧ padicValNat 2 (adjacentNorm (π j) true) = 2) ∧
    (∀ j h, Nat.gcd (adjacentNorm (π j) false) (adjacentNorm (π h) true) = 4) ∧
    (∀ j e, (adjacentNorm (π j) e).Coprime (7*M))

/-- thm:v5-simultaneous-primes. Positive u,w follow every choice of the fixed inputs. -/
def GaussianTuples : Prop := ∀ k : ℕ, 2 ≤ k → ∀ c : Fin k → ℤ, Function.Injective c →
  ∀ q M : ℕ, 0 < q → 0 < M → Odd M → squarefree M → ¬ 7 ∣ M →
  ∀ H Y : ℝ, 0 < H → 0 < Y → ∃ u w : ℕ, 0 < u ∧ 0 < w ∧ H < (u:ℝ)/w^2 ∧
  ∃ p : Fin k → ℕ, gaussianPattern c q M u w p ∧ ∀ j, Y < (p j:ℝ)

end ManuscriptV15.Arithmetic
