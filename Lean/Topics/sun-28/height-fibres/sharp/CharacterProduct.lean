import CharacterField

/-! The three quadratic character supports at odd valuation; primes including
two are counted through their parity here and the dyadic factor is separate. -/
namespace Sun28.HeightFibres.Sharp
open Sun28.FiveMarkUnits
noncomputable section

def parityPrimes (S : Finset ℕ) (a b : ℤ) :=
  S.filter fun p => Odd (padicValInt p a+padicValInt p b)

/-- A prime occurs in either zero or two of the three squareclasses.
Multiplication gives the square of the common prime product as an upper bound. -/
theorem character_product (S : Finset ℕ) (pr : ∀ p∈S,p.Prime) (g h k : ℤ) :
    primeProduct (parityPrimes S g h)*primeProduct (parityPrimes S g k)*
    primeProduct (parityPrimes S h k) ≤ (primeProduct S)^2 := by
  classical
  simp only [primeProduct,parityPrimes,Finset.prod_filter,←Finset.prod_mul_distrib,←Finset.prod_pow]
  apply Finset.prod_le_prod
  intro p hp
  have pos : 1≤p := (pr p hp).pos
  have pair {a b : ℕ} : Odd (a+b) ↔ a%2≠b%2 := by
    rw [Nat.odd_iff];omega
  simp only [pair]
  rcases Nat.mod_two_eq_zero_or_one (padicValInt p g) with ga|ga <;>
    rcases Nat.mod_two_eq_zero_or_one (padicValInt p h) with ha|ha <;>
    rcases Nat.mod_two_eq_zero_or_one (padicValInt p k) with ka|ka <;>
    simp [ga,ha,ka,pow_two] <;> nlinarith

/-- The product of the three quadratic fundamental discriminant bounds.
For nonzero integers a,b, parityPrimes gives the support of the signed
squarefree representative of ab under the stipulated support containments.
Each quadratic fundamental discriminant contributes at most one factor four.
It also bounds the degree-one and degree-two degenerations. -/
def QuadraticCharacterDiscriminants : Prop :=
  ∀ (S : Finset ℕ) (g h k : ℤ) (r w : Omega), (∀ p∈S,p.Prime) → g≠0 → h≠0 → k≠0 →
    g.natAbs.primeFactors⊆S → h.natAbs.primeFactors⊆S → k.natAbs.primeFactors⊆S →
    r^2=(g:Omega)*h → w^2=(g:Omega)*k →
    (NumberField.discr (IntermediateField.adjoin ℚ ({r,w} : Set Omega))).natAbs ≤
      64*(primeProduct (parityPrimes S g h)*primeProduct (parityPrimes S g k)*primeProduct (parityPrimes S h k))

theorem conductor_from_characters (formula : QuadraticCharacterDiscriminants) : ConductorDiscriminants := by
  intro S g h k r w pr ng nh nk gs hs ks hr hw
  exact (formula S g h k r w pr ng nh nk gs hs ks hr hw).trans (Nat.mul_le_mul_left _ (character_product S pr g h k))

end
end Sun28.HeightFibres.Sharp
#print axioms Sun28.HeightFibres.Sharp.character_product
#print axioms Sun28.HeightFibres.Sharp.conductor_from_characters
