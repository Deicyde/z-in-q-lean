import BalancedHeight

namespace Sun28.HeightBalance
open Sun28.Ordinary Sun28.FiveMarkUnits Sun28.MinimalConductors Sun28.HeightFibres Height
open Sun28.HeightExtension Sun28.HeightExtension.SquareSupport Sun28.HeightBudget Sun28.HeightFibres.Sharp
noncomputable section

/-- Any choice of center, and any three of the remaining four rows. -/
def Covered (A B : ℤ) : Prop :=
  ∃ (R : FourRows) (d u v w : ℤ), R.Balance A B d u v w ∧
    primeProduct (R.primes A B) ≤ heightRadical A B^23

theorem five_height_of_balance (units : PublishedCorollary72) {A B : ℤ}
    (cop : Int.gcd A B=1) (off : ∀ i,oldForm i A B≠0) (cover : Covered A B) : target A B := by
  obtain ⟨R,d,u,v,w,h,small⟩:=cover
  let T:ℝ:=heightRadical A B
  let N:=primeProduct (R.primes A B)
  have one : 1≤T:=Nat.one_le_cast.mpr (Nat.mul_pos pos_cutoff (pos_odd A B))
  have np : 1≤(N:ℝ):=Nat.one_le_cast.mpr (Finset.prod_pos (fun _ hp=>(R.primes_prime A B hp).pos))
  have base:=R.height units cop off h
  change pairLogHeight A B≤6*FourRows.heightBound N+36 at base
  have absorb:=analytic_absorption np one (show (N:ℝ)≤T^23 by dsimp only [N,T];exact_mod_cast small)
  change FourRows.heightBound N≤(192*53^2)*T^24+65 at absorb
  have modest : pairLogHeight A B≤2^23*T^24:=by
    linarith only [base,absorb,one_le_pow₀ one (n:=24)]
  have room:2^23*T^24≤2^810*T^24:=mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (by decide : 23≤810)) (by positivity)
  simpa only [target,oddProduct,oddSupport,primeProduct,Nat.cast_prod] using
    (modest.trans room).trans (original_margin A B)

def Residual : Prop :=
  ∀ A B : ℤ,Int.gcd A B=1 → (∀ i,oldForm i A B≠0) →
    (∀ i,¬SparseRepeated i A B) →
    glazerConstant24*(oddProduct A B:ℝ)^24<vonKanelBound (best A B) →
    (∀ i b c,¬HeightRefinement.Sharp.Test i A B b c) → ¬Covered A B → target A B

theorem original_iff_balance (units : PublishedCorollary72) (pell : PublishedAllPell)
    (classes : PublishedClassRegulator) (formula : QuadraticCharacterDiscriminants) :
    OriginalFiveHeight glazerConstant24 oldCutoff ↔ Residual := by
  constructor
  · exact fun full A B cop off _ _ _ _ => full A B cop off
  · intro remaining
    apply (HeightRefinement.Sharp.original_iff_sharp units pell classes formula).mpr
    intro A B cop off sparse least failures
    by_cases yes : Covered A B
    · exact five_height_of_balance units cop off yes
    · exact remaining A B cop off sparse least failures yes

end
end Sun28.HeightBalance
#print axioms Sun28.HeightBalance.five_height_of_balance
#print axioms Sun28.HeightBalance.original_iff_balance
