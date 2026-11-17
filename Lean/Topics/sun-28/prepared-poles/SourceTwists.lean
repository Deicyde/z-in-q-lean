import ZInQKernel.RouteK.Slots.Theta
import FixedData

/-! The paired-twist hypothesis with the abscissa class and the local lifting
conditions of the original three-torsion-coefficient model. -/
namespace Sun28.PreparedPoles
open ZInQ.RouteK

def LocalSquareAt (p a : ℕ) : Prop :=
  ∀ k : ℕ, ∃ t : ℤ, t^2 ≡ a [ZMOD (p:ℤ)^k]

def TwistPoint (β l : ℕ) : Prop :=
  ∃ t y : ℚ, t≠0 ∧
    (let x := (β:ℚ)*t^2; y^2=x*(x-l)*(x+3*l))

/-- The arithmetic realization in the source blueprint. The same n is used for both twists. -/
def SimultaneousTwists : Prop :=
  ∀ β θ : ℕ, 0<β → 0<θ → Squarefree β → Squarefree θ →
    β.Coprime θ → β.Coprime 6 → θ.Coprime 6 → β%24=17 → θ%24=1 →
    (∀ p : ℕ, p.Prime → p∣θ → LocalSquareAt p β) →
    (∀ p : ℕ, p.Prime → p∣β → LocalSquareAt p θ) →
    ∃ n : ℕ, 0<n ∧ Squarefree n ∧ n.Coprime (6*θ) ∧ TwistPoint β n ∧ TwistPoint β (n*θ)

def Prepared (B : ℚ) : Prop :=
  IsSquare B.den ∧ 0<B ∧ B<1/2 ∧ ∀ p∈FixedPreparation.primes, 4≤padicValRat p B

theorem prepared_admissible {B : ℚ} (h : Prepared B) : Admissible B := by
  refine ⟨h.1,h.2.1,h.2.2.1,fun p hp => h.2.2.2 p ?_⟩
  rw [ZInQ.poleS0] at hp
  rw [FixedPreparation.primes]
  simp only [Finset.mem_insert,Finset.mem_singleton] at hp ⊢
  tauto

end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.prepared_admissible
