import IntegerProjection

/-! Four definitions transcribed from the archived manuscript blueprint. -/
namespace ManuscriptV15.Arithmetic

def squarefree (a : ℕ) : Prop := ∀ p : ℕ, p.Prime → ¬ p^2 ∣ a

def localSquareAt (p a : ℕ) : Prop := ∀ k : ℕ, ∃ t : ℤ, Int.ModEq ((p:ℤ)^k) (t^2) a

def twistPointInClass (β l : ℕ) : Prop := ∃ t y : ℚ, t ≠ 0 ∧
  let x := β*t^2
  y^2 = x*(x-l)*(x+3*l)

def SimultaneousTwists : Prop := ∀ β θ : ℕ, 0 < β → 0 < θ → squarefree β → squarefree θ →
  β.Coprime θ → β.Coprime 6 → θ.Coprime 6 → β % 24 = 17 → θ % 24 = 1 →
  (∀ p : ℕ, p.Prime → p ∣ θ → localSquareAt p β) →
  (∀ p : ℕ, p.Prime → p ∣ β → localSquareAt p θ) →
  ∃ n : ℕ, 0 < n ∧ squarefree n ∧ n.Coprime (6*θ) ∧ twistPointInClass β n ∧ twistPointInClass β (n*θ)

end ManuscriptV15.Arithmetic

namespace Sun28.PreparedPoles

private theorem squarefree_source (n : ℕ) : ManuscriptV15.Arithmetic.squarefree n ↔ Squarefree n := by
  simp only [ManuscriptV15.Arithmetic.squarefree, Nat.squarefree_iff_prime_squarefree, sq]

theorem twists_iff_manuscript : SimultaneousTwists ↔ ManuscriptV15.Arithmetic.SimultaneousTwists := by
  simp only [SimultaneousTwists, ManuscriptV15.Arithmetic.SimultaneousTwists, squarefree_source]
  rfl

theorem projection_of_manuscript_twists (units : FiveMarkUnits.PublishedCorollary72)
    (remaining : MinimalConductors.ExactLeastHeight) (preparation : IntegerPreparation)
    (twists : ManuscriptV15.Arithmetic.SimultaneousTwists) (x : ℚ) :
    (∃ w : Fin 28 → ℚ, Sun28.eval28 Concrete.fixedPolynomial x w=0) ↔ ∃ k : ℤ, x=(k:ℚ) :=
  fixed_projection units remaining preparation (twists_iff_manuscript.mpr twists) x

end Sun28.PreparedPoles
#print axioms Sun28.PreparedPoles.twists_iff_manuscript
#print axioms Sun28.PreparedPoles.projection_of_manuscript_twists
