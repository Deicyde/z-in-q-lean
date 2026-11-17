import CongruentCover
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers

namespace ZInQBlueprint.Descent
open ZInQBlueprint

def LocalCover (K : Type*) [Field K] (d a b : K) : Prop :=
  (IsSquare a ∧ IsSquare b) ∨
    ∃ x : K, IsSquare (x/a) ∧ IsSquare ((x-d)/b) ∧ IsSquare ((x+d)/(a*b))

/-- Signed squarefree representatives, soluble at every completion of Q. -/
def selmerPairs (d : ℕ) : Set (ℤ × ℤ) :=
  {ab | Squarefree ab.1 ∧ Squarefree ab.2 ∧ LocalCover ℝ d ab.1 ab.2 ∧
    ∀ (p : ℕ) [Fact p.Prime], LocalCover ℚ_[p] d ab.1 ab.2}

private theorem map_square {K : Type*} [Field K] [CharZero K] {x : ℚ} (h : IsSquare x) :
    IsSquare ((Rat.castHom K) x) := by
  obtain ⟨z,hz⟩ := h
  exact ⟨(Rat.castHom K) z, by rw [hz,map_mul]⟩

theorem cover_at_completion {K : Type*} [Field K] [CharZero K] {d a b : ℚ}
    (h : Cover d a b) :
    LocalCover K ((Rat.castHom K) d) ((Rat.castHom K) a) ((Rat.castHom K) b) := by
  rcases h with ⟨ha,hb⟩ | ⟨x,h₀,h₁,h₂⟩
  · exact Or.inl ⟨map_square ha,map_square hb⟩
  · right
    refine ⟨(Rat.castHom K) x, ?_, ?_, ?_⟩
    · simpa only [map_div₀] using map_square (K := K) h₀
    · simpa only [map_div₀,map_sub] using map_square (K := K) h₁
    · simpa only [map_div₀,map_add,map_mul] using map_square (K := K) h₂

theorem mem_of_rational {d : ℕ} {a b : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (pt : Cover d a b) : (a,b) ∈ selmerPairs d := by
  refine ⟨ha,hb,?_,?_⟩
  · simpa using cover_at_completion (K := ℝ) pt
  · intro p hp
    simpa using cover_at_completion (K := ℚ_[p]) pt

/-- Local membership follows from the same rational points and adds no certificate data. -/
structure EightCovers (d : ℕ) where
  pair : Fin 8 → ℤ × ℤ
  distinct : Function.Injective pair
  first : ∀ i, Squarefree (pair i).1
  second : ∀ i, Squarefree (pair i).2
  point : ∀ i, Cover d (pair i).1 (pair i).2

theorem all_rational {d : ℕ} (count : (selmerPairs d).ncard = 8) (cert : EightCovers d) :
    ∀ ab ∈ selmerPairs d, Cover d ab.1 ab.2 := by
  exact all_classes_of_eight count (fun ab => Cover d ab.1 ab.2) cert.pair cert.distinct
    (fun i => mem_of_rational (cert.first i) (cert.second i) (cert.point i)) cert.point

def EightCoverSelection : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (selmerPairs d).ncard = 8 →
    (∃ ab ∈ selmerPairs d, ab.1.natAbs % 8 = 7) → Nonempty (EightCovers d)

def CertifiedRankSel : Prop :=
  ∀ d : ℕ, d % 8 = 5 → Squarefree d → (selmerPairs d).ncard = 8 →
    (∃ ab ∈ selmerPairs d, ab.1.natAbs % 8 = 7) → ∀ ab ∈ selmerPairs d, LocalCover ℚ d ab.1 ab.2

theorem certifiedRank_of_eight (supply : EightCoverSelection) : CertifiedRankSel := by
  intro d residue free count witness
  obtain ⟨cert⟩ := supply d residue free count witness
  exact all_rational count cert

#print axioms cover_at_completion
#print axioms mem_of_rational
#print axioms all_rational
#print axioms certifiedRank_of_eight
end ZInQBlueprint.Descent
