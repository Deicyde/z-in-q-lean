import LiteralV15
import Mathlib.Tactic.Positivity

namespace ManuscriptV15.Quadrics
open MvPolynomial

structure Quadratic (n : ℕ) where
  weightPred : ℕ
  terms : List (Row n)

def parseQuadratic (n : ℕ) (s : String) : Option (Quadratic n) := do
  let [w,terms] := s.splitOn "|" | none
  let weight ← w.toNat?
  let parsed ← (terms.splitOn ";").mapM (parseRow n)
  match weight with
  | 0 => none
  | k+1 => some ⟨k,parsed⟩

def parseSystem (n : ℕ) (s : String) : Option (List (Quadratic n)) :=
  ((s.splitOn "\n").filter (· != "")).mapM (parseQuadratic n)

def fixedSystem := parseSystem 314 (include_str "data/quadrics314.txt")
def familySystem := parseSystem 222 (include_str "data/quadrics222.txt")

noncomputable def value {n : ℕ} (A : ℤ) (x : Fin n → ℚ) (r : Quadratic n) : ℚ :=
  eval₂ (Int.castRingHom ℚ) x (fromRows A r.terms)

noncomputable def sumAt {n : ℕ} (A : ℤ) (x : Fin n → ℚ) : List (Quadratic n) → ℚ
  | [] => 0
  | r::rs => ((r.weightPred:ℚ)+1) * (value A x r)^2 + sumAt A x rs

theorem sum_nonneg {n : ℕ} (A : ℤ) (x : Fin n → ℚ) (rs : List (Quadratic n)) : 0 ≤ sumAt A x rs := by
  induction rs with
  | nil => exact le_refl 0
  | cons r rs ih => exact add_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) ih

theorem sum_zero_iff {n : ℕ} (A : ℤ) (x : Fin n → ℚ) (rs : List (Quadratic n)) :
    sumAt A x rs = 0 ↔ ∀ r ∈ rs, value A x r = 0 := by
  induction rs with
  | nil => simp [sumAt]
  | cons r rs ih =>
    have hw : 0 < (r.weightPred:ℚ)+1 := by positivity
    rw [sumAt,add_eq_zero_iff_of_nonneg (mul_nonneg hw.le (sq_nonneg _)) (sum_nonneg A x rs),
      mul_eq_zero,ih]
    simp [ne_of_gt hw]

def Expansion {n : ℕ} (A : ℤ) (rs : List (Quadratic n)) (P : MvPolynomial (Fin n) ℤ) : Prop :=
  ∀ x : Fin n → ℚ, eval₂ (Int.castRingHom ℚ) x P = sumAt A x rs

def RowProjection {m : ℕ} (A : ℤ) (rs : List (Quadratic (m+1))) : Prop :=
  ∀ q : ℚ, (∃ w : Fin m → ℚ, ∀ r ∈ rs, value A (Fin.cons q w) r = 0) ↔ ∃ z : ℤ, (z : ℚ) = q

theorem projection_iff {m : ℕ} {A : ℤ} {rs : List (Quadratic (m+1))}
    {P : MvPolynomial (Fin (m+1)) ℤ} (expansion : Expansion A rs P) :
    DefinesIntegers P ↔ RowProjection A rs := by
  have test (q : ℚ) (w : Fin m → ℚ) :
      eval₂ (Int.castRingHom ℚ) (Fin.cons q w) P = 0 ↔
        ∀ r ∈ rs, value A (Fin.cons q w) r = 0 := by
    rw [expansion (Fin.cons q w), sum_zero_iff]
  exact forall_congr' fun q => iff_congr (exists_congr fun w => test q w) Iff.rfl

def FixedExpansion : Prop :=
  ∃ rs P, fixedSystem = some rs ∧ fixedTable = some P ∧ Expansion 1 rs P

def FamilyExpansion : Prop :=
  ∃ rs, familySystem = some rs ∧ ∀ N : ℕ,
    ∃ P, familyTable N = some P ∧ Expansion (A N) rs P

def FixedRowProjection : Prop := ∃ rs, fixedSystem = some rs ∧ RowProjection 1 rs

def FamilyRowProjection : Prop := ∃ rs, familySystem = some rs ∧
  ∃ N₀ : ℕ, ∀ N ≥ N₀, RowProjection (A N) rs

theorem fixed_projection (table : FixedExpansion) (points : FixedRowProjection) :
    ∃ P, fixedTable = some P ∧ DefinesIntegers P := by
  obtain ⟨rs,P,hs,hp,he⟩ := table
  obtain ⟨rs',hs',hr⟩ := points
  obtain rfl := Option.some.inj (hs'.symm.trans hs)
  exact ⟨P,hp,(projection_iff he).mpr hr⟩

theorem family_projection (table : FamilyExpansion) (points : FamilyRowProjection) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∃ P, familyTable N = some P ∧ DefinesIntegers P := by
  obtain ⟨rs,hs,hp⟩ := table
  obtain ⟨rs',hs',N₀,hr⟩ := points
  obtain rfl := Option.some.inj (hs'.symm.trans hs)
  refine ⟨N₀,fun N hN => ?_⟩
  obtain ⟨P,hP,he⟩ := hp N
  exact ⟨P,hP,(projection_iff he).mpr (hr N hN)⟩

#eval fixedSystem.map List.length
#eval familySystem.map List.length
#print axioms sum_zero_iff
#print axioms projection_iff
#print axioms fixed_projection
#print axioms family_projection
end ManuscriptV15.Quadrics
